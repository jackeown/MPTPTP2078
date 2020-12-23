%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:27 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 267 expanded)
%              Number of clauses        :   38 ( 114 expanded)
%              Number of leaves         :   11 (  66 expanded)
%              Depth                    :   12
%              Number of atoms          :  150 (1058 expanded)
%              Number of equality atoms :   77 ( 665 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(d4_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t80_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))
     => ( ! [X7] :
            ( m1_subset_1(X7,X1)
           => ! [X8] :
                ( m1_subset_1(X8,X2)
               => ! [X9] :
                    ( m1_subset_1(X9,X3)
                   => ! [X10] :
                        ( m1_subset_1(X10,X4)
                       => ( X6 = k4_mcart_1(X7,X8,X9,X10)
                         => X5 = X8 ) ) ) ) )
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X3 = k1_xboole_0
          | X4 = k1_xboole_0
          | X5 = k9_mcart_1(X1,X2,X3,X4,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_mcart_1)).

fof(t60_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0
        & ~ ! [X5] :
              ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
             => X5 = k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5),k10_mcart_1(X1,X2,X3,X4,X5),k11_mcart_1(X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_mcart_1)).

fof(dt_k11_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k11_mcart_1(X1,X2,X3,X4,X5),X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_mcart_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(dt_k10_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k10_mcart_1(X1,X2,X3,X4,X5),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_mcart_1)).

fof(dt_k9_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k9_mcart_1(X1,X2,X3,X4,X5),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_mcart_1)).

fof(dt_k8_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k8_mcart_1(X1,X2,X3,X4,X5),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_mcart_1)).

fof(c_0_11,plain,(
    ! [X26,X27,X28,X29] : k4_mcart_1(X26,X27,X28,X29) = k4_tarski(k3_mcart_1(X26,X27,X28),X29) ),
    inference(variable_rename,[status(thm)],[d4_mcart_1])).

fof(c_0_12,plain,(
    ! [X20,X21,X22] : k3_mcart_1(X20,X21,X22) = k4_tarski(k4_tarski(X20,X21),X22) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_13,plain,(
    ! [X30,X31,X32,X33] : k4_zfmisc_1(X30,X31,X32,X33) = k2_zfmisc_1(k3_zfmisc_1(X30,X31,X32),X33) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

fof(c_0_14,plain,(
    ! [X23,X24,X25] : k3_zfmisc_1(X23,X24,X25) = k2_zfmisc_1(k2_zfmisc_1(X23,X24),X25) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))
       => ( ! [X7] :
              ( m1_subset_1(X7,X1)
             => ! [X8] :
                  ( m1_subset_1(X8,X2)
                 => ! [X9] :
                      ( m1_subset_1(X9,X3)
                     => ! [X10] :
                          ( m1_subset_1(X10,X4)
                         => ( X6 = k4_mcart_1(X7,X8,X9,X10)
                           => X5 = X8 ) ) ) ) )
         => ( X1 = k1_xboole_0
            | X2 = k1_xboole_0
            | X3 = k1_xboole_0
            | X4 = k1_xboole_0
            | X5 = k9_mcart_1(X1,X2,X3,X4,X6) ) ) ) ),
    inference(assume_negation,[status(cth)],[t80_mcart_1])).

fof(c_0_16,plain,(
    ! [X57,X58,X59,X60,X61] :
      ( X57 = k1_xboole_0
      | X58 = k1_xboole_0
      | X59 = k1_xboole_0
      | X60 = k1_xboole_0
      | ~ m1_subset_1(X61,k4_zfmisc_1(X57,X58,X59,X60))
      | X61 = k4_mcart_1(k8_mcart_1(X57,X58,X59,X60,X61),k9_mcart_1(X57,X58,X59,X60,X61),k10_mcart_1(X57,X58,X59,X60,X61),k11_mcart_1(X57,X58,X59,X60,X61)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_mcart_1])])])).

cnf(c_0_17,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,negated_conjecture,(
    ! [X70,X71,X72,X73] :
      ( m1_subset_1(esk8_0,k4_zfmisc_1(esk3_0,esk4_0,esk5_0,esk6_0))
      & ( ~ m1_subset_1(X70,esk3_0)
        | ~ m1_subset_1(X71,esk4_0)
        | ~ m1_subset_1(X72,esk5_0)
        | ~ m1_subset_1(X73,esk6_0)
        | esk8_0 != k4_mcart_1(X70,X71,X72,X73)
        | esk7_0 = X71 )
      & esk3_0 != k1_xboole_0
      & esk4_0 != k1_xboole_0
      & esk5_0 != k1_xboole_0
      & esk6_0 != k1_xboole_0
      & esk7_0 != k9_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0,esk8_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])).

fof(c_0_22,plain,(
    ! [X39,X40,X41,X42,X43] :
      ( ~ m1_subset_1(X43,k4_zfmisc_1(X39,X40,X41,X42))
      | m1_subset_1(k11_mcart_1(X39,X40,X41,X42,X43),X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_mcart_1])])).

cnf(c_0_23,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5),k10_mcart_1(X1,X2,X3,X4,X5),k11_mcart_1(X1,X2,X3,X4,X5))
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk8_0,k4_zfmisc_1(esk3_0,esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( m1_subset_1(k11_mcart_1(X2,X3,X4,X5,X1),X5)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_28,plain,(
    ! [X62,X63] :
      ( k1_mcart_1(k4_tarski(X62,X63)) = X62
      & k2_mcart_1(k4_tarski(X62,X63)) = X63 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_29,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X5 = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5)),k10_mcart_1(X1,X2,X3,X4,X5)),k11_mcart_1(X1,X2,X3,X4,X5))
    | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk8_0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[c_0_26,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,plain,
    ( m1_subset_1(k11_mcart_1(X2,X3,X4,X5,X1),X5)
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X5)) ),
    inference(rw,[status(thm)],[c_0_27,c_0_25])).

cnf(c_0_36,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0,esk8_0),k9_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0,esk8_0)),k10_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0,esk8_0)),k11_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0,esk8_0)) = esk8_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34])).

fof(c_0_38,plain,(
    ! [X34,X35,X36,X37,X38] :
      ( ~ m1_subset_1(X38,k4_zfmisc_1(X34,X35,X36,X37))
      | m1_subset_1(k10_mcart_1(X34,X35,X36,X37,X38),X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k10_mcart_1])])).

cnf(c_0_39,negated_conjecture,
    ( esk7_0 = X2
    | ~ m1_subset_1(X1,esk3_0)
    | ~ m1_subset_1(X2,esk4_0)
    | ~ m1_subset_1(X3,esk5_0)
    | ~ m1_subset_1(X4,esk6_0)
    | esk8_0 != k4_mcart_1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(k11_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0,esk8_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( k11_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0,esk8_0) = k2_mcart_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,plain,
    ( m1_subset_1(k10_mcart_1(X2,X3,X4,X5,X1),X4)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_43,plain,(
    ! [X49,X50,X51,X52,X53] :
      ( ~ m1_subset_1(X53,k4_zfmisc_1(X49,X50,X51,X52))
      | m1_subset_1(k9_mcart_1(X49,X50,X51,X52,X53),X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_mcart_1])])).

cnf(c_0_44,negated_conjecture,
    ( esk7_0 = X2
    | esk8_0 != k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)
    | ~ m1_subset_1(X4,esk6_0)
    | ~ m1_subset_1(X3,esk5_0)
    | ~ m1_subset_1(X2,esk4_0)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(rw,[status(thm)],[c_0_39,c_0_24])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(k2_mcart_1(esk8_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,plain,
    ( m1_subset_1(k10_mcart_1(X2,X3,X4,X5,X1),X4)
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X5)) ),
    inference(rw,[status(thm)],[c_0_42,c_0_25])).

cnf(c_0_47,plain,
    ( m1_subset_1(k9_mcart_1(X2,X3,X4,X5,X1),X3)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_48,plain,(
    ! [X44,X45,X46,X47,X48] :
      ( ~ m1_subset_1(X48,k4_zfmisc_1(X44,X45,X46,X47))
      | m1_subset_1(k8_mcart_1(X44,X45,X46,X47,X48),X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_mcart_1])])).

cnf(c_0_49,negated_conjecture,
    ( esk7_0 = X1
    | k4_tarski(k4_tarski(k4_tarski(X2,X1),X3),k2_mcart_1(esk8_0)) != esk8_0
    | ~ m1_subset_1(X3,esk5_0)
    | ~ m1_subset_1(X1,esk4_0)
    | ~ m1_subset_1(X2,esk3_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(k10_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0,esk8_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_30])).

cnf(c_0_51,plain,
    ( m1_subset_1(k9_mcart_1(X2,X3,X4,X5,X1),X3)
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X5)) ),
    inference(rw,[status(thm)],[c_0_47,c_0_25])).

cnf(c_0_52,plain,
    ( m1_subset_1(k8_mcart_1(X2,X3,X4,X5,X1),X2)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( esk7_0 = X1
    | k4_tarski(k4_tarski(k4_tarski(X2,X1),k10_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0,esk8_0)),k2_mcart_1(esk8_0)) != esk8_0
    | ~ m1_subset_1(X1,esk4_0)
    | ~ m1_subset_1(X2,esk3_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(k9_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0,esk8_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_30])).

cnf(c_0_55,negated_conjecture,
    ( esk7_0 != k9_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_56,plain,
    ( m1_subset_1(k8_mcart_1(X2,X3,X4,X5,X1),X2)
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X5)) ),
    inference(rw,[status(thm)],[c_0_52,c_0_25])).

cnf(c_0_57,negated_conjecture,
    ( k4_tarski(k4_tarski(k4_tarski(X1,k9_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0,esk8_0)),k10_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0,esk8_0)),k2_mcart_1(esk8_0)) != esk8_0
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(k8_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0,esk8_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_30])).

cnf(c_0_59,negated_conjecture,
    ( k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0,esk8_0),k9_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0,esk8_0)),k10_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0,esk8_0)),k2_mcart_1(esk8_0)) != esk8_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_41]),c_0_59]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:18:39 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.13/0.38  # and selection function GSelectMinInfpos.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(d4_mcart_1, axiom, ![X1, X2, X3, X4]:k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_mcart_1)).
% 0.13/0.38  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.13/0.38  fof(d4_zfmisc_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 0.13/0.38  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.13/0.38  fof(t80_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6]:(m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))=>(![X7]:(m1_subset_1(X7,X1)=>![X8]:(m1_subset_1(X8,X2)=>![X9]:(m1_subset_1(X9,X3)=>![X10]:(m1_subset_1(X10,X4)=>(X6=k4_mcart_1(X7,X8,X9,X10)=>X5=X8)))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k9_mcart_1(X1,X2,X3,X4,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_mcart_1)).
% 0.13/0.38  fof(t60_mcart_1, axiom, ![X1, X2, X3, X4]:~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&~(![X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>X5=k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5),k10_mcart_1(X1,X2,X3,X4,X5),k11_mcart_1(X1,X2,X3,X4,X5)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_mcart_1)).
% 0.13/0.38  fof(dt_k11_mcart_1, axiom, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>m1_subset_1(k11_mcart_1(X1,X2,X3,X4,X5),X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k11_mcart_1)).
% 0.13/0.38  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.13/0.38  fof(dt_k10_mcart_1, axiom, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>m1_subset_1(k10_mcart_1(X1,X2,X3,X4,X5),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_mcart_1)).
% 0.13/0.38  fof(dt_k9_mcart_1, axiom, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>m1_subset_1(k9_mcart_1(X1,X2,X3,X4,X5),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_mcart_1)).
% 0.13/0.38  fof(dt_k8_mcart_1, axiom, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>m1_subset_1(k8_mcart_1(X1,X2,X3,X4,X5),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_mcart_1)).
% 0.13/0.38  fof(c_0_11, plain, ![X26, X27, X28, X29]:k4_mcart_1(X26,X27,X28,X29)=k4_tarski(k3_mcart_1(X26,X27,X28),X29), inference(variable_rename,[status(thm)],[d4_mcart_1])).
% 0.13/0.38  fof(c_0_12, plain, ![X20, X21, X22]:k3_mcart_1(X20,X21,X22)=k4_tarski(k4_tarski(X20,X21),X22), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.13/0.38  fof(c_0_13, plain, ![X30, X31, X32, X33]:k4_zfmisc_1(X30,X31,X32,X33)=k2_zfmisc_1(k3_zfmisc_1(X30,X31,X32),X33), inference(variable_rename,[status(thm)],[d4_zfmisc_1])).
% 0.13/0.38  fof(c_0_14, plain, ![X23, X24, X25]:k3_zfmisc_1(X23,X24,X25)=k2_zfmisc_1(k2_zfmisc_1(X23,X24),X25), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.13/0.38  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:(m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))=>(![X7]:(m1_subset_1(X7,X1)=>![X8]:(m1_subset_1(X8,X2)=>![X9]:(m1_subset_1(X9,X3)=>![X10]:(m1_subset_1(X10,X4)=>(X6=k4_mcart_1(X7,X8,X9,X10)=>X5=X8)))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k9_mcart_1(X1,X2,X3,X4,X6))))), inference(assume_negation,[status(cth)],[t80_mcart_1])).
% 0.13/0.38  fof(c_0_16, plain, ![X57, X58, X59, X60, X61]:(X57=k1_xboole_0|X58=k1_xboole_0|X59=k1_xboole_0|X60=k1_xboole_0|(~m1_subset_1(X61,k4_zfmisc_1(X57,X58,X59,X60))|X61=k4_mcart_1(k8_mcart_1(X57,X58,X59,X60,X61),k9_mcart_1(X57,X58,X59,X60,X61),k10_mcart_1(X57,X58,X59,X60,X61),k11_mcart_1(X57,X58,X59,X60,X61)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_mcart_1])])])).
% 0.13/0.38  cnf(c_0_17, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_18, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_19, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_20, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  fof(c_0_21, negated_conjecture, ![X70, X71, X72, X73]:(m1_subset_1(esk8_0,k4_zfmisc_1(esk3_0,esk4_0,esk5_0,esk6_0))&((~m1_subset_1(X70,esk3_0)|(~m1_subset_1(X71,esk4_0)|(~m1_subset_1(X72,esk5_0)|(~m1_subset_1(X73,esk6_0)|(esk8_0!=k4_mcart_1(X70,X71,X72,X73)|esk7_0=X71)))))&((((esk3_0!=k1_xboole_0&esk4_0!=k1_xboole_0)&esk5_0!=k1_xboole_0)&esk6_0!=k1_xboole_0)&esk7_0!=k9_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0,esk8_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])).
% 0.13/0.38  fof(c_0_22, plain, ![X39, X40, X41, X42, X43]:(~m1_subset_1(X43,k4_zfmisc_1(X39,X40,X41,X42))|m1_subset_1(k11_mcart_1(X39,X40,X41,X42,X43),X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_mcart_1])])).
% 0.13/0.38  cnf(c_0_23, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5),k10_mcart_1(X1,X2,X3,X4,X5),k11_mcart_1(X1,X2,X3,X4,X5))|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_24, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.38  cnf(c_0_25, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk8_0,k4_zfmisc_1(esk3_0,esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_27, plain, (m1_subset_1(k11_mcart_1(X2,X3,X4,X5,X1),X5)|~m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  fof(c_0_28, plain, ![X62, X63]:(k1_mcart_1(k4_tarski(X62,X63))=X62&k2_mcart_1(k4_tarski(X62,X63))=X63), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.13/0.38  cnf(c_0_29, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X5=k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5)),k10_mcart_1(X1,X2,X3,X4,X5)),k11_mcart_1(X1,X2,X3,X4,X5))|~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk8_0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk5_0),esk6_0))), inference(rw,[status(thm)],[c_0_26, c_0_25])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_35, plain, (m1_subset_1(k11_mcart_1(X2,X3,X4,X5,X1),X5)|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X5))), inference(rw,[status(thm)],[c_0_27, c_0_25])).
% 0.13/0.38  cnf(c_0_36, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0,esk8_0),k9_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0,esk8_0)),k10_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0,esk8_0)),k11_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0,esk8_0))=esk8_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34])).
% 0.13/0.38  fof(c_0_38, plain, ![X34, X35, X36, X37, X38]:(~m1_subset_1(X38,k4_zfmisc_1(X34,X35,X36,X37))|m1_subset_1(k10_mcart_1(X34,X35,X36,X37,X38),X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k10_mcart_1])])).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (esk7_0=X2|~m1_subset_1(X1,esk3_0)|~m1_subset_1(X2,esk4_0)|~m1_subset_1(X3,esk5_0)|~m1_subset_1(X4,esk6_0)|esk8_0!=k4_mcart_1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (m1_subset_1(k11_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0,esk8_0),esk6_0)), inference(spm,[status(thm)],[c_0_35, c_0_30])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (k11_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0,esk8_0)=k2_mcart_1(esk8_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.13/0.38  cnf(c_0_42, plain, (m1_subset_1(k10_mcart_1(X2,X3,X4,X5,X1),X4)|~m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.38  fof(c_0_43, plain, ![X49, X50, X51, X52, X53]:(~m1_subset_1(X53,k4_zfmisc_1(X49,X50,X51,X52))|m1_subset_1(k9_mcart_1(X49,X50,X51,X52,X53),X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_mcart_1])])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (esk7_0=X2|esk8_0!=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)|~m1_subset_1(X4,esk6_0)|~m1_subset_1(X3,esk5_0)|~m1_subset_1(X2,esk4_0)|~m1_subset_1(X1,esk3_0)), inference(rw,[status(thm)],[c_0_39, c_0_24])).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (m1_subset_1(k2_mcart_1(esk8_0),esk6_0)), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.13/0.38  cnf(c_0_46, plain, (m1_subset_1(k10_mcart_1(X2,X3,X4,X5,X1),X4)|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X5))), inference(rw,[status(thm)],[c_0_42, c_0_25])).
% 0.13/0.38  cnf(c_0_47, plain, (m1_subset_1(k9_mcart_1(X2,X3,X4,X5,X1),X3)|~m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.38  fof(c_0_48, plain, ![X44, X45, X46, X47, X48]:(~m1_subset_1(X48,k4_zfmisc_1(X44,X45,X46,X47))|m1_subset_1(k8_mcart_1(X44,X45,X46,X47,X48),X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_mcart_1])])).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (esk7_0=X1|k4_tarski(k4_tarski(k4_tarski(X2,X1),X3),k2_mcart_1(esk8_0))!=esk8_0|~m1_subset_1(X3,esk5_0)|~m1_subset_1(X1,esk4_0)|~m1_subset_1(X2,esk3_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (m1_subset_1(k10_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0,esk8_0),esk5_0)), inference(spm,[status(thm)],[c_0_46, c_0_30])).
% 0.13/0.38  cnf(c_0_51, plain, (m1_subset_1(k9_mcart_1(X2,X3,X4,X5,X1),X3)|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X5))), inference(rw,[status(thm)],[c_0_47, c_0_25])).
% 0.13/0.38  cnf(c_0_52, plain, (m1_subset_1(k8_mcart_1(X2,X3,X4,X5,X1),X2)|~m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (esk7_0=X1|k4_tarski(k4_tarski(k4_tarski(X2,X1),k10_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0,esk8_0)),k2_mcart_1(esk8_0))!=esk8_0|~m1_subset_1(X1,esk4_0)|~m1_subset_1(X2,esk3_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, (m1_subset_1(k9_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0,esk8_0),esk4_0)), inference(spm,[status(thm)],[c_0_51, c_0_30])).
% 0.13/0.38  cnf(c_0_55, negated_conjecture, (esk7_0!=k9_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_56, plain, (m1_subset_1(k8_mcart_1(X2,X3,X4,X5,X1),X2)|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X5))), inference(rw,[status(thm)],[c_0_52, c_0_25])).
% 0.13/0.38  cnf(c_0_57, negated_conjecture, (k4_tarski(k4_tarski(k4_tarski(X1,k9_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0,esk8_0)),k10_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0,esk8_0)),k2_mcart_1(esk8_0))!=esk8_0|~m1_subset_1(X1,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])).
% 0.13/0.38  cnf(c_0_58, negated_conjecture, (m1_subset_1(k8_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0,esk8_0),esk3_0)), inference(spm,[status(thm)],[c_0_56, c_0_30])).
% 0.13/0.38  cnf(c_0_59, negated_conjecture, (k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0,esk8_0),k9_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0,esk8_0)),k10_mcart_1(esk3_0,esk4_0,esk5_0,esk6_0,esk8_0)),k2_mcart_1(esk8_0))!=esk8_0), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.13/0.38  cnf(c_0_60, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_41]), c_0_59]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 61
% 0.13/0.38  # Proof object clause steps            : 38
% 0.13/0.38  # Proof object formula steps           : 23
% 0.13/0.38  # Proof object conjectures             : 24
% 0.13/0.38  # Proof object clause conjectures      : 21
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 17
% 0.13/0.38  # Proof object initial formulas used   : 11
% 0.13/0.38  # Proof object generating inferences   : 10
% 0.13/0.38  # Proof object simplifying inferences  : 18
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 13
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 23
% 0.13/0.38  # Removed in clause preprocessing      : 4
% 0.13/0.38  # Initial clauses in saturation        : 19
% 0.13/0.38  # Processed clauses                    : 59
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 0
% 0.13/0.38  # ...remaining for further processing  : 58
% 0.13/0.38  # Other redundant clauses eliminated   : 6
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 3
% 0.13/0.38  # Generated clauses                    : 33
% 0.13/0.38  # ...of the previous two non-trivial   : 35
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 27
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 7
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 31
% 0.13/0.38  #    Positive orientable unit clauses  : 8
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 9
% 0.13/0.38  #    Non-unit-clauses                  : 14
% 0.13/0.38  # Current number of unprocessed clauses: 8
% 0.13/0.38  # ...number of literals in the above   : 22
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 26
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 84
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 41
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.38  # Unit Clause-clause subsumption calls : 13
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 1
% 0.13/0.38  # BW rewrite match successes           : 1
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 2256
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.032 s
% 0.13/0.38  # System time              : 0.002 s
% 0.13/0.38  # Total time               : 0.034 s
% 0.13/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
