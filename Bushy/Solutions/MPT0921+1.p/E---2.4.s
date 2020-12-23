%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : mcart_1__t81_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:14 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   40 (  81 expanded)
%              Number of clauses        :   23 (  30 expanded)
%              Number of leaves         :    8 (  20 expanded)
%              Depth                    :   10
%              Number of atoms          :  121 ( 492 expanded)
%              Number of equality atoms :   58 ( 275 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t81_mcart_1.p',d4_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t81_mcart_1.p',d3_mcart_1)).

fof(t81_mcart_1,conjecture,(
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
                         => X5 = X9 ) ) ) ) )
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X3 = k1_xboole_0
          | X4 = k1_xboole_0
          | X5 = k10_mcart_1(X1,X2,X3,X4,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t81_mcart_1.p',t81_mcart_1)).

fof(t60_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0
        & ~ ! [X5] :
              ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
             => X5 = k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5),k10_mcart_1(X1,X2,X3,X4,X5),k11_mcart_1(X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t81_mcart_1.p',t60_mcart_1)).

fof(dt_k9_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k9_mcart_1(X1,X2,X3,X4,X5),X2) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t81_mcart_1.p',dt_k9_mcart_1)).

fof(dt_k8_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k8_mcart_1(X1,X2,X3,X4,X5),X1) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t81_mcart_1.p',dt_k8_mcart_1)).

fof(dt_k11_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k11_mcart_1(X1,X2,X3,X4,X5),X4) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t81_mcart_1.p',dt_k11_mcart_1)).

fof(dt_k10_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k10_mcart_1(X1,X2,X3,X4,X5),X3) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t81_mcart_1.p',dt_k10_mcart_1)).

fof(c_0_8,plain,(
    ! [X26,X27,X28,X29] : k4_mcart_1(X26,X27,X28,X29) = k4_tarski(k3_mcart_1(X26,X27,X28),X29) ),
    inference(variable_rename,[status(thm)],[d4_mcart_1])).

fof(c_0_9,plain,(
    ! [X23,X24,X25] : k3_mcart_1(X23,X24,X25) = k4_tarski(k4_tarski(X23,X24),X25) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_10,negated_conjecture,(
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
                           => X5 = X9 ) ) ) ) )
         => ( X1 = k1_xboole_0
            | X2 = k1_xboole_0
            | X3 = k1_xboole_0
            | X4 = k1_xboole_0
            | X5 = k10_mcart_1(X1,X2,X3,X4,X6) ) ) ) ),
    inference(assume_negation,[status(cth)],[t81_mcart_1])).

fof(c_0_11,plain,(
    ! [X56,X57,X58,X59,X60] :
      ( X56 = k1_xboole_0
      | X57 = k1_xboole_0
      | X58 = k1_xboole_0
      | X59 = k1_xboole_0
      | ~ m1_subset_1(X60,k4_zfmisc_1(X56,X57,X58,X59))
      | X60 = k4_mcart_1(k8_mcart_1(X56,X57,X58,X59,X60),k9_mcart_1(X56,X57,X58,X59,X60),k10_mcart_1(X56,X57,X58,X59,X60),k11_mcart_1(X56,X57,X58,X59,X60)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_mcart_1])])])).

cnf(c_0_12,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,negated_conjecture,(
    ! [X17,X18,X19,X20] :
      ( m1_subset_1(esk6_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0))
      & ( ~ m1_subset_1(X17,esk1_0)
        | ~ m1_subset_1(X18,esk2_0)
        | ~ m1_subset_1(X19,esk3_0)
        | ~ m1_subset_1(X20,esk4_0)
        | esk6_0 != k4_mcart_1(X17,X18,X19,X20)
        | esk5_0 = X19 )
      & esk1_0 != k1_xboole_0
      & esk2_0 != k1_xboole_0
      & esk3_0 != k1_xboole_0
      & esk4_0 != k1_xboole_0
      & esk5_0 != k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).

cnf(c_0_15,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5),k10_mcart_1(X1,X2,X3,X4,X5),k11_mcart_1(X1,X2,X3,X4,X5))
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( esk5_0 = X3
    | ~ m1_subset_1(X1,esk1_0)
    | ~ m1_subset_1(X2,esk2_0)
    | ~ m1_subset_1(X3,esk3_0)
    | ~ m1_subset_1(X4,esk4_0)
    | esk6_0 != k4_mcart_1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X5 = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5)),k10_mcart_1(X1,X2,X3,X4,X5)),k11_mcart_1(X1,X2,X3,X4,X5))
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk6_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( esk5_0 = X3
    | esk6_0 != k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)
    | ~ m1_subset_1(X4,esk4_0)
    | ~ m1_subset_1(X3,esk3_0)
    | ~ m1_subset_1(X2,esk2_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(rw,[status(thm)],[c_0_17,c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)),k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)),k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)) = esk6_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( esk5_0 != k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_27,plain,(
    ! [X45,X46,X47,X48,X49] :
      ( ~ m1_subset_1(X49,k4_zfmisc_1(X45,X46,X47,X48))
      | m1_subset_1(k9_mcart_1(X45,X46,X47,X48,X49),X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_mcart_1])])).

cnf(c_0_28,negated_conjecture,
    ( ~ m1_subset_1(k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),esk4_0)
    | ~ m1_subset_1(k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),esk3_0)
    | ~ m1_subset_1(k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),esk2_0)
    | ~ m1_subset_1(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

cnf(c_0_29,plain,
    ( m1_subset_1(k9_mcart_1(X2,X3,X4,X5,X1),X3)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_30,plain,(
    ! [X40,X41,X42,X43,X44] :
      ( ~ m1_subset_1(X44,k4_zfmisc_1(X40,X41,X42,X43))
      | m1_subset_1(k8_mcart_1(X40,X41,X42,X43,X44),X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_mcart_1])])).

cnf(c_0_31,negated_conjecture,
    ( ~ m1_subset_1(k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),esk4_0)
    | ~ m1_subset_1(k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),esk3_0)
    | ~ m1_subset_1(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_19])])).

cnf(c_0_32,plain,
    ( m1_subset_1(k8_mcart_1(X2,X3,X4,X5,X1),X2)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_33,plain,(
    ! [X35,X36,X37,X38,X39] :
      ( ~ m1_subset_1(X39,k4_zfmisc_1(X35,X36,X37,X38))
      | m1_subset_1(k11_mcart_1(X35,X36,X37,X38,X39),X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_mcart_1])])).

cnf(c_0_34,negated_conjecture,
    ( ~ m1_subset_1(k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),esk4_0)
    | ~ m1_subset_1(k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_19])])).

cnf(c_0_35,plain,
    ( m1_subset_1(k11_mcart_1(X2,X3,X4,X5,X1),X5)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_36,plain,(
    ! [X30,X31,X32,X33,X34] :
      ( ~ m1_subset_1(X34,k4_zfmisc_1(X30,X31,X32,X33))
      | m1_subset_1(k10_mcart_1(X30,X31,X32,X33,X34),X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k10_mcart_1])])).

cnf(c_0_37,negated_conjecture,
    ( ~ m1_subset_1(k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_19])])).

cnf(c_0_38,plain,
    ( m1_subset_1(k10_mcart_1(X2,X3,X4,X5,X1),X4)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_19])]),
    [proof]).
%------------------------------------------------------------------------------
