%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:26 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 160 expanded)
%              Number of clauses        :   31 (  69 expanded)
%              Number of leaves         :   10 (  40 expanded)
%              Depth                    :    6
%              Number of atoms          :  131 ( 569 expanded)
%              Number of equality atoms :   65 ( 345 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(d4_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t79_mcart_1,conjecture,(
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
                         => X5 = X7 ) ) ) ) )
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X3 = k1_xboole_0
          | X4 = k1_xboole_0
          | X5 = k8_mcart_1(X1,X2,X3,X4,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_mcart_1)).

fof(t60_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0
        & ~ ! [X5] :
              ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
             => X5 = k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5),k10_mcart_1(X1,X2,X3,X4,X5),k11_mcart_1(X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_mcart_1)).

fof(dt_k11_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k11_mcart_1(X1,X2,X3,X4,X5),X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_mcart_1)).

fof(dt_k10_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k10_mcart_1(X1,X2,X3,X4,X5),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_mcart_1)).

fof(dt_k9_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k9_mcart_1(X1,X2,X3,X4,X5),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_mcart_1)).

fof(dt_k8_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k8_mcart_1(X1,X2,X3,X4,X5),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_mcart_1)).

fof(c_0_10,plain,(
    ! [X17,X18,X19,X20] : k4_mcart_1(X17,X18,X19,X20) = k4_tarski(k3_mcart_1(X17,X18,X19),X20) ),
    inference(variable_rename,[status(thm)],[d4_mcart_1])).

fof(c_0_11,plain,(
    ! [X11,X12,X13] : k3_mcart_1(X11,X12,X13) = k4_tarski(k4_tarski(X11,X12),X13) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_12,plain,(
    ! [X21,X22,X23,X24] : k4_zfmisc_1(X21,X22,X23,X24) = k2_zfmisc_1(k3_zfmisc_1(X21,X22,X23),X24) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

fof(c_0_13,plain,(
    ! [X14,X15,X16] : k3_zfmisc_1(X14,X15,X16) = k2_zfmisc_1(k2_zfmisc_1(X14,X15),X16) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_14,negated_conjecture,(
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
                           => X5 = X7 ) ) ) ) )
         => ( X1 = k1_xboole_0
            | X2 = k1_xboole_0
            | X3 = k1_xboole_0
            | X4 = k1_xboole_0
            | X5 = k8_mcart_1(X1,X2,X3,X4,X6) ) ) ) ),
    inference(assume_negation,[status(cth)],[t79_mcart_1])).

fof(c_0_15,plain,(
    ! [X45,X46,X47,X48,X49] :
      ( X45 = k1_xboole_0
      | X46 = k1_xboole_0
      | X47 = k1_xboole_0
      | X48 = k1_xboole_0
      | ~ m1_subset_1(X49,k4_zfmisc_1(X45,X46,X47,X48))
      | X49 = k4_mcart_1(k8_mcart_1(X45,X46,X47,X48,X49),k9_mcart_1(X45,X46,X47,X48,X49),k10_mcart_1(X45,X46,X47,X48,X49),k11_mcart_1(X45,X46,X47,X48,X49)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_mcart_1])])])).

cnf(c_0_16,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,negated_conjecture,(
    ! [X56,X57,X58,X59] :
      ( m1_subset_1(esk6_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0))
      & ( ~ m1_subset_1(X56,esk1_0)
        | ~ m1_subset_1(X57,esk2_0)
        | ~ m1_subset_1(X58,esk3_0)
        | ~ m1_subset_1(X59,esk4_0)
        | esk6_0 != k4_mcart_1(X56,X57,X58,X59)
        | esk5_0 = X56 )
      & esk1_0 != k1_xboole_0
      & esk2_0 != k1_xboole_0
      & esk3_0 != k1_xboole_0
      & esk4_0 != k1_xboole_0
      & esk5_0 != k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])])).

fof(c_0_21,plain,(
    ! [X30,X31,X32,X33,X34] :
      ( ~ m1_subset_1(X34,k4_zfmisc_1(X30,X31,X32,X33))
      | m1_subset_1(k11_mcart_1(X30,X31,X32,X33,X34),X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_mcart_1])])).

fof(c_0_22,plain,(
    ! [X25,X26,X27,X28,X29] :
      ( ~ m1_subset_1(X29,k4_zfmisc_1(X25,X26,X27,X28))
      | m1_subset_1(k10_mcart_1(X25,X26,X27,X28,X29),X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k10_mcart_1])])).

fof(c_0_23,plain,(
    ! [X40,X41,X42,X43,X44] :
      ( ~ m1_subset_1(X44,k4_zfmisc_1(X40,X41,X42,X43))
      | m1_subset_1(k9_mcart_1(X40,X41,X42,X43,X44),X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_mcart_1])])).

fof(c_0_24,plain,(
    ! [X35,X36,X37,X38,X39] :
      ( ~ m1_subset_1(X39,k4_zfmisc_1(X35,X36,X37,X38))
      | m1_subset_1(k8_mcart_1(X35,X36,X37,X38,X39),X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_mcart_1])])).

cnf(c_0_25,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5),k10_mcart_1(X1,X2,X3,X4,X5),k11_mcart_1(X1,X2,X3,X4,X5))
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_27,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk6_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( m1_subset_1(k11_mcart_1(X2,X3,X4,X5,X1),X5)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( m1_subset_1(k10_mcart_1(X2,X3,X4,X5,X1),X4)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( m1_subset_1(k9_mcart_1(X2,X3,X4,X5,X1),X3)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( m1_subset_1(k8_mcart_1(X2,X3,X4,X5,X1),X2)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( esk5_0 = X1
    | ~ m1_subset_1(X1,esk1_0)
    | ~ m1_subset_1(X2,esk2_0)
    | ~ m1_subset_1(X3,esk3_0)
    | ~ m1_subset_1(X4,esk4_0)
    | esk6_0 != k4_mcart_1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_34,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X5 = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5)),k10_mcart_1(X1,X2,X3,X4,X5)),k11_mcart_1(X1,X2,X3,X4,X5))
    | ~ m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk6_0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0)) ),
    inference(rw,[status(thm)],[c_0_28,c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_37,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_38,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_39,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_40,plain,
    ( m1_subset_1(k11_mcart_1(X2,X3,X4,X5,X1),X5)
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X5)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_27])).

cnf(c_0_41,plain,
    ( m1_subset_1(k10_mcart_1(X2,X3,X4,X5,X1),X4)
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X5)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_27])).

cnf(c_0_42,plain,
    ( m1_subset_1(k9_mcart_1(X2,X3,X4,X5,X1),X3)
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X5)) ),
    inference(rw,[status(thm)],[c_0_31,c_0_27])).

cnf(c_0_43,plain,
    ( m1_subset_1(k8_mcart_1(X2,X3,X4,X5,X1),X2)
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X5)) ),
    inference(rw,[status(thm)],[c_0_32,c_0_27])).

cnf(c_0_44,negated_conjecture,
    ( esk5_0 = X1
    | esk6_0 != k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)
    | ~ m1_subset_1(X4,esk4_0)
    | ~ m1_subset_1(X3,esk3_0)
    | ~ m1_subset_1(X2,esk2_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(rw,[status(thm)],[c_0_33,c_0_26])).

cnf(c_0_45,negated_conjecture,
    ( k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)),k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)),k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)) = esk6_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_35])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_35])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_35])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_35])).

cnf(c_0_50,negated_conjecture,
    ( esk5_0 != k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47]),c_0_48]),c_0_49])]),c_0_50]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:57:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.027 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(d4_mcart_1, axiom, ![X1, X2, X3, X4]:k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_mcart_1)).
% 0.20/0.38  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.20/0.38  fof(d4_zfmisc_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 0.20/0.38  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.20/0.38  fof(t79_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6]:(m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))=>(![X7]:(m1_subset_1(X7,X1)=>![X8]:(m1_subset_1(X8,X2)=>![X9]:(m1_subset_1(X9,X3)=>![X10]:(m1_subset_1(X10,X4)=>(X6=k4_mcart_1(X7,X8,X9,X10)=>X5=X7)))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k8_mcart_1(X1,X2,X3,X4,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_mcart_1)).
% 0.20/0.38  fof(t60_mcart_1, axiom, ![X1, X2, X3, X4]:~(((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)&~(![X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>X5=k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5),k10_mcart_1(X1,X2,X3,X4,X5),k11_mcart_1(X1,X2,X3,X4,X5)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_mcart_1)).
% 0.20/0.38  fof(dt_k11_mcart_1, axiom, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>m1_subset_1(k11_mcart_1(X1,X2,X3,X4,X5),X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k11_mcart_1)).
% 0.20/0.38  fof(dt_k10_mcart_1, axiom, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>m1_subset_1(k10_mcart_1(X1,X2,X3,X4,X5),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_mcart_1)).
% 0.20/0.38  fof(dt_k9_mcart_1, axiom, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>m1_subset_1(k9_mcart_1(X1,X2,X3,X4,X5),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_mcart_1)).
% 0.20/0.38  fof(dt_k8_mcart_1, axiom, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))=>m1_subset_1(k8_mcart_1(X1,X2,X3,X4,X5),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_mcart_1)).
% 0.20/0.38  fof(c_0_10, plain, ![X17, X18, X19, X20]:k4_mcart_1(X17,X18,X19,X20)=k4_tarski(k3_mcart_1(X17,X18,X19),X20), inference(variable_rename,[status(thm)],[d4_mcart_1])).
% 0.20/0.38  fof(c_0_11, plain, ![X11, X12, X13]:k3_mcart_1(X11,X12,X13)=k4_tarski(k4_tarski(X11,X12),X13), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.20/0.38  fof(c_0_12, plain, ![X21, X22, X23, X24]:k4_zfmisc_1(X21,X22,X23,X24)=k2_zfmisc_1(k3_zfmisc_1(X21,X22,X23),X24), inference(variable_rename,[status(thm)],[d4_zfmisc_1])).
% 0.20/0.38  fof(c_0_13, plain, ![X14, X15, X16]:k3_zfmisc_1(X14,X15,X16)=k2_zfmisc_1(k2_zfmisc_1(X14,X15),X16), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.20/0.38  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:(m1_subset_1(X6,k4_zfmisc_1(X1,X2,X3,X4))=>(![X7]:(m1_subset_1(X7,X1)=>![X8]:(m1_subset_1(X8,X2)=>![X9]:(m1_subset_1(X9,X3)=>![X10]:(m1_subset_1(X10,X4)=>(X6=k4_mcart_1(X7,X8,X9,X10)=>X5=X7)))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k8_mcart_1(X1,X2,X3,X4,X6))))), inference(assume_negation,[status(cth)],[t79_mcart_1])).
% 0.20/0.38  fof(c_0_15, plain, ![X45, X46, X47, X48, X49]:(X45=k1_xboole_0|X46=k1_xboole_0|X47=k1_xboole_0|X48=k1_xboole_0|(~m1_subset_1(X49,k4_zfmisc_1(X45,X46,X47,X48))|X49=k4_mcart_1(k8_mcart_1(X45,X46,X47,X48,X49),k9_mcart_1(X45,X46,X47,X48,X49),k10_mcart_1(X45,X46,X47,X48,X49),k11_mcart_1(X45,X46,X47,X48,X49)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_mcart_1])])])).
% 0.20/0.38  cnf(c_0_16, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_17, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_18, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_19, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  fof(c_0_20, negated_conjecture, ![X56, X57, X58, X59]:(m1_subset_1(esk6_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0))&((~m1_subset_1(X56,esk1_0)|(~m1_subset_1(X57,esk2_0)|(~m1_subset_1(X58,esk3_0)|(~m1_subset_1(X59,esk4_0)|(esk6_0!=k4_mcart_1(X56,X57,X58,X59)|esk5_0=X56)))))&((((esk1_0!=k1_xboole_0&esk2_0!=k1_xboole_0)&esk3_0!=k1_xboole_0)&esk4_0!=k1_xboole_0)&esk5_0!=k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])])).
% 0.20/0.38  fof(c_0_21, plain, ![X30, X31, X32, X33, X34]:(~m1_subset_1(X34,k4_zfmisc_1(X30,X31,X32,X33))|m1_subset_1(k11_mcart_1(X30,X31,X32,X33,X34),X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_mcart_1])])).
% 0.20/0.38  fof(c_0_22, plain, ![X25, X26, X27, X28, X29]:(~m1_subset_1(X29,k4_zfmisc_1(X25,X26,X27,X28))|m1_subset_1(k10_mcart_1(X25,X26,X27,X28,X29),X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k10_mcart_1])])).
% 0.20/0.38  fof(c_0_23, plain, ![X40, X41, X42, X43, X44]:(~m1_subset_1(X44,k4_zfmisc_1(X40,X41,X42,X43))|m1_subset_1(k9_mcart_1(X40,X41,X42,X43,X44),X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_mcart_1])])).
% 0.20/0.38  fof(c_0_24, plain, ![X35, X36, X37, X38, X39]:(~m1_subset_1(X39,k4_zfmisc_1(X35,X36,X37,X38))|m1_subset_1(k8_mcart_1(X35,X36,X37,X38,X39),X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_mcart_1])])).
% 0.20/0.38  cnf(c_0_25, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|X5=k4_mcart_1(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5),k10_mcart_1(X1,X2,X3,X4,X5),k11_mcart_1(X1,X2,X3,X4,X5))|~m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_26, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.38  cnf(c_0_27, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.38  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk6_0,k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.38  cnf(c_0_29, plain, (m1_subset_1(k11_mcart_1(X2,X3,X4,X5,X1),X5)|~m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.38  cnf(c_0_30, plain, (m1_subset_1(k10_mcart_1(X2,X3,X4,X5,X1),X4)|~m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.38  cnf(c_0_31, plain, (m1_subset_1(k9_mcart_1(X2,X3,X4,X5,X1),X3)|~m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.38  cnf(c_0_32, plain, (m1_subset_1(k8_mcart_1(X2,X3,X4,X5,X1),X2)|~m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_33, negated_conjecture, (esk5_0=X1|~m1_subset_1(X1,esk1_0)|~m1_subset_1(X2,esk2_0)|~m1_subset_1(X3,esk3_0)|~m1_subset_1(X4,esk4_0)|esk6_0!=k4_mcart_1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.38  cnf(c_0_34, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X5=k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(X1,X2,X3,X4,X5),k9_mcart_1(X1,X2,X3,X4,X5)),k10_mcart_1(X1,X2,X3,X4,X5)),k11_mcart_1(X1,X2,X3,X4,X5))|~m1_subset_1(X5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26]), c_0_27])).
% 0.20/0.38  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk6_0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0))), inference(rw,[status(thm)],[c_0_28, c_0_27])).
% 0.20/0.38  cnf(c_0_36, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.38  cnf(c_0_37, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.38  cnf(c_0_38, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.38  cnf(c_0_39, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.38  cnf(c_0_40, plain, (m1_subset_1(k11_mcart_1(X2,X3,X4,X5,X1),X5)|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X5))), inference(rw,[status(thm)],[c_0_29, c_0_27])).
% 0.20/0.38  cnf(c_0_41, plain, (m1_subset_1(k10_mcart_1(X2,X3,X4,X5,X1),X4)|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X5))), inference(rw,[status(thm)],[c_0_30, c_0_27])).
% 0.20/0.38  cnf(c_0_42, plain, (m1_subset_1(k9_mcart_1(X2,X3,X4,X5,X1),X3)|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X5))), inference(rw,[status(thm)],[c_0_31, c_0_27])).
% 0.20/0.38  cnf(c_0_43, plain, (m1_subset_1(k8_mcart_1(X2,X3,X4,X5,X1),X2)|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X5))), inference(rw,[status(thm)],[c_0_32, c_0_27])).
% 0.20/0.38  cnf(c_0_44, negated_conjecture, (esk5_0=X1|esk6_0!=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)|~m1_subset_1(X4,esk4_0)|~m1_subset_1(X3,esk3_0)|~m1_subset_1(X2,esk2_0)|~m1_subset_1(X1,esk1_0)), inference(rw,[status(thm)],[c_0_33, c_0_26])).
% 0.20/0.38  cnf(c_0_45, negated_conjecture, (k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)),k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)),k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0))=esk6_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.20/0.38  cnf(c_0_46, negated_conjecture, (m1_subset_1(k11_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),esk4_0)), inference(spm,[status(thm)],[c_0_40, c_0_35])).
% 0.20/0.38  cnf(c_0_47, negated_conjecture, (m1_subset_1(k10_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),esk3_0)), inference(spm,[status(thm)],[c_0_41, c_0_35])).
% 0.20/0.38  cnf(c_0_48, negated_conjecture, (m1_subset_1(k9_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),esk2_0)), inference(spm,[status(thm)],[c_0_42, c_0_35])).
% 0.20/0.38  cnf(c_0_49, negated_conjecture, (m1_subset_1(k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),esk1_0)), inference(spm,[status(thm)],[c_0_43, c_0_35])).
% 0.20/0.38  cnf(c_0_50, negated_conjecture, (esk5_0!=k8_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.38  cnf(c_0_51, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_47]), c_0_48]), c_0_49])]), c_0_50]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 52
% 0.20/0.38  # Proof object clause steps            : 31
% 0.20/0.38  # Proof object formula steps           : 21
% 0.20/0.38  # Proof object conjectures             : 18
% 0.20/0.38  # Proof object clause conjectures      : 15
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 16
% 0.20/0.38  # Proof object initial formulas used   : 10
% 0.20/0.38  # Proof object generating inferences   : 6
% 0.20/0.38  # Proof object simplifying inferences  : 20
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 10
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 16
% 0.20/0.38  # Removed in clause preprocessing      : 4
% 0.20/0.38  # Initial clauses in saturation        : 12
% 0.20/0.38  # Processed clauses                    : 29
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 0
% 0.20/0.38  # ...remaining for further processing  : 29
% 0.20/0.38  # Other redundant clauses eliminated   : 0
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 0
% 0.20/0.38  # Generated clauses                    : 8
% 0.20/0.38  # ...of the previous two non-trivial   : 7
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 8
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 0
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 17
% 0.20/0.38  #    Positive orientable unit clauses  : 6
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 5
% 0.20/0.38  #    Non-unit-clauses                  : 6
% 0.20/0.38  # Current number of unprocessed clauses: 0
% 0.20/0.38  # ...number of literals in the above   : 0
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 16
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 6
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 6
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.38  # Unit Clause-clause subsumption calls : 9
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 0
% 0.20/0.38  # BW rewrite match successes           : 0
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 1676
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.026 s
% 0.20/0.38  # System time              : 0.006 s
% 0.20/0.38  # Total time               : 0.032 s
% 0.20/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
