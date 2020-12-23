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
% DateTime   : Thu Dec  3 11:00:16 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 250 expanded)
%              Number of clauses        :   45 (  97 expanded)
%              Number of leaves         :   12 (  62 expanded)
%              Depth                    :   13
%              Number of atoms          :  222 (1264 expanded)
%              Number of equality atoms :  112 ( 764 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t71_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))
     => ( ! [X6] :
            ( m1_subset_1(X6,X1)
           => ! [X7] :
                ( m1_subset_1(X7,X2)
               => ! [X8] :
                    ( m1_subset_1(X8,X3)
                   => ( X5 = k3_mcart_1(X6,X7,X8)
                     => X4 = X8 ) ) ) )
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X3 = k1_xboole_0
          | X4 = k7_mcart_1(X1,X2,X3,X5) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(t50_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
                & k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
                & k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

fof(dt_k6_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k6_mcart_1(X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_mcart_1)).

fof(dt_k5_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k5_mcart_1(X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(t24_mcart_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & ~ ! [X3] :
              ( m1_subset_1(X3,k2_zfmisc_1(X1,X2))
             => X3 = k4_tarski(k1_mcart_1(X3),k2_mcart_1(X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_mcart_1)).

fof(dt_k7_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k7_mcart_1(X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_mcart_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ( m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))
       => ( ! [X6] :
              ( m1_subset_1(X6,X1)
             => ! [X7] :
                  ( m1_subset_1(X7,X2)
                 => ! [X8] :
                      ( m1_subset_1(X8,X3)
                     => ( X5 = k3_mcart_1(X6,X7,X8)
                       => X4 = X8 ) ) ) )
         => ( X1 = k1_xboole_0
            | X2 = k1_xboole_0
            | X3 = k1_xboole_0
            | X4 = k7_mcart_1(X1,X2,X3,X5) ) ) ) ),
    inference(assume_negation,[status(cth)],[t71_mcart_1])).

fof(c_0_13,negated_conjecture,(
    ! [X49,X50,X51] :
      ( m1_subset_1(esk5_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0))
      & ( ~ m1_subset_1(X49,esk1_0)
        | ~ m1_subset_1(X50,esk2_0)
        | ~ m1_subset_1(X51,esk3_0)
        | esk5_0 != k3_mcart_1(X49,X50,X51)
        | esk4_0 = X51 )
      & esk1_0 != k1_xboole_0
      & esk2_0 != k1_xboole_0
      & esk3_0 != k1_xboole_0
      & esk4_0 != k7_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).

fof(c_0_14,plain,(
    ! [X19,X20,X21] : k3_zfmisc_1(X19,X20,X21) = k2_zfmisc_1(k2_zfmisc_1(X19,X20),X21) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_15,plain,(
    ! [X12,X13] :
      ( ( ~ m1_subset_1(X13,X12)
        | r2_hidden(X13,X12)
        | v1_xboole_0(X12) )
      & ( ~ r2_hidden(X13,X12)
        | m1_subset_1(X13,X12)
        | v1_xboole_0(X12) )
      & ( ~ m1_subset_1(X13,X12)
        | v1_xboole_0(X13)
        | ~ v1_xboole_0(X12) )
      & ( ~ v1_xboole_0(X13)
        | m1_subset_1(X13,X12)
        | ~ v1_xboole_0(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk5_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X34,X35,X36] :
      ( ( r2_hidden(k1_mcart_1(X34),X35)
        | ~ r2_hidden(X34,k2_zfmisc_1(X35,X36)) )
      & ( r2_hidden(k2_mcart_1(X34),X36)
        | ~ r2_hidden(X34,k2_zfmisc_1(X35,X36)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk5_0,k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_21,plain,(
    ! [X40,X41,X42,X43] :
      ( ( k5_mcart_1(X40,X41,X42,X43) = k1_mcart_1(k1_mcart_1(X43))
        | ~ m1_subset_1(X43,k3_zfmisc_1(X40,X41,X42))
        | X40 = k1_xboole_0
        | X41 = k1_xboole_0
        | X42 = k1_xboole_0 )
      & ( k6_mcart_1(X40,X41,X42,X43) = k2_mcart_1(k1_mcart_1(X43))
        | ~ m1_subset_1(X43,k3_zfmisc_1(X40,X41,X42))
        | X40 = k1_xboole_0
        | X41 = k1_xboole_0
        | X42 = k1_xboole_0 )
      & ( k7_mcart_1(X40,X41,X42,X43) = k2_mcart_1(X43)
        | ~ m1_subset_1(X43,k3_zfmisc_1(X40,X41,X42))
        | X40 = k1_xboole_0
        | X41 = k1_xboole_0
        | X42 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).

cnf(c_0_22,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk5_0,k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_24,plain,(
    ! [X26,X27,X28,X29] :
      ( ~ m1_subset_1(X29,k3_zfmisc_1(X26,X27,X28))
      | m1_subset_1(k6_mcart_1(X26,X27,X28,X29),X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k6_mcart_1])])).

cnf(c_0_25,plain,
    ( k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_26,plain,(
    ! [X22,X23,X24,X25] :
      ( ~ m1_subset_1(X25,k3_zfmisc_1(X22,X23,X24))
      | m1_subset_1(k5_mcart_1(X22,X23,X24,X25),X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_mcart_1])])).

cnf(c_0_27,plain,
    ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_28,plain,(
    ! [X16,X17,X18] : k3_mcart_1(X16,X17,X18) = k4_tarski(k4_tarski(X16,X17),X18) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_29,plain,(
    ! [X37,X38,X39] :
      ( X37 = k1_xboole_0
      | X38 = k1_xboole_0
      | ~ m1_subset_1(X39,k2_zfmisc_1(X37,X38))
      | X39 = k4_tarski(k1_mcart_1(X39),k2_mcart_1(X39)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_mcart_1])])])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk5_0),k2_zfmisc_1(esk1_0,esk2_0))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_32,plain,
    ( m1_subset_1(k6_mcart_1(X2,X3,X4,X1),X3)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_17])).

cnf(c_0_34,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_35,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_36,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_37,plain,
    ( m1_subset_1(k5_mcart_1(X2,X3,X4,X1),X2)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_27,c_0_17])).

fof(c_0_39,plain,(
    ! [X30,X31,X32,X33] :
      ( ~ m1_subset_1(X33,k3_zfmisc_1(X30,X31,X32))
      | m1_subset_1(k7_mcart_1(X30,X31,X32,X33),X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_mcart_1])])).

cnf(c_0_40,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_41,negated_conjecture,
    ( esk4_0 = X3
    | ~ m1_subset_1(X1,esk1_0)
    | ~ m1_subset_1(X2,esk2_0)
    | ~ m1_subset_1(X3,esk3_0)
    | esk5_0 != k3_mcart_1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_42,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_43,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k4_tarski(k1_mcart_1(X3),k2_mcart_1(X3))
    | ~ m1_subset_1(X3,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(k1_mcart_1(esk5_0),k2_zfmisc_1(esk1_0,esk2_0))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0))
    | v1_xboole_0(k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_45,plain,
    ( m1_subset_1(k6_mcart_1(X2,X3,X4,X1),X3)
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_32,c_0_17])).

cnf(c_0_46,negated_conjecture,
    ( k6_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0) = k2_mcart_1(k1_mcart_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_20]),c_0_34]),c_0_35]),c_0_36])).

cnf(c_0_47,plain,
    ( m1_subset_1(k5_mcart_1(X2,X3,X4,X1),X2)
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_37,c_0_17])).

cnf(c_0_48,negated_conjecture,
    ( k5_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0) = k1_mcart_1(k1_mcart_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_20]),c_0_34]),c_0_35]),c_0_36])).

cnf(c_0_49,plain,
    ( m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_40,c_0_17])).

cnf(c_0_51,negated_conjecture,
    ( esk4_0 = X3
    | esk5_0 != k4_tarski(k4_tarski(X1,X2),X3)
    | ~ m1_subset_1(X3,esk3_0)
    | ~ m1_subset_1(X2,esk2_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(esk5_0)),k2_mcart_1(k1_mcart_1(esk5_0))) = k1_mcart_1(esk5_0)
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0))
    | v1_xboole_0(k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_35]),c_0_36])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(esk5_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_20])])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(esk5_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_20])])).

cnf(c_0_55,plain,
    ( m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_49,c_0_17])).

cnf(c_0_56,negated_conjecture,
    ( k7_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0) = k2_mcart_1(esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_20]),c_0_34]),c_0_35]),c_0_36])).

cnf(c_0_57,negated_conjecture,
    ( esk4_0 != k7_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_58,plain,(
    ! [X9] :
      ( ~ v1_xboole_0(X9)
      | X9 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_59,negated_conjecture,
    ( esk4_0 = X1
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0))
    | v1_xboole_0(k2_zfmisc_1(esk1_0,esk2_0))
    | k4_tarski(k1_mcart_1(esk5_0),X1) != esk5_0
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_54])])).

cnf(c_0_60,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk5_0),k2_mcart_1(esk5_0)) = esk5_0
    | k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_20]),c_0_34])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(k2_mcart_1(esk5_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_20])])).

cnf(c_0_62,negated_conjecture,
    ( k2_mcart_1(esk5_0) != esk4_0 ),
    inference(rw,[status(thm)],[c_0_57,c_0_56])).

cnf(c_0_63,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_64,plain,(
    ! [X10,X11] :
      ( ( k2_zfmisc_1(X10,X11) != k1_xboole_0
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0 )
      & ( X10 != k1_xboole_0
        | k2_zfmisc_1(X10,X11) = k1_xboole_0 )
      & ( X11 != k1_xboole_0
        | k2_zfmisc_1(X10,X11) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_65,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])]),c_0_62]),c_0_63])).

cnf(c_0_66,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0) = k1_xboole_0
    | k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_63,c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_34])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_68]),c_0_35]),c_0_36]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:50:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t71_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X8))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k7_mcart_1(X1,X2,X3,X5)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_mcart_1)).
% 0.13/0.38  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.13/0.38  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.13/0.38  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.13/0.38  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 0.13/0.38  fof(dt_k6_mcart_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>m1_subset_1(k6_mcart_1(X1,X2,X3,X4),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_mcart_1)).
% 0.13/0.38  fof(dt_k5_mcart_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>m1_subset_1(k5_mcart_1(X1,X2,X3,X4),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_mcart_1)).
% 0.13/0.38  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.13/0.38  fof(t24_mcart_1, axiom, ![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~(![X3]:(m1_subset_1(X3,k2_zfmisc_1(X1,X2))=>X3=k4_tarski(k1_mcart_1(X3),k2_mcart_1(X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_mcart_1)).
% 0.13/0.38  fof(dt_k7_mcart_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>m1_subset_1(k7_mcart_1(X1,X2,X3,X4),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_mcart_1)).
% 0.13/0.38  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.13/0.38  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.13/0.38  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X8))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k7_mcart_1(X1,X2,X3,X5))))), inference(assume_negation,[status(cth)],[t71_mcart_1])).
% 0.13/0.38  fof(c_0_13, negated_conjecture, ![X49, X50, X51]:(m1_subset_1(esk5_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0))&((~m1_subset_1(X49,esk1_0)|(~m1_subset_1(X50,esk2_0)|(~m1_subset_1(X51,esk3_0)|(esk5_0!=k3_mcart_1(X49,X50,X51)|esk4_0=X51))))&(((esk1_0!=k1_xboole_0&esk2_0!=k1_xboole_0)&esk3_0!=k1_xboole_0)&esk4_0!=k7_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).
% 0.13/0.38  fof(c_0_14, plain, ![X19, X20, X21]:k3_zfmisc_1(X19,X20,X21)=k2_zfmisc_1(k2_zfmisc_1(X19,X20),X21), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.13/0.38  fof(c_0_15, plain, ![X12, X13]:(((~m1_subset_1(X13,X12)|r2_hidden(X13,X12)|v1_xboole_0(X12))&(~r2_hidden(X13,X12)|m1_subset_1(X13,X12)|v1_xboole_0(X12)))&((~m1_subset_1(X13,X12)|v1_xboole_0(X13)|~v1_xboole_0(X12))&(~v1_xboole_0(X13)|m1_subset_1(X13,X12)|~v1_xboole_0(X12)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.13/0.38  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk5_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_17, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  fof(c_0_18, plain, ![X34, X35, X36]:((r2_hidden(k1_mcart_1(X34),X35)|~r2_hidden(X34,k2_zfmisc_1(X35,X36)))&(r2_hidden(k2_mcart_1(X34),X36)|~r2_hidden(X34,k2_zfmisc_1(X35,X36)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.13/0.38  cnf(c_0_19, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk5_0,k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0))), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.13/0.38  fof(c_0_21, plain, ![X40, X41, X42, X43]:(((k5_mcart_1(X40,X41,X42,X43)=k1_mcart_1(k1_mcart_1(X43))|~m1_subset_1(X43,k3_zfmisc_1(X40,X41,X42))|(X40=k1_xboole_0|X41=k1_xboole_0|X42=k1_xboole_0))&(k6_mcart_1(X40,X41,X42,X43)=k2_mcart_1(k1_mcart_1(X43))|~m1_subset_1(X43,k3_zfmisc_1(X40,X41,X42))|(X40=k1_xboole_0|X41=k1_xboole_0|X42=k1_xboole_0)))&(k7_mcart_1(X40,X41,X42,X43)=k2_mcart_1(X43)|~m1_subset_1(X43,k3_zfmisc_1(X40,X41,X42))|(X40=k1_xboole_0|X41=k1_xboole_0|X42=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 0.13/0.38  cnf(c_0_22, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (r2_hidden(esk5_0,k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0))|v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.38  fof(c_0_24, plain, ![X26, X27, X28, X29]:(~m1_subset_1(X29,k3_zfmisc_1(X26,X27,X28))|m1_subset_1(k6_mcart_1(X26,X27,X28,X29),X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k6_mcart_1])])).
% 0.13/0.38  cnf(c_0_25, plain, (k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  fof(c_0_26, plain, ![X22, X23, X24, X25]:(~m1_subset_1(X25,k3_zfmisc_1(X22,X23,X24))|m1_subset_1(k5_mcart_1(X22,X23,X24,X25),X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_mcart_1])])).
% 0.13/0.38  cnf(c_0_27, plain, (k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  fof(c_0_28, plain, ![X16, X17, X18]:k3_mcart_1(X16,X17,X18)=k4_tarski(k4_tarski(X16,X17),X18), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.13/0.38  fof(c_0_29, plain, ![X37, X38, X39]:(X37=k1_xboole_0|X38=k1_xboole_0|(~m1_subset_1(X39,k2_zfmisc_1(X37,X38))|X39=k4_tarski(k1_mcart_1(X39),k2_mcart_1(X39)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_mcart_1])])])).
% 0.13/0.38  cnf(c_0_30, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (r2_hidden(k1_mcart_1(esk5_0),k2_zfmisc_1(esk1_0,esk2_0))|v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.13/0.38  cnf(c_0_32, plain, (m1_subset_1(k6_mcart_1(X2,X3,X4,X1),X3)|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  cnf(c_0_33, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_25, c_0_17])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_37, plain, (m1_subset_1(k5_mcart_1(X2,X3,X4,X1),X2)|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.38  cnf(c_0_38, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_27, c_0_17])).
% 0.13/0.38  fof(c_0_39, plain, ![X30, X31, X32, X33]:(~m1_subset_1(X33,k3_zfmisc_1(X30,X31,X32))|m1_subset_1(k7_mcart_1(X30,X31,X32,X33),X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_mcart_1])])).
% 0.13/0.38  cnf(c_0_40, plain, (k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (esk4_0=X3|~m1_subset_1(X1,esk1_0)|~m1_subset_1(X2,esk2_0)|~m1_subset_1(X3,esk3_0)|esk5_0!=k3_mcart_1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_42, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.38  cnf(c_0_43, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k4_tarski(k1_mcart_1(X3),k2_mcart_1(X3))|~m1_subset_1(X3,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (m1_subset_1(k1_mcart_1(esk5_0),k2_zfmisc_1(esk1_0,esk2_0))|v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0))|v1_xboole_0(k2_zfmisc_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.38  cnf(c_0_45, plain, (m1_subset_1(k6_mcart_1(X2,X3,X4,X1),X3)|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))), inference(rw,[status(thm)],[c_0_32, c_0_17])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (k6_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0)=k2_mcart_1(k1_mcart_1(esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_20]), c_0_34]), c_0_35]), c_0_36])).
% 0.13/0.38  cnf(c_0_47, plain, (m1_subset_1(k5_mcart_1(X2,X3,X4,X1),X2)|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))), inference(rw,[status(thm)],[c_0_37, c_0_17])).
% 0.13/0.38  cnf(c_0_48, negated_conjecture, (k5_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0)=k1_mcart_1(k1_mcart_1(esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_20]), c_0_34]), c_0_35]), c_0_36])).
% 0.13/0.38  cnf(c_0_49, plain, (m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.38  cnf(c_0_50, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_40, c_0_17])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (esk4_0=X3|esk5_0!=k4_tarski(k4_tarski(X1,X2),X3)|~m1_subset_1(X3,esk3_0)|~m1_subset_1(X2,esk2_0)|~m1_subset_1(X1,esk1_0)), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 0.13/0.38  cnf(c_0_52, negated_conjecture, (k4_tarski(k1_mcart_1(k1_mcart_1(esk5_0)),k2_mcart_1(k1_mcart_1(esk5_0)))=k1_mcart_1(esk5_0)|v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0))|v1_xboole_0(k2_zfmisc_1(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_35]), c_0_36])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (m1_subset_1(k2_mcart_1(k1_mcart_1(esk5_0)),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_20])])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, (m1_subset_1(k1_mcart_1(k1_mcart_1(esk5_0)),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_20])])).
% 0.13/0.38  cnf(c_0_55, plain, (m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))), inference(rw,[status(thm)],[c_0_49, c_0_17])).
% 0.13/0.38  cnf(c_0_56, negated_conjecture, (k7_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0)=k2_mcart_1(esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_20]), c_0_34]), c_0_35]), c_0_36])).
% 0.13/0.38  cnf(c_0_57, negated_conjecture, (esk4_0!=k7_mcart_1(esk1_0,esk2_0,esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  fof(c_0_58, plain, ![X9]:(~v1_xboole_0(X9)|X9=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.13/0.38  cnf(c_0_59, negated_conjecture, (esk4_0=X1|v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0))|v1_xboole_0(k2_zfmisc_1(esk1_0,esk2_0))|k4_tarski(k1_mcart_1(esk5_0),X1)!=esk5_0|~m1_subset_1(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_54])])).
% 0.13/0.38  cnf(c_0_60, negated_conjecture, (k4_tarski(k1_mcart_1(esk5_0),k2_mcart_1(esk5_0))=esk5_0|k2_zfmisc_1(esk1_0,esk2_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_20]), c_0_34])).
% 0.13/0.38  cnf(c_0_61, negated_conjecture, (m1_subset_1(k2_mcart_1(esk5_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_20])])).
% 0.13/0.38  cnf(c_0_62, negated_conjecture, (k2_mcart_1(esk5_0)!=esk4_0), inference(rw,[status(thm)],[c_0_57, c_0_56])).
% 0.13/0.38  cnf(c_0_63, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.13/0.38  fof(c_0_64, plain, ![X10, X11]:((k2_zfmisc_1(X10,X11)!=k1_xboole_0|(X10=k1_xboole_0|X11=k1_xboole_0))&((X10!=k1_xboole_0|k2_zfmisc_1(X10,X11)=k1_xboole_0)&(X11!=k1_xboole_0|k2_zfmisc_1(X10,X11)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.13/0.38  cnf(c_0_65, negated_conjecture, (k2_zfmisc_1(esk1_0,esk2_0)=k1_xboole_0|v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])]), c_0_62]), c_0_63])).
% 0.13/0.38  cnf(c_0_66, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.13/0.38  cnf(c_0_67, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0)=k1_xboole_0|k2_zfmisc_1(esk1_0,esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_63, c_0_65])).
% 0.13/0.38  cnf(c_0_68, negated_conjecture, (k2_zfmisc_1(esk1_0,esk2_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_34])).
% 0.13/0.38  cnf(c_0_69, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_68]), c_0_35]), c_0_36]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 70
% 0.13/0.38  # Proof object clause steps            : 45
% 0.13/0.38  # Proof object formula steps           : 25
% 0.13/0.38  # Proof object conjectures             : 28
% 0.13/0.38  # Proof object clause conjectures      : 25
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 20
% 0.13/0.38  # Proof object initial formulas used   : 12
% 0.13/0.38  # Proof object generating inferences   : 16
% 0.13/0.38  # Proof object simplifying inferences  : 37
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 13
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 26
% 0.13/0.38  # Removed in clause preprocessing      : 2
% 0.13/0.38  # Initial clauses in saturation        : 24
% 0.13/0.38  # Processed clauses                    : 124
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 6
% 0.13/0.38  # ...remaining for further processing  : 118
% 0.13/0.38  # Other redundant clauses eliminated   : 2
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 7
% 0.13/0.38  # Backward-rewritten                   : 21
% 0.13/0.38  # Generated clauses                    : 155
% 0.13/0.38  # ...of the previous two non-trivial   : 151
% 0.13/0.38  # Contextual simplify-reflections      : 1
% 0.13/0.38  # Paramodulations                      : 153
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 2
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
% 0.13/0.38  # Current number of processed clauses  : 65
% 0.13/0.38  #    Positive orientable unit clauses  : 9
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 4
% 0.13/0.38  #    Non-unit-clauses                  : 52
% 0.13/0.38  # Current number of unprocessed clauses: 51
% 0.13/0.38  # ...number of literals in the above   : 173
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 53
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 534
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 412
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 12
% 0.13/0.38  # Unit Clause-clause subsumption calls : 18
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 3
% 0.13/0.38  # BW rewrite match successes           : 3
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 4233
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.036 s
% 0.13/0.38  # System time              : 0.003 s
% 0.13/0.38  # Total time               : 0.039 s
% 0.13/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
