%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : mcart_1__t10_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:03 EDT 2019

% Result     : Theorem 4.91s
% Output     : CNFRefutation 4.91s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 115 expanded)
%              Number of clauses        :   38 (  59 expanded)
%              Number of leaves         :    7 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :  162 ( 493 expanded)
%              Number of equality atoms :   75 ( 193 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ! [X2] :
          ( X2 = k2_mcart_1(X1)
        <=> ! [X3,X4] :
              ( X1 = k4_tarski(X3,X4)
             => X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t10_mcart_1.p',d2_mcart_1)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t10_mcart_1.p',d2_zfmisc_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t10_mcart_1.p',t7_boole)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t10_mcart_1.p',t1_subset)).

fof(d1_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ! [X2] :
          ( X2 = k1_mcart_1(X1)
        <=> ! [X3,X4] :
              ( X1 = k4_tarski(X3,X4)
             => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t10_mcart_1.p',d1_mcart_1)).

fof(t10_mcart_1,conjecture,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t10_mcart_1.p',t10_mcart_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t10_mcart_1.p',t2_subset)).

fof(c_0_7,plain,(
    ! [X21,X22,X23,X24,X25,X26,X27] :
      ( ( X24 != k2_mcart_1(X21)
        | X21 != k4_tarski(X25,X26)
        | X24 = X26
        | X21 != k4_tarski(X22,X23) )
      & ( X21 = k4_tarski(esk6_2(X21,X27),esk7_2(X21,X27))
        | X27 = k2_mcart_1(X21)
        | X21 != k4_tarski(X22,X23) )
      & ( X27 != esk7_2(X21,X27)
        | X27 = k2_mcart_1(X21)
        | X21 != k4_tarski(X22,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_mcart_1])])])])])])).

cnf(c_0_8,plain,
    ( X1 = X4
    | X1 != k2_mcart_1(X2)
    | X2 != k4_tarski(X3,X4)
    | X2 != k4_tarski(X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_9,plain,
    ( X1 = X2
    | k4_tarski(X3,X4) != k4_tarski(X5,X2)
    | X1 != k2_mcart_1(k4_tarski(X3,X4)) ),
    inference(er,[status(thm)],[c_0_8])).

fof(c_0_10,plain,(
    ! [X30,X31,X32,X33,X36,X37,X38,X39,X40,X41,X43,X44] :
      ( ( r2_hidden(esk8_4(X30,X31,X32,X33),X30)
        | ~ r2_hidden(X33,X32)
        | X32 != k2_zfmisc_1(X30,X31) )
      & ( r2_hidden(esk9_4(X30,X31,X32,X33),X31)
        | ~ r2_hidden(X33,X32)
        | X32 != k2_zfmisc_1(X30,X31) )
      & ( X33 = k4_tarski(esk8_4(X30,X31,X32,X33),esk9_4(X30,X31,X32,X33))
        | ~ r2_hidden(X33,X32)
        | X32 != k2_zfmisc_1(X30,X31) )
      & ( ~ r2_hidden(X37,X30)
        | ~ r2_hidden(X38,X31)
        | X36 != k4_tarski(X37,X38)
        | r2_hidden(X36,X32)
        | X32 != k2_zfmisc_1(X30,X31) )
      & ( ~ r2_hidden(esk10_3(X39,X40,X41),X41)
        | ~ r2_hidden(X43,X39)
        | ~ r2_hidden(X44,X40)
        | esk10_3(X39,X40,X41) != k4_tarski(X43,X44)
        | X41 = k2_zfmisc_1(X39,X40) )
      & ( r2_hidden(esk11_3(X39,X40,X41),X39)
        | r2_hidden(esk10_3(X39,X40,X41),X41)
        | X41 = k2_zfmisc_1(X39,X40) )
      & ( r2_hidden(esk12_3(X39,X40,X41),X40)
        | r2_hidden(esk10_3(X39,X40,X41),X41)
        | X41 = k2_zfmisc_1(X39,X40) )
      & ( esk10_3(X39,X40,X41) = k4_tarski(esk11_3(X39,X40,X41),esk12_3(X39,X40,X41))
        | r2_hidden(esk10_3(X39,X40,X41),X41)
        | X41 = k2_zfmisc_1(X39,X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

fof(c_0_11,plain,(
    ! [X54,X55] :
      ( ~ r2_hidden(X54,X55)
      | ~ v1_xboole_0(X55) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_12,plain,(
    ! [X49,X50] :
      ( ~ r2_hidden(X49,X50)
      | m1_subset_1(X49,X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_13,plain,(
    ! [X12,X13,X14,X15,X16,X17,X18] :
      ( ( X15 != k1_mcart_1(X12)
        | X12 != k4_tarski(X16,X17)
        | X15 = X16
        | X12 != k4_tarski(X13,X14) )
      & ( X12 = k4_tarski(esk4_2(X12,X18),esk5_2(X12,X18))
        | X18 = k1_mcart_1(X12)
        | X12 != k4_tarski(X13,X14) )
      & ( X18 != esk4_2(X12,X18)
        | X18 = k1_mcart_1(X12)
        | X12 != k4_tarski(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_mcart_1])])])])])])).

cnf(c_0_14,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X3
    | k4_tarski(X1,X2) != k4_tarski(X4,X3) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( X1 = k4_tarski(esk8_4(X2,X3,X4,X1),esk9_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k2_zfmisc_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
       => ( r2_hidden(k1_mcart_1(X1),X2)
          & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    inference(assume_negation,[status(cth)],[t10_mcart_1])).

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( r2_hidden(esk8_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( r2_hidden(esk9_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( X1 = X3
    | X1 != k1_mcart_1(X2)
    | X2 != k4_tarski(X3,X4)
    | X2 != k4_tarski(X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k4_tarski(esk8_4(X1,X2,k2_zfmisc_1(X1,X2),X3),esk9_4(X1,X2,k2_zfmisc_1(X1,X2),X3)) = X3
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_15])).

fof(c_0_24,negated_conjecture,
    ( r2_hidden(esk1_0,k2_zfmisc_1(esk2_0,esk3_0))
    & ( ~ r2_hidden(k1_mcart_1(esk1_0),esk2_0)
      | ~ r2_hidden(k2_mcart_1(esk1_0),esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_25,plain,(
    ! [X51,X52] :
      ( ~ m1_subset_1(X51,X52)
      | v1_xboole_0(X52)
      | r2_hidden(X51,X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_26,plain,
    ( X1 != k2_zfmisc_1(X2,X3)
    | ~ v1_xboole_0(X2)
    | ~ r2_hidden(X4,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_27,plain,
    ( X1 != k2_zfmisc_1(X2,X3)
    | ~ v1_xboole_0(X3)
    | ~ r2_hidden(X4,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_19])).

cnf(c_0_28,plain,
    ( m1_subset_1(esk9_4(X1,X2,X3,X4),X2)
    | X3 != k2_zfmisc_1(X1,X2)
    | ~ r2_hidden(X4,X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_19])).

cnf(c_0_29,plain,
    ( X1 = X2
    | k4_tarski(X3,X4) != k4_tarski(X2,X5)
    | X1 != k1_mcart_1(k4_tarski(X3,X4)) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( esk9_4(X1,X2,k2_zfmisc_1(X1,X2),X3) = k2_mcart_1(X3)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk1_0,k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( ~ r2_hidden(k1_mcart_1(esk1_0),esk2_0)
    | ~ r2_hidden(k2_mcart_1(esk1_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k2_zfmisc_1(X1,X3)) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k2_zfmisc_1(X3,X1)) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( m1_subset_1(esk9_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( m1_subset_1(esk8_4(X1,X2,X3,X4),X1)
    | X3 != k2_zfmisc_1(X1,X2)
    | ~ r2_hidden(X4,X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_18])).

cnf(c_0_38,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X3
    | k4_tarski(X1,X2) != k4_tarski(X3,X4) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( esk9_4(esk2_0,esk3_0,k2_zfmisc_1(esk2_0,esk3_0),esk1_0) = k2_mcart_1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | ~ m1_subset_1(k2_mcart_1(esk1_0),esk3_0)
    | ~ r2_hidden(k1_mcart_1(esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_31])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk9_4(esk2_0,esk3_0,k2_zfmisc_1(esk2_0,esk3_0),esk1_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_31])).

cnf(c_0_44,plain,
    ( m1_subset_1(esk8_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( k4_tarski(esk8_4(esk2_0,esk3_0,k2_zfmisc_1(esk2_0,esk3_0),esk1_0),k2_mcart_1(esk1_0)) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_39]),c_0_31])])).

cnf(c_0_47,negated_conjecture,
    ( ~ m1_subset_1(k2_mcart_1(esk1_0),esk3_0)
    | ~ m1_subset_1(k1_mcart_1(esk1_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_33]),c_0_41]),c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(k2_mcart_1(esk1_0),esk3_0) ),
    inference(rw,[status(thm)],[c_0_43,c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk8_4(esk2_0,esk3_0,k2_zfmisc_1(esk2_0,esk3_0),esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_31])).

cnf(c_0_50,negated_conjecture,
    ( esk8_4(esk2_0,esk3_0,k2_zfmisc_1(esk2_0,esk3_0),esk1_0) = k1_mcart_1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( ~ m1_subset_1(k1_mcart_1(esk1_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48])])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50]),c_0_51]),
    [proof]).
%------------------------------------------------------------------------------
