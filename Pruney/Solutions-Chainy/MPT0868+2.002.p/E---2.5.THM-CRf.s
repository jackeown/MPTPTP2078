%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:33 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   77 (2116 expanded)
%              Number of clauses        :   58 (1051 expanded)
%              Number of leaves         :    9 ( 505 expanded)
%              Depth                    :   20
%              Number of atoms          :  202 (8443 expanded)
%              Number of equality atoms :   93 (3395 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t23_mcart_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,X2)
       => X1 = k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(t26_mcart_1,conjecture,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & ~ ! [X3] :
              ( m1_subset_1(X3,k2_zfmisc_1(X1,X2))
             => ( X3 != k1_mcart_1(X3)
                & X3 != k2_mcart_1(X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_mcart_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t20_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(c_0_9,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_10,plain,(
    ! [X13,X14,X15,X16,X19,X20,X21,X22,X23,X24,X26,X27] :
      ( ( r2_hidden(esk3_4(X13,X14,X15,X16),X13)
        | ~ r2_hidden(X16,X15)
        | X15 != k2_zfmisc_1(X13,X14) )
      & ( r2_hidden(esk4_4(X13,X14,X15,X16),X14)
        | ~ r2_hidden(X16,X15)
        | X15 != k2_zfmisc_1(X13,X14) )
      & ( X16 = k4_tarski(esk3_4(X13,X14,X15,X16),esk4_4(X13,X14,X15,X16))
        | ~ r2_hidden(X16,X15)
        | X15 != k2_zfmisc_1(X13,X14) )
      & ( ~ r2_hidden(X20,X13)
        | ~ r2_hidden(X21,X14)
        | X19 != k4_tarski(X20,X21)
        | r2_hidden(X19,X15)
        | X15 != k2_zfmisc_1(X13,X14) )
      & ( ~ r2_hidden(esk5_3(X22,X23,X24),X24)
        | ~ r2_hidden(X26,X22)
        | ~ r2_hidden(X27,X23)
        | esk5_3(X22,X23,X24) != k4_tarski(X26,X27)
        | X24 = k2_zfmisc_1(X22,X23) )
      & ( r2_hidden(esk6_3(X22,X23,X24),X22)
        | r2_hidden(esk5_3(X22,X23,X24),X24)
        | X24 = k2_zfmisc_1(X22,X23) )
      & ( r2_hidden(esk7_3(X22,X23,X24),X23)
        | r2_hidden(esk5_3(X22,X23,X24),X24)
        | X24 = k2_zfmisc_1(X22,X23) )
      & ( esk5_3(X22,X23,X24) = k4_tarski(esk6_3(X22,X23,X24),esk7_3(X22,X23,X24))
        | r2_hidden(esk5_3(X22,X23,X24),X24)
        | X24 = k2_zfmisc_1(X22,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_11,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( X1 != k2_zfmisc_1(X2,X3)
    | ~ r2_hidden(X4,X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_14,plain,(
    ! [X11] :
      ( X11 = k1_xboole_0
      | r2_hidden(esk2_1(X11),X11) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X2,X3))
    | ~ v1_xboole_0(X2) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_16,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_17,plain,(
    ! [X37,X38] :
      ( ~ v1_relat_1(X38)
      | ~ r2_hidden(X37,X38)
      | X37 = k4_tarski(k1_mcart_1(X37),k2_mcart_1(X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_mcart_1])])).

fof(c_0_18,plain,(
    ! [X30,X31] :
      ( ~ m1_subset_1(X30,X31)
      | v1_xboole_0(X31)
      | r2_hidden(X30,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & ~ ! [X3] :
                ( m1_subset_1(X3,k2_zfmisc_1(X1,X2))
               => ( X3 != k1_mcart_1(X3)
                  & X3 != k2_mcart_1(X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t26_mcart_1])).

cnf(c_0_20,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( X2 = k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,negated_conjecture,
    ( esk8_0 != k1_xboole_0
    & esk9_0 != k1_xboole_0
    & m1_subset_1(esk10_0,k2_zfmisc_1(esk8_0,esk9_0))
    & ( esk10_0 = k1_mcart_1(esk10_0)
      | esk10_0 = k2_mcart_1(esk10_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_24,plain,(
    ! [X32,X33] : v1_relat_1(k2_zfmisc_1(X32,X33)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_25,plain,(
    ! [X34,X35,X36] :
      ( ( X34 != k1_mcart_1(X34)
        | X34 != k4_tarski(X35,X36) )
      & ( X34 != k2_mcart_1(X34)
        | X34 != k4_tarski(X35,X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_mcart_1])])])])).

fof(c_0_26,plain,(
    ! [X39,X40] :
      ( k1_mcart_1(k4_tarski(X39,X40)) = X39
      & k2_mcart_1(k4_tarski(X39,X40)) = X40 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_20])).

cnf(c_0_28,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_29,plain,
    ( k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) = X1
    | v1_xboole_0(X2)
    | ~ v1_relat_1(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk10_0,k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( X1 != k1_mcart_1(X1)
    | X1 != k4_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( X1 = k4_tarski(esk3_4(X2,X3,X4,X1),esk4_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k2_zfmisc_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_34,plain,
    ( X1 != k2_mcart_1(X1)
    | X1 != k4_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk10_0),k2_mcart_1(esk10_0)) = esk10_0
    | v1_xboole_0(k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])])).

cnf(c_0_38,plain,
    ( X1 != k2_zfmisc_1(X2,X3)
    | k1_mcart_1(X4) != X4
    | ~ r2_hidden(X4,X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33])])).

cnf(c_0_39,plain,
    ( X1 != k2_zfmisc_1(k1_xboole_0,X2)
    | ~ r2_hidden(X3,X1)
    | ~ v1_xboole_0(X4) ),
    inference(spm,[status(thm)],[c_0_27,c_0_12])).

cnf(c_0_40,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) != k4_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_42,plain,
    ( k4_tarski(X1,X2) != X1 ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_32]),c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk10_0),k2_mcart_1(esk10_0)) = esk10_0
    | v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,plain,
    ( k1_mcart_1(X1) != X1
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(k1_xboole_0,X2))
    | ~ v1_xboole_0(X3) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( esk10_0 = k1_mcart_1(esk10_0)
    | esk10_0 = k2_mcart_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_47,plain,
    ( k4_tarski(X1,X2) != X2 ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( v1_xboole_0(k1_xboole_0)
    | k1_mcart_1(esk10_0) != esk10_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,plain,
    ( r2_hidden(X5,X6)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X5 != k4_tarski(X1,X3)
    | X6 != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_50,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | k1_mcart_1(X3) != X3
    | ~ m1_subset_1(X3,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_22])).

cnf(c_0_51,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_16])).

cnf(c_0_52,negated_conjecture,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
    | X1 != k4_tarski(X4,X5)
    | ~ r2_hidden(X5,X3)
    | ~ r2_hidden(X4,X2) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_54,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_16])).

cnf(c_0_55,negated_conjecture,
    ( v1_xboole_0(k2_zfmisc_1(esk8_0,esk9_0))
    | k1_mcart_1(esk10_0) != esk10_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_30])).

cnf(c_0_56,negated_conjecture,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,plain,
    ( X1 != k2_zfmisc_1(X2,X3)
    | k2_mcart_1(X4) != X4
    | ~ r2_hidden(X4,X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_33])])).

cnf(c_0_58,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | k1_mcart_1(esk10_0) != esk10_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_56]),c_0_52])])).

cnf(c_0_61,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X1)
    | r2_hidden(esk5_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_62,plain,
    ( k2_mcart_1(X1) != X1
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( k1_mcart_1(esk10_0) != esk10_0
    | ~ r2_hidden(X1,esk9_0)
    | ~ r2_hidden(X2,esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(esk5_3(k1_xboole_0,X2,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_56])).

cnf(c_0_65,negated_conjecture,
    ( esk9_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_66,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | k2_mcart_1(X3) != X3
    | ~ m1_subset_1(X3,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_22])).

cnf(c_0_67,negated_conjecture,
    ( k1_mcart_1(esk10_0) != esk10_0
    | ~ r2_hidden(X1,esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_69,negated_conjecture,
    ( v1_xboole_0(k2_zfmisc_1(esk8_0,esk9_0))
    | k2_mcart_1(esk10_0) != esk10_0 ),
    inference(spm,[status(thm)],[c_0_66,c_0_30])).

cnf(c_0_70,negated_conjecture,
    ( k1_mcart_1(esk10_0) != esk10_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_64]),c_0_68])).

cnf(c_0_71,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | k2_mcart_1(esk10_0) != esk10_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_69])).

cnf(c_0_72,negated_conjecture,
    ( k2_mcart_1(esk10_0) = esk10_0 ),
    inference(sr,[status(thm)],[c_0_46,c_0_70])).

cnf(c_0_73,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_72])])).

cnf(c_0_74,negated_conjecture,
    ( ~ r2_hidden(X1,esk9_0)
    | ~ r2_hidden(X2,esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_73]),c_0_60])).

cnf(c_0_75,negated_conjecture,
    ( ~ r2_hidden(X1,esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_64]),c_0_65])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_64]),c_0_68]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:52:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.20/0.41  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.027 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.41  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.20/0.41  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.20/0.41  fof(t23_mcart_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,X2)=>X1=k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_mcart_1)).
% 0.20/0.41  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.20/0.41  fof(t26_mcart_1, conjecture, ![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~(![X3]:(m1_subset_1(X3,k2_zfmisc_1(X1,X2))=>(X3!=k1_mcart_1(X3)&X3!=k2_mcart_1(X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_mcart_1)).
% 0.20/0.41  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.20/0.41  fof(t20_mcart_1, axiom, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 0.20/0.41  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.20/0.41  fof(c_0_9, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.41  fof(c_0_10, plain, ![X13, X14, X15, X16, X19, X20, X21, X22, X23, X24, X26, X27]:(((((r2_hidden(esk3_4(X13,X14,X15,X16),X13)|~r2_hidden(X16,X15)|X15!=k2_zfmisc_1(X13,X14))&(r2_hidden(esk4_4(X13,X14,X15,X16),X14)|~r2_hidden(X16,X15)|X15!=k2_zfmisc_1(X13,X14)))&(X16=k4_tarski(esk3_4(X13,X14,X15,X16),esk4_4(X13,X14,X15,X16))|~r2_hidden(X16,X15)|X15!=k2_zfmisc_1(X13,X14)))&(~r2_hidden(X20,X13)|~r2_hidden(X21,X14)|X19!=k4_tarski(X20,X21)|r2_hidden(X19,X15)|X15!=k2_zfmisc_1(X13,X14)))&((~r2_hidden(esk5_3(X22,X23,X24),X24)|(~r2_hidden(X26,X22)|~r2_hidden(X27,X23)|esk5_3(X22,X23,X24)!=k4_tarski(X26,X27))|X24=k2_zfmisc_1(X22,X23))&(((r2_hidden(esk6_3(X22,X23,X24),X22)|r2_hidden(esk5_3(X22,X23,X24),X24)|X24=k2_zfmisc_1(X22,X23))&(r2_hidden(esk7_3(X22,X23,X24),X23)|r2_hidden(esk5_3(X22,X23,X24),X24)|X24=k2_zfmisc_1(X22,X23)))&(esk5_3(X22,X23,X24)=k4_tarski(esk6_3(X22,X23,X24),esk7_3(X22,X23,X24))|r2_hidden(esk5_3(X22,X23,X24),X24)|X24=k2_zfmisc_1(X22,X23))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.20/0.41  cnf(c_0_11, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_12, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X1)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_13, plain, (X1!=k2_zfmisc_1(X2,X3)|~r2_hidden(X4,X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.20/0.41  fof(c_0_14, plain, ![X11]:(X11=k1_xboole_0|r2_hidden(esk2_1(X11),X11)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.20/0.41  cnf(c_0_15, plain, (~r2_hidden(X1,k2_zfmisc_1(X2,X3))|~v1_xboole_0(X2)), inference(er,[status(thm)],[c_0_13])).
% 0.20/0.41  cnf(c_0_16, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  fof(c_0_17, plain, ![X37, X38]:(~v1_relat_1(X38)|(~r2_hidden(X37,X38)|X37=k4_tarski(k1_mcart_1(X37),k2_mcart_1(X37)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_mcart_1])])).
% 0.20/0.41  fof(c_0_18, plain, ![X30, X31]:(~m1_subset_1(X30,X31)|(v1_xboole_0(X31)|r2_hidden(X30,X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.20/0.41  fof(c_0_19, negated_conjecture, ~(![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~(![X3]:(m1_subset_1(X3,k2_zfmisc_1(X1,X2))=>(X3!=k1_mcart_1(X3)&X3!=k2_mcart_1(X3))))))), inference(assume_negation,[status(cth)],[t26_mcart_1])).
% 0.20/0.41  cnf(c_0_20, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.41  cnf(c_0_21, plain, (X2=k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2))|~v1_relat_1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.41  cnf(c_0_22, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  fof(c_0_23, negated_conjecture, ((esk8_0!=k1_xboole_0&esk9_0!=k1_xboole_0)&(m1_subset_1(esk10_0,k2_zfmisc_1(esk8_0,esk9_0))&(esk10_0=k1_mcart_1(esk10_0)|esk10_0=k2_mcart_1(esk10_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.20/0.41  fof(c_0_24, plain, ![X32, X33]:v1_relat_1(k2_zfmisc_1(X32,X33)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.20/0.41  fof(c_0_25, plain, ![X34, X35, X36]:((X34!=k1_mcart_1(X34)|X34!=k4_tarski(X35,X36))&(X34!=k2_mcart_1(X34)|X34!=k4_tarski(X35,X36))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_mcart_1])])])])).
% 0.20/0.41  fof(c_0_26, plain, ![X39, X40]:(k1_mcart_1(k4_tarski(X39,X40))=X39&k2_mcart_1(k4_tarski(X39,X40))=X40), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.20/0.41  cnf(c_0_27, plain, (~r2_hidden(X1,k1_xboole_0)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_15, c_0_20])).
% 0.20/0.41  cnf(c_0_28, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_29, plain, (k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1))=X1|v1_xboole_0(X2)|~v1_relat_1(X2)|~m1_subset_1(X1,X2)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.41  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk10_0,k2_zfmisc_1(esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.41  cnf(c_0_31, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.41  cnf(c_0_32, plain, (X1!=k1_mcart_1(X1)|X1!=k4_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.41  cnf(c_0_33, plain, (X1=k4_tarski(esk3_4(X2,X3,X4,X1),esk4_4(X2,X3,X4,X1))|~r2_hidden(X1,X4)|X4!=k2_zfmisc_1(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_34, plain, (X1!=k2_mcart_1(X1)|X1!=k4_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.41  cnf(c_0_35, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.41  cnf(c_0_36, plain, (v1_xboole_0(k1_xboole_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.41  cnf(c_0_37, negated_conjecture, (k4_tarski(k1_mcart_1(esk10_0),k2_mcart_1(esk10_0))=esk10_0|v1_xboole_0(k2_zfmisc_1(esk8_0,esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])])).
% 0.20/0.41  cnf(c_0_38, plain, (X1!=k2_zfmisc_1(X2,X3)|k1_mcart_1(X4)!=X4|~r2_hidden(X4,X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33])])).
% 0.20/0.41  cnf(c_0_39, plain, (X1!=k2_zfmisc_1(k1_xboole_0,X2)|~r2_hidden(X3,X1)|~v1_xboole_0(X4)), inference(spm,[status(thm)],[c_0_27, c_0_12])).
% 0.20/0.41  cnf(c_0_40, plain, (k2_mcart_1(k4_tarski(X1,X2))!=k4_tarski(X1,X2)), inference(er,[status(thm)],[c_0_34])).
% 0.20/0.41  cnf(c_0_41, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.41  cnf(c_0_42, plain, (k4_tarski(X1,X2)!=X1), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_32]), c_0_35])).
% 0.20/0.41  cnf(c_0_43, negated_conjecture, (k4_tarski(k1_mcart_1(esk10_0),k2_mcart_1(esk10_0))=esk10_0|v1_xboole_0(k1_xboole_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.41  cnf(c_0_44, plain, (k1_mcart_1(X1)!=X1|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(er,[status(thm)],[c_0_38])).
% 0.20/0.41  cnf(c_0_45, plain, (~r2_hidden(X1,k2_zfmisc_1(k1_xboole_0,X2))|~v1_xboole_0(X3)), inference(er,[status(thm)],[c_0_39])).
% 0.20/0.41  cnf(c_0_46, negated_conjecture, (esk10_0=k1_mcart_1(esk10_0)|esk10_0=k2_mcart_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.41  cnf(c_0_47, plain, (k4_tarski(X1,X2)!=X2), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.41  cnf(c_0_48, negated_conjecture, (v1_xboole_0(k1_xboole_0)|k1_mcart_1(esk10_0)!=esk10_0), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.41  cnf(c_0_49, plain, (r2_hidden(X5,X6)|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X5!=k4_tarski(X1,X3)|X6!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_50, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|k1_mcart_1(X3)!=X3|~m1_subset_1(X3,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_44, c_0_22])).
% 0.20/0.41  cnf(c_0_51, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_45, c_0_16])).
% 0.20/0.41  cnf(c_0_52, negated_conjecture, (v1_xboole_0(k1_xboole_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_46]), c_0_47]), c_0_48])).
% 0.20/0.41  cnf(c_0_53, plain, (r2_hidden(X1,k2_zfmisc_1(X2,X3))|X1!=k4_tarski(X4,X5)|~r2_hidden(X5,X3)|~r2_hidden(X4,X2)), inference(er,[status(thm)],[c_0_49])).
% 0.20/0.41  cnf(c_0_54, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_11, c_0_16])).
% 0.20/0.41  cnf(c_0_55, negated_conjecture, (v1_xboole_0(k2_zfmisc_1(esk8_0,esk9_0))|k1_mcart_1(esk10_0)!=esk10_0), inference(spm,[status(thm)],[c_0_50, c_0_30])).
% 0.20/0.41  cnf(c_0_56, negated_conjecture, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.20/0.41  cnf(c_0_57, plain, (X1!=k2_zfmisc_1(X2,X3)|k2_mcart_1(X4)!=X4|~r2_hidden(X4,X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_33])])).
% 0.20/0.41  cnf(c_0_58, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))|~r2_hidden(X2,X4)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_53])).
% 0.20/0.41  cnf(c_0_59, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|k1_mcart_1(esk10_0)!=esk10_0), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.41  cnf(c_0_60, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_56]), c_0_52])])).
% 0.20/0.41  cnf(c_0_61, plain, (r2_hidden(esk6_3(X1,X2,X3),X1)|r2_hidden(esk5_3(X1,X2,X3),X3)|X3=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_62, plain, (k2_mcart_1(X1)!=X1|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(er,[status(thm)],[c_0_57])).
% 0.20/0.41  cnf(c_0_63, negated_conjecture, (k1_mcart_1(esk10_0)!=esk10_0|~r2_hidden(X1,esk9_0)|~r2_hidden(X2,esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])).
% 0.20/0.41  cnf(c_0_64, negated_conjecture, (X1=k1_xboole_0|r2_hidden(esk5_3(k1_xboole_0,X2,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_56])).
% 0.20/0.41  cnf(c_0_65, negated_conjecture, (esk9_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.41  cnf(c_0_66, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|k2_mcart_1(X3)!=X3|~m1_subset_1(X3,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_62, c_0_22])).
% 0.20/0.41  cnf(c_0_67, negated_conjecture, (k1_mcart_1(esk10_0)!=esk10_0|~r2_hidden(X1,esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65])).
% 0.20/0.41  cnf(c_0_68, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.41  cnf(c_0_69, negated_conjecture, (v1_xboole_0(k2_zfmisc_1(esk8_0,esk9_0))|k2_mcart_1(esk10_0)!=esk10_0), inference(spm,[status(thm)],[c_0_66, c_0_30])).
% 0.20/0.41  cnf(c_0_70, negated_conjecture, (k1_mcart_1(esk10_0)!=esk10_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_64]), c_0_68])).
% 0.20/0.41  cnf(c_0_71, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|k2_mcart_1(esk10_0)!=esk10_0), inference(spm,[status(thm)],[c_0_54, c_0_69])).
% 0.20/0.41  cnf(c_0_72, negated_conjecture, (k2_mcart_1(esk10_0)=esk10_0), inference(sr,[status(thm)],[c_0_46, c_0_70])).
% 0.20/0.41  cnf(c_0_73, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_72])])).
% 0.20/0.41  cnf(c_0_74, negated_conjecture, (~r2_hidden(X1,esk9_0)|~r2_hidden(X2,esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_73]), c_0_60])).
% 0.20/0.41  cnf(c_0_75, negated_conjecture, (~r2_hidden(X1,esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_64]), c_0_65])).
% 0.20/0.41  cnf(c_0_76, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_64]), c_0_68]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 77
% 0.20/0.41  # Proof object clause steps            : 58
% 0.20/0.41  # Proof object formula steps           : 19
% 0.20/0.41  # Proof object conjectures             : 26
% 0.20/0.41  # Proof object clause conjectures      : 23
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 18
% 0.20/0.41  # Proof object initial formulas used   : 9
% 0.20/0.41  # Proof object generating inferences   : 37
% 0.20/0.41  # Proof object simplifying inferences  : 20
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 9
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 22
% 0.20/0.41  # Removed in clause preprocessing      : 0
% 0.20/0.41  # Initial clauses in saturation        : 22
% 0.20/0.41  # Processed clauses                    : 957
% 0.20/0.41  # ...of these trivial                  : 15
% 0.20/0.41  # ...subsumed                          : 714
% 0.20/0.41  # ...remaining for further processing  : 228
% 0.20/0.41  # Other redundant clauses eliminated   : 3
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 17
% 0.20/0.41  # Backward-rewritten                   : 41
% 0.20/0.41  # Generated clauses                    : 2303
% 0.20/0.41  # ...of the previous two non-trivial   : 2015
% 0.20/0.41  # Contextual simplify-reflections      : 3
% 0.20/0.41  # Paramodulations                      : 2261
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 41
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 147
% 0.20/0.41  #    Positive orientable unit clauses  : 10
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 7
% 0.20/0.41  #    Non-unit-clauses                  : 130
% 0.20/0.41  # Current number of unprocessed clauses: 1002
% 0.20/0.41  # ...number of literals in the above   : 3984
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 81
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 8821
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 5241
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 449
% 0.20/0.41  # Unit Clause-clause subsumption calls : 281
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 11
% 0.20/0.41  # BW rewrite match successes           : 11
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 20791
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.063 s
% 0.20/0.41  # System time              : 0.010 s
% 0.20/0.41  # Total time               : 0.073 s
% 0.20/0.41  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
