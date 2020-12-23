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
% DateTime   : Thu Dec  3 10:59:52 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 176 expanded)
%              Number of clauses        :   40 (  77 expanded)
%              Number of leaves         :   10 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :  181 ( 693 expanded)
%              Number of equality atoms :  142 ( 541 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t29_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k3_mcart_1(X3,X4,X5) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(t48_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(t46_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(t20_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t51_mcart_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => ( X4 != k5_mcart_1(X1,X2,X3,X4)
                & X4 != k6_mcart_1(X1,X2,X3,X4)
                & X4 != k7_mcart_1(X1,X2,X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_mcart_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(c_0_10,plain,(
    ! [X48,X50,X51,X52] :
      ( ( r2_hidden(esk6_1(X48),X48)
        | X48 = k1_xboole_0 )
      & ( ~ r2_hidden(X50,X48)
        | esk6_1(X48) != k3_mcart_1(X50,X51,X52)
        | X48 = k1_xboole_0 )
      & ( ~ r2_hidden(X51,X48)
        | esk6_1(X48) != k3_mcart_1(X50,X51,X52)
        | X48 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).

fof(c_0_11,plain,(
    ! [X30,X31,X32] : k3_mcart_1(X30,X31,X32) = k4_tarski(k4_tarski(X30,X31),X32) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_12,plain,(
    ! [X53,X54,X55,X56] :
      ( X53 = k1_xboole_0
      | X54 = k1_xboole_0
      | X55 = k1_xboole_0
      | ~ m1_subset_1(X56,k3_zfmisc_1(X53,X54,X55))
      | X56 = k3_mcart_1(k5_mcart_1(X53,X54,X55,X56),k6_mcart_1(X53,X54,X55,X56),k7_mcart_1(X53,X54,X55,X56)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).

fof(c_0_13,plain,(
    ! [X21,X22] : k2_xboole_0(k1_tarski(X21),X22) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

fof(c_0_14,plain,(
    ! [X19,X20] :
      ( ~ r2_hidden(X19,X20)
      | k2_xboole_0(k1_tarski(X19),X20) = X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_zfmisc_1])])).

fof(c_0_15,plain,(
    ! [X45,X46,X47] :
      ( ( X45 != k1_mcart_1(X45)
        | X45 != k4_tarski(X46,X47) )
      & ( X45 != k2_mcart_1(X45)
        | X45 != k4_tarski(X46,X47) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_mcart_1])])])])).

fof(c_0_16,plain,(
    ! [X61,X62] :
      ( k1_mcart_1(k4_tarski(X61,X62)) = X61
      & k2_mcart_1(k4_tarski(X61,X62)) = X62 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_17,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk6_1(X2) != k3_mcart_1(X3,X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_22,plain,(
    ! [X10,X11,X12,X13,X14,X15] :
      ( ( ~ r2_hidden(X12,X11)
        | X12 = X10
        | X11 != k1_tarski(X10) )
      & ( X13 != X10
        | r2_hidden(X13,X11)
        | X11 != k1_tarski(X10) )
      & ( ~ r2_hidden(esk3_2(X14,X15),X15)
        | esk3_2(X14,X15) != X14
        | X15 = k1_tarski(X14) )
      & ( r2_hidden(esk3_2(X14,X15),X15)
        | esk3_2(X14,X15) = X14
        | X15 = k1_tarski(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_23,plain,
    ( X1 != k2_mcart_1(X1)
    | X1 != k4_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & X3 != k1_xboole_0
          & ~ ! [X4] :
                ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
               => ( X4 != k5_mcart_1(X1,X2,X3,X4)
                  & X4 != k6_mcart_1(X1,X2,X3,X4)
                  & X4 != k7_mcart_1(X1,X2,X3,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t51_mcart_1])).

cnf(c_0_26,plain,
    ( X2 = k1_xboole_0
    | esk6_1(X2) != k4_tarski(k4_tarski(X3,X1),X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_27,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_28,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k4_tarski(X1,X2) != X2 ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_23]),c_0_24])).

fof(c_0_31,negated_conjecture,
    ( esk7_0 != k1_xboole_0
    & esk8_0 != k1_xboole_0
    & esk9_0 != k1_xboole_0
    & m1_subset_1(esk10_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0))
    & ( esk10_0 = k5_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0)
      | esk10_0 = k6_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0)
      | esk10_0 = k7_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

fof(c_0_32,plain,(
    ! [X8] : k2_xboole_0(X8,k1_xboole_0) = X8 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_33,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | esk6_1(X4) != X5
    | ~ m1_subset_1(X5,k3_zfmisc_1(X3,X2,X1))
    | ~ r2_hidden(k6_mcart_1(X3,X2,X1,X5),X4) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | X2 != k1_tarski(X1) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | k7_mcart_1(X3,X2,X1,X4) != X4
    | ~ m1_subset_1(X4,k3_zfmisc_1(X3,X2,X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( esk10_0 = k5_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0)
    | esk10_0 = k6_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0)
    | esk10_0 = k7_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk10_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( esk9_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_42,plain,
    ( r2_hidden(esk6_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_43,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk6_1(X2) != k3_mcart_1(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_45,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 != k1_tarski(k6_mcart_1(X1,X2,X3,X5))
    | esk6_1(X4) != X5
    | ~ m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( k5_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0) = esk10_0
    | k6_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0) = esk10_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_47,plain,
    ( esk6_1(X1) = X2
    | X1 = k1_xboole_0
    | X1 != k1_tarski(X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,plain,
    ( k1_tarski(X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_43])).

cnf(c_0_49,plain,
    ( X1 = X2
    | X3 != k1_tarski(X2)
    | X3 != k1_tarski(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_34])).

cnf(c_0_50,plain,
    ( X2 = k1_xboole_0
    | esk6_1(X2) != k4_tarski(k4_tarski(X1,X3),X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_44,c_0_18])).

cnf(c_0_51,negated_conjecture,
    ( k5_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0) = esk10_0
    | X1 != k1_tarski(esk10_0)
    | esk6_1(X1) != esk10_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_37])]),c_0_40]),c_0_39]),c_0_38])).

cnf(c_0_52,plain,
    ( esk6_1(k1_tarski(X1)) = X1 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_47]),c_0_48])).

cnf(c_0_53,plain,
    ( X1 = X2
    | k1_tarski(X2) != k1_tarski(X1) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_54,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | esk6_1(X4) != X5
    | ~ m1_subset_1(X5,k3_zfmisc_1(X3,X2,X1))
    | ~ r2_hidden(k5_mcart_1(X3,X2,X1,X5),X4) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_27]),c_0_28])).

cnf(c_0_55,negated_conjecture,
    ( k5_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0) = esk10_0
    | k1_tarski(X1) != k1_tarski(esk10_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])).

cnf(c_0_56,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 != k1_tarski(k5_mcart_1(X1,X2,X3,X5))
    | esk6_1(X4) != X5
    | ~ m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_34])).

cnf(c_0_57,negated_conjecture,
    ( k5_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0) = esk10_0 ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( X1 != k1_tarski(esk10_0)
    | esk6_1(X1) != esk10_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_37])]),c_0_40]),c_0_39]),c_0_38])).

cnf(c_0_59,negated_conjecture,
    ( k1_tarski(X1) != k1_tarski(esk10_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_52]),c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(er,[status(thm)],[c_0_59]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:35:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.44  # AutoSched0-Mode selected heuristic G_E___301_C18_F1_URBAN_S5PRR_S0Y
% 0.21/0.44  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.21/0.44  #
% 0.21/0.44  # Preprocessing time       : 0.030 s
% 0.21/0.44  
% 0.21/0.44  # Proof found!
% 0.21/0.44  # SZS status Theorem
% 0.21/0.44  # SZS output start CNFRefutation
% 0.21/0.44  fof(t29_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k3_mcart_1(X3,X4,X5))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 0.21/0.44  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.21/0.44  fof(t48_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_mcart_1)).
% 0.21/0.44  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.21/0.44  fof(t46_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 0.21/0.44  fof(t20_mcart_1, axiom, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 0.21/0.44  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.21/0.44  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.21/0.44  fof(t51_mcart_1, conjecture, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((X4!=k5_mcart_1(X1,X2,X3,X4)&X4!=k6_mcart_1(X1,X2,X3,X4))&X4!=k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_mcart_1)).
% 0.21/0.44  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.21/0.44  fof(c_0_10, plain, ![X48, X50, X51, X52]:((r2_hidden(esk6_1(X48),X48)|X48=k1_xboole_0)&((~r2_hidden(X50,X48)|esk6_1(X48)!=k3_mcart_1(X50,X51,X52)|X48=k1_xboole_0)&(~r2_hidden(X51,X48)|esk6_1(X48)!=k3_mcart_1(X50,X51,X52)|X48=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).
% 0.21/0.44  fof(c_0_11, plain, ![X30, X31, X32]:k3_mcart_1(X30,X31,X32)=k4_tarski(k4_tarski(X30,X31),X32), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.21/0.44  fof(c_0_12, plain, ![X53, X54, X55, X56]:(X53=k1_xboole_0|X54=k1_xboole_0|X55=k1_xboole_0|(~m1_subset_1(X56,k3_zfmisc_1(X53,X54,X55))|X56=k3_mcart_1(k5_mcart_1(X53,X54,X55,X56),k6_mcart_1(X53,X54,X55,X56),k7_mcart_1(X53,X54,X55,X56)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).
% 0.21/0.44  fof(c_0_13, plain, ![X21, X22]:k2_xboole_0(k1_tarski(X21),X22)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.21/0.44  fof(c_0_14, plain, ![X19, X20]:(~r2_hidden(X19,X20)|k2_xboole_0(k1_tarski(X19),X20)=X20), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_zfmisc_1])])).
% 0.21/0.44  fof(c_0_15, plain, ![X45, X46, X47]:((X45!=k1_mcart_1(X45)|X45!=k4_tarski(X46,X47))&(X45!=k2_mcart_1(X45)|X45!=k4_tarski(X46,X47))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_mcart_1])])])])).
% 0.21/0.44  fof(c_0_16, plain, ![X61, X62]:(k1_mcart_1(k4_tarski(X61,X62))=X61&k2_mcart_1(k4_tarski(X61,X62))=X62), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.21/0.44  cnf(c_0_17, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk6_1(X2)!=k3_mcart_1(X3,X1,X4)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.44  cnf(c_0_18, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.44  cnf(c_0_19, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.44  cnf(c_0_20, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.44  cnf(c_0_21, plain, (k2_xboole_0(k1_tarski(X1),X2)=X2|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.44  fof(c_0_22, plain, ![X10, X11, X12, X13, X14, X15]:(((~r2_hidden(X12,X11)|X12=X10|X11!=k1_tarski(X10))&(X13!=X10|r2_hidden(X13,X11)|X11!=k1_tarski(X10)))&((~r2_hidden(esk3_2(X14,X15),X15)|esk3_2(X14,X15)!=X14|X15=k1_tarski(X14))&(r2_hidden(esk3_2(X14,X15),X15)|esk3_2(X14,X15)=X14|X15=k1_tarski(X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.21/0.44  cnf(c_0_23, plain, (X1!=k2_mcart_1(X1)|X1!=k4_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.44  cnf(c_0_24, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.44  fof(c_0_25, negated_conjecture, ~(![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((X4!=k5_mcart_1(X1,X2,X3,X4)&X4!=k6_mcart_1(X1,X2,X3,X4))&X4!=k7_mcart_1(X1,X2,X3,X4))))))), inference(assume_negation,[status(cth)],[t51_mcart_1])).
% 0.21/0.44  cnf(c_0_26, plain, (X2=k1_xboole_0|esk6_1(X2)!=k4_tarski(k4_tarski(X3,X1),X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.21/0.44  cnf(c_0_27, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X4=k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(rw,[status(thm)],[c_0_19, c_0_18])).
% 0.21/0.44  cnf(c_0_28, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.21/0.44  cnf(c_0_29, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.44  cnf(c_0_30, plain, (k4_tarski(X1,X2)!=X2), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_23]), c_0_24])).
% 0.21/0.44  fof(c_0_31, negated_conjecture, (((esk7_0!=k1_xboole_0&esk8_0!=k1_xboole_0)&esk9_0!=k1_xboole_0)&(m1_subset_1(esk10_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0))&(esk10_0=k5_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0)|esk10_0=k6_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0)|esk10_0=k7_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 0.21/0.44  fof(c_0_32, plain, ![X8]:k2_xboole_0(X8,k1_xboole_0)=X8, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.21/0.44  cnf(c_0_33, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|esk6_1(X4)!=X5|~m1_subset_1(X5,k3_zfmisc_1(X3,X2,X1))|~r2_hidden(k6_mcart_1(X3,X2,X1,X5),X4)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.21/0.44  cnf(c_0_34, plain, (r2_hidden(X1,X2)|X2!=k1_tarski(X1)), inference(er,[status(thm)],[c_0_29])).
% 0.21/0.44  cnf(c_0_35, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|k7_mcart_1(X3,X2,X1,X4)!=X4|~m1_subset_1(X4,k3_zfmisc_1(X3,X2,X1))), inference(spm,[status(thm)],[c_0_30, c_0_27])).
% 0.21/0.44  cnf(c_0_36, negated_conjecture, (esk10_0=k5_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0)|esk10_0=k6_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0)|esk10_0=k7_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.44  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk10_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.44  cnf(c_0_38, negated_conjecture, (esk9_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.44  cnf(c_0_39, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.44  cnf(c_0_40, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.44  cnf(c_0_41, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.44  cnf(c_0_42, plain, (r2_hidden(esk6_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.44  cnf(c_0_43, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.44  cnf(c_0_44, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk6_1(X2)!=k3_mcart_1(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.44  cnf(c_0_45, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4!=k1_tarski(k6_mcart_1(X1,X2,X3,X5))|esk6_1(X4)!=X5|~m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.21/0.44  cnf(c_0_46, negated_conjecture, (k5_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0)=esk10_0|k6_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0)=esk10_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])]), c_0_38]), c_0_39]), c_0_40])).
% 0.21/0.44  cnf(c_0_47, plain, (esk6_1(X1)=X2|X1=k1_xboole_0|X1!=k1_tarski(X2)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.21/0.44  cnf(c_0_48, plain, (k1_tarski(X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_20, c_0_43])).
% 0.21/0.44  cnf(c_0_49, plain, (X1=X2|X3!=k1_tarski(X2)|X3!=k1_tarski(X1)), inference(spm,[status(thm)],[c_0_41, c_0_34])).
% 0.21/0.44  cnf(c_0_50, plain, (X2=k1_xboole_0|esk6_1(X2)!=k4_tarski(k4_tarski(X1,X3),X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_44, c_0_18])).
% 0.21/0.44  cnf(c_0_51, negated_conjecture, (k5_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0)=esk10_0|X1!=k1_tarski(esk10_0)|esk6_1(X1)!=esk10_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_37])]), c_0_40]), c_0_39]), c_0_38])).
% 0.21/0.44  cnf(c_0_52, plain, (esk6_1(k1_tarski(X1))=X1), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_47]), c_0_48])).
% 0.21/0.44  cnf(c_0_53, plain, (X1=X2|k1_tarski(X2)!=k1_tarski(X1)), inference(er,[status(thm)],[c_0_49])).
% 0.21/0.44  cnf(c_0_54, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|esk6_1(X4)!=X5|~m1_subset_1(X5,k3_zfmisc_1(X3,X2,X1))|~r2_hidden(k5_mcart_1(X3,X2,X1,X5),X4)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_27]), c_0_28])).
% 0.21/0.44  cnf(c_0_55, negated_conjecture, (k5_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0)=esk10_0|k1_tarski(X1)!=k1_tarski(esk10_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])).
% 0.21/0.44  cnf(c_0_56, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4!=k1_tarski(k5_mcart_1(X1,X2,X3,X5))|esk6_1(X4)!=X5|~m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))), inference(spm,[status(thm)],[c_0_54, c_0_34])).
% 0.21/0.44  cnf(c_0_57, negated_conjecture, (k5_mcart_1(esk7_0,esk8_0,esk9_0,esk10_0)=esk10_0), inference(er,[status(thm)],[c_0_55])).
% 0.21/0.44  cnf(c_0_58, negated_conjecture, (X1!=k1_tarski(esk10_0)|esk6_1(X1)!=esk10_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_37])]), c_0_40]), c_0_39]), c_0_38])).
% 0.21/0.44  cnf(c_0_59, negated_conjecture, (k1_tarski(X1)!=k1_tarski(esk10_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_52]), c_0_53])).
% 0.21/0.44  cnf(c_0_60, negated_conjecture, ($false), inference(er,[status(thm)],[c_0_59]), ['proof']).
% 0.21/0.44  # SZS output end CNFRefutation
% 0.21/0.44  # Proof object total steps             : 61
% 0.21/0.44  # Proof object clause steps            : 40
% 0.21/0.44  # Proof object formula steps           : 21
% 0.21/0.44  # Proof object conjectures             : 15
% 0.21/0.44  # Proof object clause conjectures      : 12
% 0.21/0.44  # Proof object formula conjectures     : 3
% 0.21/0.44  # Proof object initial clauses used    : 17
% 0.21/0.44  # Proof object initial formulas used   : 10
% 0.21/0.44  # Proof object generating inferences   : 19
% 0.21/0.44  # Proof object simplifying inferences  : 25
% 0.21/0.44  # Training examples: 0 positive, 0 negative
% 0.21/0.44  # Parsed axioms                        : 25
% 0.21/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.44  # Initial clauses                      : 41
% 0.21/0.44  # Removed in clause preprocessing      : 1
% 0.21/0.44  # Initial clauses in saturation        : 40
% 0.21/0.44  # Processed clauses                    : 304
% 0.21/0.44  # ...of these trivial                  : 5
% 0.21/0.44  # ...subsumed                          : 119
% 0.21/0.44  # ...remaining for further processing  : 180
% 0.21/0.44  # Other redundant clauses eliminated   : 35
% 0.21/0.44  # Clauses deleted for lack of memory   : 0
% 0.21/0.44  # Backward-subsumed                    : 17
% 0.21/0.44  # Backward-rewritten                   : 12
% 0.21/0.44  # Generated clauses                    : 1225
% 0.21/0.44  # ...of the previous two non-trivial   : 1152
% 0.21/0.44  # Contextual simplify-reflections      : 15
% 0.21/0.44  # Paramodulations                      : 1173
% 0.21/0.44  # Factorizations                       : 2
% 0.21/0.44  # Equation resolutions                 : 50
% 0.21/0.44  # Propositional unsat checks           : 0
% 0.21/0.44  #    Propositional check models        : 0
% 0.21/0.44  #    Propositional check unsatisfiable : 0
% 0.21/0.44  #    Propositional clauses             : 0
% 0.21/0.44  #    Propositional clauses after purity: 0
% 0.21/0.44  #    Propositional unsat core size     : 0
% 0.21/0.44  #    Propositional preprocessing time  : 0.000
% 0.21/0.44  #    Propositional encoding time       : 0.000
% 0.21/0.44  #    Propositional solver time         : 0.000
% 0.21/0.44  #    Success case prop preproc time    : 0.000
% 0.21/0.44  #    Success case prop encoding time   : 0.000
% 0.21/0.44  #    Success case prop solver time     : 0.000
% 0.21/0.44  # Current number of processed clauses  : 150
% 0.21/0.44  #    Positive orientable unit clauses  : 27
% 0.21/0.44  #    Positive unorientable unit clauses: 0
% 0.21/0.44  #    Negative unit clauses             : 17
% 0.21/0.44  #    Non-unit-clauses                  : 106
% 0.21/0.44  # Current number of unprocessed clauses: 859
% 0.21/0.44  # ...number of literals in the above   : 6915
% 0.21/0.44  # Current number of archived formulas  : 0
% 0.21/0.44  # Current number of archived clauses   : 30
% 0.21/0.44  # Clause-clause subsumption calls (NU) : 6009
% 0.21/0.44  # Rec. Clause-clause subsumption calls : 574
% 0.21/0.44  # Non-unit clause-clause subsumptions  : 111
% 0.21/0.44  # Unit Clause-clause subsumption calls : 361
% 0.21/0.44  # Rewrite failures with RHS unbound    : 0
% 0.21/0.44  # BW rewrite match attempts            : 9
% 0.21/0.44  # BW rewrite match successes           : 8
% 0.21/0.44  # Condensation attempts                : 0
% 0.21/0.44  # Condensation successes               : 0
% 0.21/0.44  # Termbank termtop insertions          : 22185
% 0.21/0.44  
% 0.21/0.44  # -------------------------------------------------
% 0.21/0.44  # User time                : 0.081 s
% 0.21/0.44  # System time              : 0.008 s
% 0.21/0.44  # Total time               : 0.089 s
% 0.21/0.44  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
