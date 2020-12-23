%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:12:58 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   55 (  82 expanded)
%              Number of clauses        :   28 (  34 expanded)
%              Number of leaves         :   13 (  21 expanded)
%              Depth                    :   11
%              Number of atoms          :  151 ( 214 expanded)
%              Number of equality atoms :   57 (  93 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_tops_2,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( X2 != k1_xboole_0
       => k5_setfam_1(X1,k7_setfam_1(X1,X2)) = k3_subset_1(X1,k6_setfam_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tops_2)).

fof(t11_tops_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( X2 != k1_xboole_0
       => k6_setfam_1(X1,k7_setfam_1(X1,X2)) = k3_subset_1(X1,k5_setfam_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tops_2)).

fof(involutiveness_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k7_setfam_1(X1,k7_setfam_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(dt_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(dt_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k5_setfam_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(d8_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
         => ( X3 = k7_setfam_1(X1,X2)
          <=> ! [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(X1))
               => ( r2_hidden(X4,X3)
                <=> r2_hidden(k3_subset_1(X1,X4),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(t34_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5,X6] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k4_mcart_1(X3,X4,X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ( X2 != k1_xboole_0
         => k5_setfam_1(X1,k7_setfam_1(X1,X2)) = k3_subset_1(X1,k6_setfam_1(X1,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t12_tops_2])).

fof(c_0_14,plain,(
    ! [X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(k1_zfmisc_1(X35)))
      | X36 = k1_xboole_0
      | k6_setfam_1(X35,k7_setfam_1(X35,X36)) = k3_subset_1(X35,k5_setfam_1(X35,X36)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tops_2])])).

fof(c_0_15,plain,(
    ! [X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24)))
      | k7_setfam_1(X24,k7_setfam_1(X24,X25)) = X25 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).

fof(c_0_16,plain,(
    ! [X22,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(X22)))
      | m1_subset_1(k7_setfam_1(X22,X23),k1_zfmisc_1(k1_zfmisc_1(X22))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).

fof(c_0_17,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))
    & esk4_0 != k1_xboole_0
    & k5_setfam_1(esk3_0,k7_setfam_1(esk3_0,esk4_0)) != k3_subset_1(esk3_0,k6_setfam_1(esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_18,plain,
    ( X1 = k1_xboole_0
    | k6_setfam_1(X2,k7_setfam_1(X2,X1)) = k3_subset_1(X2,k5_setfam_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k7_setfam_1(X2,k7_setfam_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( k5_setfam_1(esk3_0,k7_setfam_1(esk3_0,esk4_0)) != k3_subset_1(esk3_0,k6_setfam_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( k6_setfam_1(X1,X2) = k3_subset_1(X1,k5_setfam_1(X1,k7_setfam_1(X1,X2)))
    | k7_setfam_1(X1,X2) = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(X12))
      | k3_subset_1(X12,k3_subset_1(X12,X13)) = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_25,negated_conjecture,
    ( k7_setfam_1(esk3_0,esk4_0) = k1_xboole_0
    | k3_subset_1(esk3_0,k3_subset_1(esk3_0,k5_setfam_1(esk3_0,k7_setfam_1(esk3_0,esk4_0)))) != k5_setfam_1(esk3_0,k7_setfam_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_26,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_27,plain,(
    ! [X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X20)))
      | m1_subset_1(k5_setfam_1(X20,X21),k1_zfmisc_1(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_setfam_1])])).

fof(c_0_28,plain,(
    ! [X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X18,X17)
        | r2_hidden(k3_subset_1(X15,X18),X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X15))
        | X17 != k7_setfam_1(X15,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X15)))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(X15))) )
      & ( ~ r2_hidden(k3_subset_1(X15,X18),X16)
        | r2_hidden(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X15))
        | X17 != k7_setfam_1(X15,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X15)))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(X15))) )
      & ( m1_subset_1(esk1_3(X15,X16,X17),k1_zfmisc_1(X15))
        | X17 = k7_setfam_1(X15,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X15)))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(X15))) )
      & ( ~ r2_hidden(esk1_3(X15,X16,X17),X17)
        | ~ r2_hidden(k3_subset_1(X15,esk1_3(X15,X16,X17)),X16)
        | X17 = k7_setfam_1(X15,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X15)))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(X15))) )
      & ( r2_hidden(esk1_3(X15,X16,X17),X17)
        | r2_hidden(k3_subset_1(X15,esk1_3(X15,X16,X17)),X16)
        | X17 = k7_setfam_1(X15,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X15)))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(X15))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_setfam_1])])])])])).

fof(c_0_29,plain,(
    ! [X26,X27,X28] :
      ( ~ r2_hidden(X26,X27)
      | ~ m1_subset_1(X27,k1_zfmisc_1(X28))
      | m1_subset_1(X26,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_30,negated_conjecture,
    ( k7_setfam_1(esk3_0,esk4_0) = k1_xboole_0
    | ~ m1_subset_1(k5_setfam_1(esk3_0,k7_setfam_1(esk3_0,esk4_0)),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( m1_subset_1(k5_setfam_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( r2_hidden(k3_subset_1(X3,X1),X4)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | X2 != k7_setfam_1(X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( k7_setfam_1(esk3_0,esk4_0) = k1_xboole_0
    | ~ m1_subset_1(k7_setfam_1(esk3_0,esk4_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_35,plain,(
    ! [X10,X11] :
      ( ( k4_xboole_0(X10,k1_tarski(X11)) != X10
        | ~ r2_hidden(X11,X10) )
      & ( r2_hidden(X11,X10)
        | k4_xboole_0(X10,k1_tarski(X11)) = X10 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_36,plain,(
    ! [X7,X8] : k4_xboole_0(X7,X8) = k5_xboole_0(X7,k3_xboole_0(X7,X8)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_37,plain,
    ( r2_hidden(k3_subset_1(X1,X2),X3)
    | X4 != k7_setfam_1(X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X2,X4) ),
    inference(csr,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( k7_setfam_1(esk3_0,esk4_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_20]),c_0_23])])).

fof(c_0_39,plain,(
    ! [X14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X14)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_40,plain,(
    ! [X9] : k4_xboole_0(k1_xboole_0,X9) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,k1_tarski(X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk3_0,X1),X2)
    | k7_setfam_1(esk3_0,X2) != esk4_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_23])).

cnf(c_0_44,negated_conjecture,
    ( k7_setfam_1(esk3_0,k1_xboole_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_38]),c_0_23])])).

cnf(c_0_45,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_tarski(X2))) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk3_0,X1),k1_xboole_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

cnf(c_0_49,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_46,c_0_42])).

fof(c_0_50,plain,(
    ! [X29,X31,X32,X33,X34] :
      ( ( r2_hidden(esk2_1(X29),X29)
        | X29 = k1_xboole_0 )
      & ( ~ r2_hidden(X31,X29)
        | esk2_1(X29) != k4_mcart_1(X31,X32,X33,X34)
        | X29 = k1_xboole_0 )
      & ( ~ r2_hidden(X32,X29)
        | esk2_1(X29) != k4_mcart_1(X31,X32,X33,X34)
        | X29 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_mcart_1])])])])])])).

cnf(c_0_51,negated_conjecture,
    ( ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])])).

cnf(c_0_52,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:16:51 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.12/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t12_tops_2, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(X2!=k1_xboole_0=>k5_setfam_1(X1,k7_setfam_1(X1,X2))=k3_subset_1(X1,k6_setfam_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_tops_2)).
% 0.12/0.37  fof(t11_tops_2, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(X2!=k1_xboole_0=>k6_setfam_1(X1,k7_setfam_1(X1,X2))=k3_subset_1(X1,k5_setfam_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tops_2)).
% 0.12/0.37  fof(involutiveness_k7_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k7_setfam_1(X1,k7_setfam_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 0.12/0.37  fof(dt_k7_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 0.12/0.37  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.12/0.37  fof(dt_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(k5_setfam_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 0.12/0.37  fof(d8_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(X3=k7_setfam_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>(r2_hidden(X4,X3)<=>r2_hidden(k3_subset_1(X1,X4),X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_setfam_1)).
% 0.12/0.37  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.12/0.37  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.12/0.37  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.12/0.37  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.12/0.37  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 0.12/0.37  fof(t34_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5, X6]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_mcart_1(X3,X4,X5,X6))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_mcart_1)).
% 0.12/0.37  fof(c_0_13, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(X2!=k1_xboole_0=>k5_setfam_1(X1,k7_setfam_1(X1,X2))=k3_subset_1(X1,k6_setfam_1(X1,X2))))), inference(assume_negation,[status(cth)],[t12_tops_2])).
% 0.12/0.37  fof(c_0_14, plain, ![X35, X36]:(~m1_subset_1(X36,k1_zfmisc_1(k1_zfmisc_1(X35)))|(X36=k1_xboole_0|k6_setfam_1(X35,k7_setfam_1(X35,X36))=k3_subset_1(X35,k5_setfam_1(X35,X36)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tops_2])])).
% 0.12/0.37  fof(c_0_15, plain, ![X24, X25]:(~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24)))|k7_setfam_1(X24,k7_setfam_1(X24,X25))=X25), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).
% 0.12/0.37  fof(c_0_16, plain, ![X22, X23]:(~m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(X22)))|m1_subset_1(k7_setfam_1(X22,X23),k1_zfmisc_1(k1_zfmisc_1(X22)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).
% 0.12/0.37  fof(c_0_17, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))&(esk4_0!=k1_xboole_0&k5_setfam_1(esk3_0,k7_setfam_1(esk3_0,esk4_0))!=k3_subset_1(esk3_0,k6_setfam_1(esk3_0,esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.12/0.37  cnf(c_0_18, plain, (X1=k1_xboole_0|k6_setfam_1(X2,k7_setfam_1(X2,X1))=k3_subset_1(X2,k5_setfam_1(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.37  cnf(c_0_19, plain, (k7_setfam_1(X2,k7_setfam_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_20, plain, (m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_21, negated_conjecture, (k5_setfam_1(esk3_0,k7_setfam_1(esk3_0,esk4_0))!=k3_subset_1(esk3_0,k6_setfam_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  cnf(c_0_22, plain, (k6_setfam_1(X1,X2)=k3_subset_1(X1,k5_setfam_1(X1,k7_setfam_1(X1,X2)))|k7_setfam_1(X1,X2)=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 0.12/0.37  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  fof(c_0_24, plain, ![X12, X13]:(~m1_subset_1(X13,k1_zfmisc_1(X12))|k3_subset_1(X12,k3_subset_1(X12,X13))=X13), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.12/0.37  cnf(c_0_25, negated_conjecture, (k7_setfam_1(esk3_0,esk4_0)=k1_xboole_0|k3_subset_1(esk3_0,k3_subset_1(esk3_0,k5_setfam_1(esk3_0,k7_setfam_1(esk3_0,esk4_0))))!=k5_setfam_1(esk3_0,k7_setfam_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 0.12/0.37  cnf(c_0_26, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.37  fof(c_0_27, plain, ![X20, X21]:(~m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X20)))|m1_subset_1(k5_setfam_1(X20,X21),k1_zfmisc_1(X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_setfam_1])])).
% 0.12/0.37  fof(c_0_28, plain, ![X15, X16, X17, X18]:(((~r2_hidden(X18,X17)|r2_hidden(k3_subset_1(X15,X18),X16)|~m1_subset_1(X18,k1_zfmisc_1(X15))|X17!=k7_setfam_1(X15,X16)|~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X15)))|~m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(X15))))&(~r2_hidden(k3_subset_1(X15,X18),X16)|r2_hidden(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(X15))|X17!=k7_setfam_1(X15,X16)|~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X15)))|~m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(X15)))))&((m1_subset_1(esk1_3(X15,X16,X17),k1_zfmisc_1(X15))|X17=k7_setfam_1(X15,X16)|~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X15)))|~m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(X15))))&((~r2_hidden(esk1_3(X15,X16,X17),X17)|~r2_hidden(k3_subset_1(X15,esk1_3(X15,X16,X17)),X16)|X17=k7_setfam_1(X15,X16)|~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X15)))|~m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(X15))))&(r2_hidden(esk1_3(X15,X16,X17),X17)|r2_hidden(k3_subset_1(X15,esk1_3(X15,X16,X17)),X16)|X17=k7_setfam_1(X15,X16)|~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X15)))|~m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(X15))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_setfam_1])])])])])).
% 0.12/0.37  fof(c_0_29, plain, ![X26, X27, X28]:(~r2_hidden(X26,X27)|~m1_subset_1(X27,k1_zfmisc_1(X28))|m1_subset_1(X26,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.12/0.37  cnf(c_0_30, negated_conjecture, (k7_setfam_1(esk3_0,esk4_0)=k1_xboole_0|~m1_subset_1(k5_setfam_1(esk3_0,k7_setfam_1(esk3_0,esk4_0)),k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.12/0.37  cnf(c_0_31, plain, (m1_subset_1(k5_setfam_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.37  cnf(c_0_32, plain, (r2_hidden(k3_subset_1(X3,X1),X4)|~r2_hidden(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X3))|X2!=k7_setfam_1(X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.37  cnf(c_0_33, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.37  cnf(c_0_34, negated_conjecture, (k7_setfam_1(esk3_0,esk4_0)=k1_xboole_0|~m1_subset_1(k7_setfam_1(esk3_0,esk4_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0)))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.12/0.37  fof(c_0_35, plain, ![X10, X11]:((k4_xboole_0(X10,k1_tarski(X11))!=X10|~r2_hidden(X11,X10))&(r2_hidden(X11,X10)|k4_xboole_0(X10,k1_tarski(X11))=X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.12/0.37  fof(c_0_36, plain, ![X7, X8]:k4_xboole_0(X7,X8)=k5_xboole_0(X7,k3_xboole_0(X7,X8)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.12/0.37  cnf(c_0_37, plain, (r2_hidden(k3_subset_1(X1,X2),X3)|X4!=k7_setfam_1(X1,X3)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))|~r2_hidden(X2,X4)), inference(csr,[status(thm)],[c_0_32, c_0_33])).
% 0.12/0.37  cnf(c_0_38, negated_conjecture, (k7_setfam_1(esk3_0,esk4_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_20]), c_0_23])])).
% 0.12/0.37  fof(c_0_39, plain, ![X14]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X14)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.12/0.37  fof(c_0_40, plain, ![X9]:k4_xboole_0(k1_xboole_0,X9)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.12/0.37  cnf(c_0_41, plain, (k4_xboole_0(X1,k1_tarski(X2))!=X1|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.37  cnf(c_0_42, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.12/0.37  cnf(c_0_43, negated_conjecture, (r2_hidden(k3_subset_1(esk3_0,X1),X2)|k7_setfam_1(esk3_0,X2)!=esk4_0|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_37, c_0_23])).
% 0.12/0.37  cnf(c_0_44, negated_conjecture, (k7_setfam_1(esk3_0,k1_xboole_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_38]), c_0_23])])).
% 0.12/0.37  cnf(c_0_45, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.12/0.37  cnf(c_0_46, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.12/0.37  cnf(c_0_47, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_tarski(X2)))!=X1|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 0.12/0.37  cnf(c_0_48, negated_conjecture, (r2_hidden(k3_subset_1(esk3_0,X1),k1_xboole_0)|~r2_hidden(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])])).
% 0.12/0.37  cnf(c_0_49, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(rw,[status(thm)],[c_0_46, c_0_42])).
% 0.12/0.37  fof(c_0_50, plain, ![X29, X31, X32, X33, X34]:((r2_hidden(esk2_1(X29),X29)|X29=k1_xboole_0)&((~r2_hidden(X31,X29)|esk2_1(X29)!=k4_mcart_1(X31,X32,X33,X34)|X29=k1_xboole_0)&(~r2_hidden(X32,X29)|esk2_1(X29)!=k4_mcart_1(X31,X32,X33,X34)|X29=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_mcart_1])])])])])])).
% 0.12/0.37  cnf(c_0_51, negated_conjecture, (~r2_hidden(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])])).
% 0.12/0.37  cnf(c_0_52, plain, (r2_hidden(esk2_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.12/0.37  cnf(c_0_53, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  cnf(c_0_54, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 55
% 0.12/0.37  # Proof object clause steps            : 28
% 0.12/0.37  # Proof object formula steps           : 27
% 0.12/0.37  # Proof object conjectures             : 15
% 0.12/0.37  # Proof object clause conjectures      : 12
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 15
% 0.12/0.37  # Proof object initial formulas used   : 13
% 0.12/0.37  # Proof object generating inferences   : 10
% 0.12/0.37  # Proof object simplifying inferences  : 15
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 13
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 22
% 0.12/0.37  # Removed in clause preprocessing      : 1
% 0.12/0.37  # Initial clauses in saturation        : 21
% 0.12/0.37  # Processed clauses                    : 74
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 3
% 0.12/0.37  # ...remaining for further processing  : 71
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 4
% 0.12/0.37  # Generated clauses                    : 93
% 0.12/0.37  # ...of the previous two non-trivial   : 79
% 0.12/0.37  # Contextual simplify-reflections      : 2
% 0.12/0.37  # Paramodulations                      : 93
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 0
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 46
% 0.12/0.37  #    Positive orientable unit clauses  : 7
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 3
% 0.12/0.37  #    Non-unit-clauses                  : 36
% 0.12/0.37  # Current number of unprocessed clauses: 47
% 0.12/0.37  # ...number of literals in the above   : 209
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 26
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 328
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 125
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 5
% 0.12/0.37  # Unit Clause-clause subsumption calls : 21
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 1
% 0.12/0.37  # BW rewrite match successes           : 1
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 3805
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.028 s
% 0.12/0.37  # System time              : 0.007 s
% 0.12/0.37  # Total time               : 0.036 s
% 0.12/0.37  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
