%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0423+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:36 EST 2020

% Result     : Theorem 4.51s
% Output     : CNFRefutation 4.51s
% Verified   : 
% Statistics : Number of formulae       :  113 (1011 expanded)
%              Number of clauses        :   80 ( 473 expanded)
%              Number of leaves         :   16 ( 263 expanded)
%              Depth                    :   16
%              Number of atoms          :  296 (2704 expanded)
%              Number of equality atoms :   78 ( 795 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).

fof(dt_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(t55_setfam_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( X2 = k1_tarski(X1)
       => k7_setfam_1(X1,X2) = k1_tarski(k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_setfam_1)).

fof(t37_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t37_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(involutiveness_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k7_setfam_1(X1,k7_setfam_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(c_0_16,plain,(
    ! [X34,X35] :
      ( ( ~ m1_subset_1(X34,k1_zfmisc_1(X35))
        | r1_tarski(X34,X35) )
      & ( ~ r1_tarski(X34,X35)
        | m1_subset_1(X34,k1_zfmisc_1(X35)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_17,plain,(
    ! [X28] : r1_tarski(k1_xboole_0,X28) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_18,plain,(
    ! [X20] : m1_subset_1(k2_subset_1(X20),k1_zfmisc_1(X20)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_19,plain,(
    ! [X12] : k2_subset_1(X12) = X12 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_20,plain,(
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
      & ( m1_subset_1(esk2_3(X15,X16,X17),k1_zfmisc_1(X15))
        | X17 = k7_setfam_1(X15,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X15)))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(X15))) )
      & ( ~ r2_hidden(esk2_3(X15,X16,X17),X17)
        | ~ r2_hidden(k3_subset_1(X15,esk2_3(X15,X16,X17)),X16)
        | X17 = k7_setfam_1(X15,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X15)))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(X15))) )
      & ( r2_hidden(esk2_3(X15,X16,X17),X17)
        | r2_hidden(k3_subset_1(X15,esk2_3(X15,X16,X17)),X16)
        | X17 = k7_setfam_1(X15,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X15)))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(X15))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_setfam_1])])])])])).

fof(c_0_21,plain,(
    ! [X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(X21)))
      | m1_subset_1(k7_setfam_1(X21,X22),k1_zfmisc_1(k1_zfmisc_1(X21))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).

fof(c_0_22,plain,(
    ! [X33] : k4_xboole_0(X33,k1_xboole_0) = X33 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_23,plain,(
    ! [X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | k3_subset_1(X13,X14) = k4_xboole_0(X13,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ( X2 = k1_tarski(X1)
         => k7_setfam_1(X1,X2) = k1_tarski(k1_xboole_0) ) ) ),
    inference(assume_negation,[status(cth)],[t55_setfam_1])).

fof(c_0_27,plain,(
    ! [X29,X30] :
      ( ( k4_xboole_0(X29,X30) != k1_xboole_0
        | r1_tarski(X29,X30) )
      & ( ~ r1_tarski(X29,X30)
        | k4_xboole_0(X29,X30) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).

fof(c_0_28,plain,(
    ! [X36,X37,X38] :
      ( ~ r2_hidden(X36,X37)
      | ~ m1_subset_1(X37,k1_zfmisc_1(X38))
      | m1_subset_1(X36,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_29,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | X4 != k7_setfam_1(X1,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_36,plain,(
    ! [X31,X32] :
      ( ( ~ r1_tarski(k1_tarski(X31),X32)
        | r2_hidden(X31,X32) )
      & ( ~ r2_hidden(X31,X32)
        | r1_tarski(k1_tarski(X31),X32) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_zfmisc_1])])).

fof(c_0_37,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))
    & esk4_0 = k1_tarski(esk3_0)
    & k7_setfam_1(esk3_0,esk4_0) != k1_tarski(k1_xboole_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).

fof(c_0_38,plain,(
    ! [X5,X6,X7,X8,X9,X10] :
      ( ( ~ r2_hidden(X7,X6)
        | X7 = X5
        | X6 != k1_tarski(X5) )
      & ( X8 != X5
        | r2_hidden(X8,X6)
        | X6 != k1_tarski(X5) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | esk1_2(X9,X10) != X9
        | X10 = k1_tarski(X9) )
      & ( r2_hidden(esk1_2(X9,X10),X10)
        | esk1_2(X9,X10) = X9
        | X10 = k1_tarski(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k7_setfam_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(k3_subset_1(X2,X1),X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_31]),c_0_32])).

cnf(c_0_43,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

fof(c_0_44,plain,(
    ! [X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24)))
      | k7_setfam_1(X24,k7_setfam_1(X24,X25)) = X25 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( esk4_0 = k1_tarski(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,plain,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_39])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_51,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_52,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_53,plain,
    ( r2_hidden(k1_xboole_0,k7_setfam_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_35])])).

cnf(c_0_54,plain,
    ( k7_setfam_1(X2,k7_setfam_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk3_0,X1)
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | ~ r2_hidden(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_46])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_48])])).

cnf(c_0_58,plain,
    ( k1_xboole_0 = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_59,plain,
    ( esk1_2(X1,X2) = X1
    | X2 = k1_tarski(X1)
    | m1_subset_1(esk1_2(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

fof(c_0_60,plain,(
    ! [X26,X27] :
      ( ~ m1_subset_1(X26,X27)
      | v1_xboole_0(X27)
      | r2_hidden(X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_61,plain,(
    ! [X23] : ~ v1_xboole_0(k1_zfmisc_1(X23)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_62,plain,
    ( r2_hidden(k1_xboole_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ r2_hidden(X2,k7_setfam_1(X2,X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_32])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk3_0,X1)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_50])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(X1))
    | ~ r2_hidden(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_56])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,k7_setfam_1(X2,k1_tarski(k3_subset_1(X2,X1))))
    | ~ m1_subset_1(k1_tarski(k3_subset_1(X2,X1)),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_57])).

cnf(c_0_66,plain,
    ( esk1_2(X1,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | esk1_2(X1,k1_zfmisc_1(k1_xboole_0)) = X1
    | k1_tarski(X1) = k1_zfmisc_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_67,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_68,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(k1_xboole_0,X1)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k7_setfam_1(esk3_0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k7_setfam_1(X1,k1_tarski(k3_subset_1(X1,esk3_0)))))
    | ~ m1_subset_1(k1_tarski(k3_subset_1(X1,esk3_0)),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_71,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(k3_subset_1(X1,esk2_3(X1,X2,X3)),X2)
    | X3 = k7_setfam_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_72,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_47])).

cnf(c_0_73,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_74,plain,
    ( esk1_2(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_66])])).

cnf(c_0_75,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_35]),c_0_68])).

cnf(c_0_76,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k1_tarski(k3_subset_1(esk3_0,esk3_0)))
    | ~ m1_subset_1(k1_tarski(k3_subset_1(esk3_0,esk3_0)),k1_zfmisc_1(k1_zfmisc_1(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_41])])).

cnf(c_0_78,plain,
    ( r2_hidden(k3_subset_1(X3,X1),X4)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | X2 != k7_setfam_1(X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_79,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(X1))
    | X3 = k7_setfam_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_80,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_41]),c_0_68])).

cnf(c_0_81,plain,
    ( k1_tarski(X1) = k7_setfam_1(X2,X3)
    | r2_hidden(k3_subset_1(X2,esk2_3(X2,X3,k1_tarski(X1))),X3)
    | r2_hidden(esk2_3(X2,X3,k1_tarski(X1)),k1_tarski(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_83,negated_conjecture,
    ( k7_setfam_1(esk3_0,esk4_0) != k1_tarski(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_84,plain,
    ( k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75])])).

cnf(c_0_85,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_76])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k1_tarski(k3_subset_1(esk3_0,esk3_0)))
    | ~ r2_hidden(k3_subset_1(esk3_0,esk3_0),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_72])).

cnf(c_0_87,plain,
    ( r2_hidden(k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X2,k7_setfam_1(X1,X3)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_78,c_0_40])]),c_0_32])).

cnf(c_0_88,plain,
    ( k7_setfam_1(X1,X2) = k7_setfam_1(X1,X3)
    | m1_subset_1(esk2_3(X1,X3,k7_setfam_1(X1,X2)),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_79,c_0_32])).

cnf(c_0_89,plain,
    ( r2_hidden(X1,k7_setfam_1(X2,k1_zfmisc_1(k3_subset_1(X2,X1))))
    | ~ m1_subset_1(k1_zfmisc_1(k3_subset_1(X2,X1)),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_80])).

cnf(c_0_90,negated_conjecture,
    ( k1_tarski(X1) = k7_setfam_1(esk3_0,esk4_0)
    | r2_hidden(k3_subset_1(esk3_0,esk2_3(esk3_0,esk4_0,k1_tarski(X1))),esk4_0)
    | r2_hidden(esk2_3(esk3_0,esk4_0,k1_tarski(X1)),k1_tarski(X1))
    | ~ r2_hidden(X1,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_91,negated_conjecture,
    ( k7_setfam_1(esk3_0,esk4_0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_92,negated_conjecture,
    ( k3_subset_1(esk3_0,esk3_0) = k1_xboole_0
    | ~ r2_hidden(k3_subset_1(esk3_0,esk3_0),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_93,plain,
    ( r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(k1_xboole_0,k7_setfam_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_43])).

cnf(c_0_94,negated_conjecture,
    ( k7_setfam_1(esk3_0,X1) = k7_setfam_1(esk3_0,esk4_0)
    | m1_subset_1(esk2_3(esk3_0,esk4_0,k7_setfam_1(esk3_0,X1)),k1_zfmisc_1(esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_88,c_0_82])).

cnf(c_0_95,plain,
    ( r2_hidden(X1,k7_setfam_1(X2,k7_setfam_1(X3,k1_zfmisc_1(k3_subset_1(X3,k3_subset_1(X2,X1))))))
    | ~ m1_subset_1(k7_setfam_1(X3,k1_zfmisc_1(k3_subset_1(X3,k3_subset_1(X2,X1)))),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(k1_zfmisc_1(k3_subset_1(X3,k3_subset_1(X2,X1))),k1_zfmisc_1(k1_zfmisc_1(X3)))
    | ~ m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_89])).

cnf(c_0_96,negated_conjecture,
    ( X1 = esk3_0
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_46])).

cnf(c_0_97,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk3_0,esk2_3(esk3_0,esk4_0,k1_zfmisc_1(k1_xboole_0))),esk4_0)
    | r2_hidden(esk2_3(esk3_0,esk4_0,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_75]),c_0_84]),c_0_84]),c_0_84]),c_0_84]),c_0_91])).

cnf(c_0_98,negated_conjecture,
    ( k3_subset_1(esk3_0,esk3_0) = k1_xboole_0
    | ~ r2_hidden(esk3_0,k7_setfam_1(esk3_0,k1_zfmisc_1(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_87]),c_0_41])])).

cnf(c_0_99,plain,
    ( r2_hidden(X1,k7_setfam_1(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(k1_xboole_0,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_54]),c_0_32])).

cnf(c_0_100,negated_conjecture,
    ( X1 = k7_setfam_1(esk3_0,esk4_0)
    | m1_subset_1(esk2_3(esk3_0,esk4_0,X1),k1_zfmisc_1(esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk3_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_54]),c_0_32])).

cnf(c_0_101,plain,
    ( m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(X1))
    | ~ r2_hidden(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_84])).

cnf(c_0_102,plain,
    ( r2_hidden(X1,k1_zfmisc_1(k3_subset_1(X2,k3_subset_1(X2,X1))))
    | ~ m1_subset_1(k1_zfmisc_1(k3_subset_1(X2,k3_subset_1(X2,X1))),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_54]),c_0_32])).

cnf(c_0_103,negated_conjecture,
    ( k3_subset_1(esk3_0,esk2_3(esk3_0,esk4_0,k1_zfmisc_1(k1_xboole_0))) = esk3_0
    | r2_hidden(esk2_3(esk3_0,esk4_0,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_104,negated_conjecture,
    ( k3_subset_1(esk3_0,esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_41]),c_0_75])])).

cnf(c_0_105,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,esk4_0,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_75])]),c_0_91])).

cnf(c_0_106,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_84])).

cnf(c_0_107,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,esk4_0,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_104]),c_0_104]),c_0_41]),c_0_105])])).

cnf(c_0_108,plain,
    ( X3 = k7_setfam_1(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(k3_subset_1(X1,esk2_3(X1,X2,X3)),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_109,negated_conjecture,
    ( esk2_3(esk3_0,esk4_0,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_110,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_46])).

cnf(c_0_111,negated_conjecture,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_82]),c_0_43]),c_0_110]),c_0_75])]),c_0_91])).

cnf(c_0_112,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_101]),c_0_75])]),
    [proof]).

%------------------------------------------------------------------------------
