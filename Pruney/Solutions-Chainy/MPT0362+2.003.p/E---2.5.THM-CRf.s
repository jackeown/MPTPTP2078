%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:46:24 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 222 expanded)
%              Number of clauses        :   51 ( 105 expanded)
%              Number of leaves         :   11 (  56 expanded)
%              Depth                    :   17
%              Number of atoms          :  184 ( 644 expanded)
%              Number of equality atoms :   35 ( 122 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t42_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,k9_subset_1(X1,X2,X3))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_subset_1)).

fof(t83_zfmisc_1,axiom,(
    ! [X1,X2] : k1_zfmisc_1(k3_xboole_0(X1,X2)) = k3_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_zfmisc_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(t31_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,X3)
          <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(c_0_11,plain,(
    ! [X20,X21,X22,X23,X24,X25] :
      ( ( ~ r2_hidden(X22,X21)
        | r1_tarski(X22,X20)
        | X21 != k1_zfmisc_1(X20) )
      & ( ~ r1_tarski(X23,X20)
        | r2_hidden(X23,X21)
        | X21 != k1_zfmisc_1(X20) )
      & ( ~ r2_hidden(esk2_2(X24,X25),X25)
        | ~ r1_tarski(esk2_2(X24,X25),X24)
        | X25 = k1_zfmisc_1(X24) )
      & ( r2_hidden(esk2_2(X24,X25),X25)
        | r1_tarski(esk2_2(X24,X25),X24)
        | X25 = k1_zfmisc_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_13,plain,(
    ! [X16,X17] : r1_tarski(k3_xboole_0(X16,X17),X16) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_15,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_16,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_17,plain,(
    ! [X29,X30] :
      ( ( ~ m1_subset_1(X30,X29)
        | r2_hidden(X30,X29)
        | v1_xboole_0(X29) )
      & ( ~ r2_hidden(X30,X29)
        | m1_subset_1(X30,X29)
        | v1_xboole_0(X29) )
      & ( ~ m1_subset_1(X30,X29)
        | v1_xboole_0(X30)
        | ~ v1_xboole_0(X29) )
      & ( ~ v1_xboole_0(X30)
        | m1_subset_1(X30,X29)
        | ~ v1_xboole_0(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_18,plain,(
    ! [X31] : ~ v1_xboole_0(k1_zfmisc_1(X31)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_19,plain,(
    ! [X18,X19] :
      ( ~ r1_tarski(X18,X19)
      | k3_xboole_0(X18,X19) = X18 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,k9_subset_1(X1,X2,X3))) ) ) ),
    inference(assume_negation,[status(cth)],[t42_subset_1])).

cnf(c_0_22,plain,
    ( r2_hidden(k3_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_20])).

fof(c_0_28,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))
    & ~ r1_tarski(k3_subset_1(esk3_0,esk4_0),k3_subset_1(esk3_0,k9_subset_1(esk3_0,esk4_0,esk5_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

cnf(c_0_29,plain,
    ( r2_hidden(k3_xboole_0(X1,X2),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_30,plain,(
    ! [X27,X28] : k1_zfmisc_1(k3_xboole_0(X27,X28)) = k3_xboole_0(k1_zfmisc_1(X27),k1_zfmisc_1(X28)) ),
    inference(variable_rename,[status(thm)],[t83_zfmisc_1])).

fof(c_0_31,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( r2_hidden(X10,X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | ~ r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k3_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k3_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X13)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k3_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_32,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_22]),c_0_25])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X2)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_29]),c_0_25])).

cnf(c_0_37,plain,
    ( k1_zfmisc_1(k3_xboole_0(X1,X2)) = k3_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1))
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk5_0,k1_zfmisc_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_25])).

cnf(c_0_41,plain,
    ( m1_subset_1(k1_zfmisc_1(k3_xboole_0(X1,X2)),k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,plain,
    ( m1_subset_1(k1_zfmisc_1(X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_33])).

cnf(c_0_45,plain,
    ( m1_subset_1(X1,k3_xboole_0(X2,X3))
    | v1_xboole_0(k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk5_0,k1_zfmisc_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_43]),c_0_25])).

cnf(c_0_47,plain,
    ( k1_zfmisc_1(k3_xboole_0(X1,X2)) = k1_zfmisc_1(X1)
    | ~ r2_hidden(k1_zfmisc_1(X1),k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_33])).

cnf(c_0_48,plain,
    ( r2_hidden(k1_zfmisc_1(X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_44]),c_0_25])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk5_0,k3_xboole_0(X1,k1_zfmisc_1(esk5_0)))
    | v1_xboole_0(k3_xboole_0(X1,k1_zfmisc_1(esk5_0)))
    | ~ r2_hidden(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_51,plain,
    ( k1_zfmisc_1(k3_xboole_0(X1,X2)) = k1_zfmisc_1(X1)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r2_hidden(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_33])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k3_xboole_0(esk3_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_40]),c_0_37]),c_0_37]),c_0_25])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_55,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(X2)
    | ~ r2_hidden(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk5_0,k1_zfmisc_1(k3_xboole_0(esk3_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_53]),c_0_25])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,k1_zfmisc_1(k3_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_37])).

cnf(c_0_58,negated_conjecture,
    ( k1_zfmisc_1(k3_xboole_0(esk3_0,esk5_0)) = k1_zfmisc_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_29])])).

fof(c_0_59,plain,(
    ! [X32,X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(X32))
      | k9_subset_1(X32,X33,X34) = k3_xboole_0(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(X1,k1_zfmisc_1(esk3_0))
    | ~ r2_hidden(X1,k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk3_0,esk4_0),k3_subset_1(esk3_0,k9_subset_1(esk3_0,esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_62,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

fof(c_0_63,plain,(
    ! [X35,X36,X37] :
      ( ( ~ r1_tarski(X36,X37)
        | r1_tarski(k3_subset_1(X35,X37),k3_subset_1(X35,X36))
        | ~ m1_subset_1(X37,k1_zfmisc_1(X35))
        | ~ m1_subset_1(X36,k1_zfmisc_1(X35)) )
      & ( ~ r1_tarski(k3_subset_1(X35,X37),k3_subset_1(X35,X36))
        | r1_tarski(X36,X37)
        | ~ m1_subset_1(X37,k1_zfmisc_1(X35))
        | ~ m1_subset_1(X36,k1_zfmisc_1(X35)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_subset_1])])])])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(k3_xboole_0(esk5_0,X1),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_22])).

cnf(c_0_65,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_23])).

cnf(c_0_66,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk3_0,esk4_0),k3_subset_1(esk3_0,k3_xboole_0(esk4_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_35])])).

cnf(c_0_67,plain,
    ( r1_tarski(k3_subset_1(X3,X2),k3_subset_1(X3,X1))
    | ~ r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(k3_xboole_0(esk5_0,X1),k1_zfmisc_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_64]),c_0_25])).

cnf(c_0_70,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_65]),c_0_23])).

cnf(c_0_71,negated_conjecture,
    ( ~ m1_subset_1(k3_xboole_0(esk4_0,esk5_0),k1_zfmisc_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_15])])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(k3_xboole_0(X1,esk5_0),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_72])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:46:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.43  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.43  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.43  #
% 0.20/0.43  # Preprocessing time       : 0.028 s
% 0.20/0.43  # Presaturation interreduction done
% 0.20/0.43  
% 0.20/0.43  # Proof found!
% 0.20/0.43  # SZS status Theorem
% 0.20/0.43  # SZS output start CNFRefutation
% 0.20/0.43  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.20/0.43  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.20/0.43  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.43  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.20/0.43  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.20/0.43  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.20/0.43  fof(t42_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,k9_subset_1(X1,X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_subset_1)).
% 0.20/0.43  fof(t83_zfmisc_1, axiom, ![X1, X2]:k1_zfmisc_1(k3_xboole_0(X1,X2))=k3_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_zfmisc_1)).
% 0.20/0.43  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.20/0.43  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.20/0.43  fof(t31_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 0.20/0.43  fof(c_0_11, plain, ![X20, X21, X22, X23, X24, X25]:(((~r2_hidden(X22,X21)|r1_tarski(X22,X20)|X21!=k1_zfmisc_1(X20))&(~r1_tarski(X23,X20)|r2_hidden(X23,X21)|X21!=k1_zfmisc_1(X20)))&((~r2_hidden(esk2_2(X24,X25),X25)|~r1_tarski(esk2_2(X24,X25),X24)|X25=k1_zfmisc_1(X24))&(r2_hidden(esk2_2(X24,X25),X25)|r1_tarski(esk2_2(X24,X25),X24)|X25=k1_zfmisc_1(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.20/0.43  cnf(c_0_12, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  fof(c_0_13, plain, ![X16, X17]:r1_tarski(k3_xboole_0(X16,X17),X16), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.20/0.43  cnf(c_0_14, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_12])).
% 0.20/0.43  cnf(c_0_15, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.43  fof(c_0_16, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.43  fof(c_0_17, plain, ![X29, X30]:(((~m1_subset_1(X30,X29)|r2_hidden(X30,X29)|v1_xboole_0(X29))&(~r2_hidden(X30,X29)|m1_subset_1(X30,X29)|v1_xboole_0(X29)))&((~m1_subset_1(X30,X29)|v1_xboole_0(X30)|~v1_xboole_0(X29))&(~v1_xboole_0(X30)|m1_subset_1(X30,X29)|~v1_xboole_0(X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.20/0.43  fof(c_0_18, plain, ![X31]:~v1_xboole_0(k1_zfmisc_1(X31)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.20/0.43  fof(c_0_19, plain, ![X18, X19]:(~r1_tarski(X18,X19)|k3_xboole_0(X18,X19)=X18), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.20/0.43  cnf(c_0_20, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.43  fof(c_0_21, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,k9_subset_1(X1,X2,X3)))))), inference(assume_negation,[status(cth)],[t42_subset_1])).
% 0.20/0.43  cnf(c_0_22, plain, (r2_hidden(k3_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.43  cnf(c_0_23, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.43  cnf(c_0_24, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.43  cnf(c_0_25, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.43  cnf(c_0_26, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.43  cnf(c_0_27, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_20])).
% 0.20/0.43  fof(c_0_28, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))&~r1_tarski(k3_subset_1(esk3_0,esk4_0),k3_subset_1(esk3_0,k9_subset_1(esk3_0,esk4_0,esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.20/0.43  cnf(c_0_29, plain, (r2_hidden(k3_xboole_0(X1,X2),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.43  fof(c_0_30, plain, ![X27, X28]:k1_zfmisc_1(k3_xboole_0(X27,X28))=k3_xboole_0(k1_zfmisc_1(X27),k1_zfmisc_1(X28)), inference(variable_rename,[status(thm)],[t83_zfmisc_1])).
% 0.20/0.43  fof(c_0_31, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k3_xboole_0(X7,X8))&(r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k3_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|~r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k3_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|~r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k3_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k3_xboole_0(X12,X13))&(r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k3_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.20/0.43  cnf(c_0_32, plain, (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_22]), c_0_25])).
% 0.20/0.43  cnf(c_0_33, plain, (k3_xboole_0(X1,X2)=X1|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.43  cnf(c_0_34, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.43  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.43  cnf(c_0_36, plain, (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X2))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_29]), c_0_25])).
% 0.20/0.43  cnf(c_0_37, plain, (k1_zfmisc_1(k3_xboole_0(X1,X2))=k3_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.43  cnf(c_0_38, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.43  cnf(c_0_39, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.43  cnf(c_0_40, negated_conjecture, (r2_hidden(esk5_0,k1_zfmisc_1(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_25])).
% 0.20/0.43  cnf(c_0_41, plain, (m1_subset_1(k1_zfmisc_1(k3_xboole_0(X1,X2)),k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.43  cnf(c_0_42, plain, (r2_hidden(X1,k3_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_38])).
% 0.20/0.43  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.43  cnf(c_0_44, plain, (m1_subset_1(k1_zfmisc_1(X1),k1_zfmisc_1(k1_zfmisc_1(X2)))|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_41, c_0_33])).
% 0.20/0.43  cnf(c_0_45, plain, (m1_subset_1(X1,k3_xboole_0(X2,X3))|v1_xboole_0(k3_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_24, c_0_42])).
% 0.20/0.43  cnf(c_0_46, negated_conjecture, (r2_hidden(esk5_0,k1_zfmisc_1(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_43]), c_0_25])).
% 0.20/0.43  cnf(c_0_47, plain, (k1_zfmisc_1(k3_xboole_0(X1,X2))=k1_zfmisc_1(X1)|~r2_hidden(k1_zfmisc_1(X1),k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(spm,[status(thm)],[c_0_37, c_0_33])).
% 0.20/0.43  cnf(c_0_48, plain, (r2_hidden(k1_zfmisc_1(X1),k1_zfmisc_1(k1_zfmisc_1(X2)))|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_44]), c_0_25])).
% 0.20/0.43  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk5_0,k3_xboole_0(X1,k1_zfmisc_1(esk5_0)))|v1_xboole_0(k3_xboole_0(X1,k1_zfmisc_1(esk5_0)))|~r2_hidden(esk5_0,X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.43  cnf(c_0_50, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.43  cnf(c_0_51, plain, (k1_zfmisc_1(k3_xboole_0(X1,X2))=k1_zfmisc_1(X1)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.43  cnf(c_0_52, plain, (k3_xboole_0(X1,X2)=X2|~r2_hidden(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_23, c_0_33])).
% 0.20/0.43  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k3_xboole_0(esk3_0,esk5_0)))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_40]), c_0_37]), c_0_37]), c_0_25])).
% 0.20/0.43  cnf(c_0_54, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_50])).
% 0.20/0.43  cnf(c_0_55, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(X2)|~r2_hidden(X2,k1_zfmisc_1(X1))|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.20/0.43  cnf(c_0_56, negated_conjecture, (r2_hidden(esk5_0,k1_zfmisc_1(k3_xboole_0(esk3_0,esk5_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_53]), c_0_25])).
% 0.20/0.43  cnf(c_0_57, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r2_hidden(X1,k1_zfmisc_1(k3_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_54, c_0_37])).
% 0.20/0.43  cnf(c_0_58, negated_conjecture, (k1_zfmisc_1(k3_xboole_0(esk3_0,esk5_0))=k1_zfmisc_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_29])])).
% 0.20/0.43  fof(c_0_59, plain, ![X32, X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(X32))|k9_subset_1(X32,X33,X34)=k3_xboole_0(X33,X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.20/0.43  cnf(c_0_60, negated_conjecture, (r2_hidden(X1,k1_zfmisc_1(esk3_0))|~r2_hidden(X1,k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.20/0.43  cnf(c_0_61, negated_conjecture, (~r1_tarski(k3_subset_1(esk3_0,esk4_0),k3_subset_1(esk3_0,k9_subset_1(esk3_0,esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.43  cnf(c_0_62, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.43  fof(c_0_63, plain, ![X35, X36, X37]:((~r1_tarski(X36,X37)|r1_tarski(k3_subset_1(X35,X37),k3_subset_1(X35,X36))|~m1_subset_1(X37,k1_zfmisc_1(X35))|~m1_subset_1(X36,k1_zfmisc_1(X35)))&(~r1_tarski(k3_subset_1(X35,X37),k3_subset_1(X35,X36))|r1_tarski(X36,X37)|~m1_subset_1(X37,k1_zfmisc_1(X35))|~m1_subset_1(X36,k1_zfmisc_1(X35)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_subset_1])])])])).
% 0.20/0.43  cnf(c_0_64, negated_conjecture, (r2_hidden(k3_xboole_0(esk5_0,X1),k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_60, c_0_22])).
% 0.20/0.43  cnf(c_0_65, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_15, c_0_23])).
% 0.20/0.43  cnf(c_0_66, negated_conjecture, (~r1_tarski(k3_subset_1(esk3_0,esk4_0),k3_subset_1(esk3_0,k3_xboole_0(esk4_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_35])])).
% 0.20/0.43  cnf(c_0_67, plain, (r1_tarski(k3_subset_1(X3,X2),k3_subset_1(X3,X1))|~r1_tarski(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.20/0.43  cnf(c_0_68, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.43  cnf(c_0_69, negated_conjecture, (m1_subset_1(k3_xboole_0(esk5_0,X1),k1_zfmisc_1(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_64]), c_0_25])).
% 0.20/0.43  cnf(c_0_70, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_65]), c_0_23])).
% 0.20/0.43  cnf(c_0_71, negated_conjecture, (~m1_subset_1(k3_xboole_0(esk4_0,esk5_0),k1_zfmisc_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68]), c_0_15])])).
% 0.20/0.43  cnf(c_0_72, negated_conjecture, (m1_subset_1(k3_xboole_0(X1,esk5_0),k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.20/0.43  cnf(c_0_73, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_72])]), ['proof']).
% 0.20/0.43  # SZS output end CNFRefutation
% 0.20/0.43  # Proof object total steps             : 74
% 0.20/0.43  # Proof object clause steps            : 51
% 0.20/0.43  # Proof object formula steps           : 23
% 0.20/0.43  # Proof object conjectures             : 20
% 0.20/0.43  # Proof object clause conjectures      : 17
% 0.20/0.43  # Proof object formula conjectures     : 3
% 0.20/0.43  # Proof object initial clauses used    : 16
% 0.20/0.43  # Proof object initial formulas used   : 11
% 0.20/0.43  # Proof object generating inferences   : 30
% 0.20/0.43  # Proof object simplifying inferences  : 24
% 0.20/0.43  # Training examples: 0 positive, 0 negative
% 0.20/0.43  # Parsed axioms                        : 11
% 0.20/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.43  # Initial clauses                      : 25
% 0.20/0.43  # Removed in clause preprocessing      : 0
% 0.20/0.43  # Initial clauses in saturation        : 25
% 0.20/0.43  # Processed clauses                    : 821
% 0.20/0.43  # ...of these trivial                  : 135
% 0.20/0.43  # ...subsumed                          : 337
% 0.20/0.43  # ...remaining for further processing  : 349
% 0.20/0.43  # Other redundant clauses eliminated   : 5
% 0.20/0.43  # Clauses deleted for lack of memory   : 0
% 0.20/0.43  # Backward-subsumed                    : 0
% 0.20/0.43  # Backward-rewritten                   : 10
% 0.20/0.43  # Generated clauses                    : 4352
% 0.20/0.43  # ...of the previous two non-trivial   : 2953
% 0.20/0.43  # Contextual simplify-reflections      : 0
% 0.20/0.43  # Paramodulations                      : 4327
% 0.20/0.43  # Factorizations                       : 20
% 0.20/0.43  # Equation resolutions                 : 5
% 0.20/0.43  # Propositional unsat checks           : 0
% 0.20/0.43  #    Propositional check models        : 0
% 0.20/0.43  #    Propositional check unsatisfiable : 0
% 0.20/0.43  #    Propositional clauses             : 0
% 0.20/0.43  #    Propositional clauses after purity: 0
% 0.20/0.43  #    Propositional unsat core size     : 0
% 0.20/0.43  #    Propositional preprocessing time  : 0.000
% 0.20/0.43  #    Propositional encoding time       : 0.000
% 0.20/0.43  #    Propositional solver time         : 0.000
% 0.20/0.43  #    Success case prop preproc time    : 0.000
% 0.20/0.43  #    Success case prop encoding time   : 0.000
% 0.20/0.43  #    Success case prop solver time     : 0.000
% 0.20/0.43  # Current number of processed clauses  : 309
% 0.20/0.43  #    Positive orientable unit clauses  : 159
% 0.20/0.43  #    Positive unorientable unit clauses: 1
% 0.20/0.43  #    Negative unit clauses             : 14
% 0.20/0.43  #    Non-unit-clauses                  : 135
% 0.20/0.43  # Current number of unprocessed clauses: 2182
% 0.20/0.43  # ...number of literals in the above   : 6189
% 0.20/0.43  # Current number of archived formulas  : 0
% 0.20/0.43  # Current number of archived clauses   : 35
% 0.20/0.43  # Clause-clause subsumption calls (NU) : 3695
% 0.20/0.43  # Rec. Clause-clause subsumption calls : 3341
% 0.20/0.43  # Non-unit clause-clause subsumptions  : 198
% 0.20/0.43  # Unit Clause-clause subsumption calls : 527
% 0.20/0.43  # Rewrite failures with RHS unbound    : 0
% 0.20/0.43  # BW rewrite match attempts            : 1757
% 0.20/0.43  # BW rewrite match successes           : 14
% 0.20/0.43  # Condensation attempts                : 0
% 0.20/0.43  # Condensation successes               : 0
% 0.20/0.43  # Termbank termtop insertions          : 67873
% 0.20/0.43  
% 0.20/0.43  # -------------------------------------------------
% 0.20/0.43  # User time                : 0.089 s
% 0.20/0.43  # System time              : 0.007 s
% 0.20/0.43  # Total time               : 0.096 s
% 0.20/0.43  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
