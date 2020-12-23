%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:46:10 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 318 expanded)
%              Number of clauses        :   44 ( 145 expanded)
%              Number of leaves         :   14 (  82 expanded)
%              Depth                    :   16
%              Number of atoms          :  143 ( 690 expanded)
%              Number of equality atoms :   43 ( 208 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k6_subset_1,axiom,(
    ! [X1,X2] : m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t40_subset_1,conjecture,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => ( ( r1_tarski(X2,X3)
          & r1_tarski(X2,k3_subset_1(X1,X3)) )
       => X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t35_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,k3_subset_1(X1,X3))
           => r1_tarski(X3,k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

fof(t38_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( r1_tarski(X2,k3_subset_1(X1,X2))
      <=> X2 = k1_subset_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(c_0_14,plain,(
    ! [X25,X26] : m1_subset_1(k6_subset_1(X25,X26),k1_zfmisc_1(X25)) ),
    inference(variable_rename,[status(thm)],[dt_k6_subset_1])).

fof(c_0_15,plain,(
    ! [X28,X29] : k6_subset_1(X28,X29) = k4_xboole_0(X28,X29) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_16,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k5_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_17,plain,(
    ! [X13,X14] : k4_xboole_0(X13,k4_xboole_0(X13,X14)) = k3_xboole_0(X13,X14) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_18,plain,
    ( m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X15,X16,X17,X18,X19,X20] :
      ( ( ~ r2_hidden(X17,X16)
        | r1_tarski(X17,X15)
        | X16 != k1_zfmisc_1(X15) )
      & ( ~ r1_tarski(X18,X15)
        | r2_hidden(X18,X16)
        | X16 != k1_zfmisc_1(X15) )
      & ( ~ r2_hidden(esk1_2(X19,X20),X20)
        | ~ r1_tarski(esk1_2(X19,X20),X19)
        | X20 = k1_zfmisc_1(X19) )
      & ( r2_hidden(esk1_2(X19,X20),X20)
        | r1_tarski(esk1_2(X19,X20),X19)
        | X20 = k1_zfmisc_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_23,plain,(
    ! [X22,X23] :
      ( ( ~ m1_subset_1(X23,X22)
        | r2_hidden(X23,X22)
        | v1_xboole_0(X22) )
      & ( ~ r2_hidden(X23,X22)
        | m1_subset_1(X23,X22)
        | v1_xboole_0(X22) )
      & ( ~ m1_subset_1(X23,X22)
        | v1_xboole_0(X23)
        | ~ v1_xboole_0(X22) )
      & ( ~ v1_xboole_0(X23)
        | m1_subset_1(X23,X22)
        | ~ v1_xboole_0(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_24,plain,
    ( m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_25,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_20]),c_0_20])).

fof(c_0_26,plain,(
    ! [X27] : ~ v1_xboole_0(k1_zfmisc_1(X27)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(X1))
       => ( ( r1_tarski(X2,X3)
            & r1_tarski(X2,k3_subset_1(X1,X3)) )
         => X2 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t40_subset_1])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_32,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
    & r1_tarski(esk3_0,esk4_0)
    & r1_tarski(esk3_0,k3_subset_1(esk2_0,esk4_0))
    & esk3_0 != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( r2_hidden(k3_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

fof(c_0_35,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_39,plain,(
    ! [X8,X9,X10] : k3_xboole_0(k3_xboole_0(X8,X9),X10) = k3_xboole_0(X8,k3_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

fof(c_0_40,plain,(
    ! [X11,X12] :
      ( ~ r1_tarski(X11,X12)
      | k3_xboole_0(X11,X12) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_36]),c_0_31])).

cnf(c_0_42,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_41])).

cnf(c_0_46,plain,
    ( r1_tarski(k3_xboole_0(X1,k3_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk2_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk4_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_48])).

fof(c_0_51,plain,(
    ! [X30,X31,X32] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(X30))
      | ~ m1_subset_1(X32,k1_zfmisc_1(X30))
      | ~ r1_tarski(X31,k3_subset_1(X30,X32))
      | r1_tarski(X32,k3_subset_1(X30,X31)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_subset_1])])])).

cnf(c_0_52,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_53,plain,
    ( r2_hidden(k3_xboole_0(X1,X2),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_38])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,plain,
    ( r1_tarski(X3,k3_subset_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k3_subset_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_56,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X2)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_31])).

cnf(c_0_57,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk2_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(esk4_0,k3_subset_1(esk2_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0))
    | ~ r1_tarski(X1,k3_subset_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_36])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(esk3_0,k3_subset_1(esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_61,plain,(
    ! [X33,X34] :
      ( ( ~ r1_tarski(X34,k3_subset_1(X33,X34))
        | X34 = k1_subset_1(X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(X33)) )
      & ( X34 != k1_subset_1(X33)
        | r1_tarski(X34,k3_subset_1(X33,X34))
        | ~ m1_subset_1(X34,k1_zfmisc_1(X33)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_subset_1])])])).

fof(c_0_62,plain,(
    ! [X24] : k1_subset_1(X24) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(esk4_0,k3_subset_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])])).

cnf(c_0_64,plain,
    ( X1 = k1_subset_1(X2)
    | ~ r1_tarski(X1,k3_subset_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_65,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( k3_xboole_0(esk3_0,k3_xboole_0(esk4_0,X1)) = k3_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_50])).

cnf(c_0_67,negated_conjecture,
    ( k3_xboole_0(esk4_0,k3_subset_1(esk2_0,esk3_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_63])).

cnf(c_0_68,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k3_subset_1(X2,X1)) ),
    inference(rw,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_70,negated_conjecture,
    ( k3_xboole_0(esk3_0,k3_subset_1(esk2_0,esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_50])).

cnf(c_0_71,negated_conjecture,
    ( ~ r1_tarski(esk3_0,k3_subset_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_59]),c_0_69])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_70]),c_0_71]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:20:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S04DN
% 0.21/0.38  # and selection function SelectNewComplex.
% 0.21/0.38  #
% 0.21/0.38  # Preprocessing time       : 0.027 s
% 0.21/0.38  # Presaturation interreduction done
% 0.21/0.38  
% 0.21/0.38  # Proof found!
% 0.21/0.38  # SZS status Theorem
% 0.21/0.38  # SZS output start CNFRefutation
% 0.21/0.38  fof(dt_k6_subset_1, axiom, ![X1, X2]:m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 0.21/0.38  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.21/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.21/0.38  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.21/0.38  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.21/0.38  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.21/0.38  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.21/0.38  fof(t40_subset_1, conjecture, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>((r1_tarski(X2,X3)&r1_tarski(X2,k3_subset_1(X1,X3)))=>X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 0.21/0.38  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.21/0.38  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 0.21/0.38  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.21/0.38  fof(t35_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X3))=>r1_tarski(X3,k3_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_subset_1)).
% 0.21/0.38  fof(t38_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X2))<=>X2=k1_subset_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 0.21/0.38  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 0.21/0.38  fof(c_0_14, plain, ![X25, X26]:m1_subset_1(k6_subset_1(X25,X26),k1_zfmisc_1(X25)), inference(variable_rename,[status(thm)],[dt_k6_subset_1])).
% 0.21/0.38  fof(c_0_15, plain, ![X28, X29]:k6_subset_1(X28,X29)=k4_xboole_0(X28,X29), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.21/0.38  fof(c_0_16, plain, ![X6, X7]:k4_xboole_0(X6,X7)=k5_xboole_0(X6,k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.21/0.38  fof(c_0_17, plain, ![X13, X14]:k4_xboole_0(X13,k4_xboole_0(X13,X14))=k3_xboole_0(X13,X14), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.21/0.38  cnf(c_0_18, plain, (m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.38  cnf(c_0_19, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.38  cnf(c_0_20, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.38  cnf(c_0_21, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.38  fof(c_0_22, plain, ![X15, X16, X17, X18, X19, X20]:(((~r2_hidden(X17,X16)|r1_tarski(X17,X15)|X16!=k1_zfmisc_1(X15))&(~r1_tarski(X18,X15)|r2_hidden(X18,X16)|X16!=k1_zfmisc_1(X15)))&((~r2_hidden(esk1_2(X19,X20),X20)|~r1_tarski(esk1_2(X19,X20),X19)|X20=k1_zfmisc_1(X19))&(r2_hidden(esk1_2(X19,X20),X20)|r1_tarski(esk1_2(X19,X20),X19)|X20=k1_zfmisc_1(X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.21/0.38  fof(c_0_23, plain, ![X22, X23]:(((~m1_subset_1(X23,X22)|r2_hidden(X23,X22)|v1_xboole_0(X22))&(~r2_hidden(X23,X22)|m1_subset_1(X23,X22)|v1_xboole_0(X22)))&((~m1_subset_1(X23,X22)|v1_xboole_0(X23)|~v1_xboole_0(X22))&(~v1_xboole_0(X23)|m1_subset_1(X23,X22)|~v1_xboole_0(X22)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.21/0.38  cnf(c_0_24, plain, (m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 0.21/0.38  cnf(c_0_25, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_20]), c_0_20])).
% 0.21/0.38  fof(c_0_26, plain, ![X27]:~v1_xboole_0(k1_zfmisc_1(X27)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.21/0.38  fof(c_0_27, negated_conjecture, ~(![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>((r1_tarski(X2,X3)&r1_tarski(X2,k3_subset_1(X1,X3)))=>X2=k1_xboole_0))), inference(assume_negation,[status(cth)],[t40_subset_1])).
% 0.21/0.38  cnf(c_0_28, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.38  cnf(c_0_29, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.38  cnf(c_0_30, plain, (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.21/0.38  cnf(c_0_31, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.38  fof(c_0_32, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))&((r1_tarski(esk3_0,esk4_0)&r1_tarski(esk3_0,k3_subset_1(esk2_0,esk4_0)))&esk3_0!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).
% 0.21/0.38  cnf(c_0_33, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_28])).
% 0.21/0.38  cnf(c_0_34, plain, (r2_hidden(k3_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 0.21/0.38  fof(c_0_35, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.21/0.38  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.38  cnf(c_0_37, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.21/0.38  cnf(c_0_38, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.38  fof(c_0_39, plain, ![X8, X9, X10]:k3_xboole_0(k3_xboole_0(X8,X9),X10)=k3_xboole_0(X8,k3_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 0.21/0.38  fof(c_0_40, plain, ![X11, X12]:(~r1_tarski(X11,X12)|k3_xboole_0(X11,X12)=X11), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.21/0.38  cnf(c_0_41, negated_conjecture, (r2_hidden(esk4_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_36]), c_0_31])).
% 0.21/0.38  cnf(c_0_42, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.21/0.38  cnf(c_0_43, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.21/0.38  cnf(c_0_44, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.38  cnf(c_0_45, negated_conjecture, (r1_tarski(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_33, c_0_41])).
% 0.21/0.38  cnf(c_0_46, plain, (r1_tarski(k3_xboole_0(X1,k3_xboole_0(X2,X3)),X3)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.21/0.38  cnf(c_0_47, negated_conjecture, (k3_xboole_0(esk4_0,esk2_0)=esk4_0), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.21/0.38  cnf(c_0_48, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.38  cnf(c_0_49, negated_conjecture, (r1_tarski(k3_xboole_0(X1,esk4_0),esk2_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.21/0.38  cnf(c_0_50, negated_conjecture, (k3_xboole_0(esk3_0,esk4_0)=esk3_0), inference(spm,[status(thm)],[c_0_44, c_0_48])).
% 0.21/0.38  fof(c_0_51, plain, ![X30, X31, X32]:(~m1_subset_1(X31,k1_zfmisc_1(X30))|(~m1_subset_1(X32,k1_zfmisc_1(X30))|(~r1_tarski(X31,k3_subset_1(X30,X32))|r1_tarski(X32,k3_subset_1(X30,X31))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_subset_1])])])).
% 0.21/0.38  cnf(c_0_52, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.38  cnf(c_0_53, plain, (r2_hidden(k3_xboole_0(X1,X2),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_34, c_0_38])).
% 0.21/0.38  cnf(c_0_54, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.21/0.38  cnf(c_0_55, plain, (r1_tarski(X3,k3_subset_1(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,k3_subset_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.21/0.38  cnf(c_0_56, plain, (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X2))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_31])).
% 0.21/0.38  cnf(c_0_57, negated_conjecture, (k3_xboole_0(esk3_0,esk2_0)=esk3_0), inference(spm,[status(thm)],[c_0_44, c_0_54])).
% 0.21/0.38  cnf(c_0_58, negated_conjecture, (r1_tarski(esk4_0,k3_subset_1(esk2_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))|~r1_tarski(X1,k3_subset_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_55, c_0_36])).
% 0.21/0.38  cnf(c_0_59, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.21/0.38  cnf(c_0_60, negated_conjecture, (r1_tarski(esk3_0,k3_subset_1(esk2_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.38  fof(c_0_61, plain, ![X33, X34]:((~r1_tarski(X34,k3_subset_1(X33,X34))|X34=k1_subset_1(X33)|~m1_subset_1(X34,k1_zfmisc_1(X33)))&(X34!=k1_subset_1(X33)|r1_tarski(X34,k3_subset_1(X33,X34))|~m1_subset_1(X34,k1_zfmisc_1(X33)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_subset_1])])])).
% 0.21/0.38  fof(c_0_62, plain, ![X24]:k1_subset_1(X24)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.21/0.38  cnf(c_0_63, negated_conjecture, (r1_tarski(esk4_0,k3_subset_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])])).
% 0.21/0.38  cnf(c_0_64, plain, (X1=k1_subset_1(X2)|~r1_tarski(X1,k3_subset_1(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.21/0.38  cnf(c_0_65, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.21/0.38  cnf(c_0_66, negated_conjecture, (k3_xboole_0(esk3_0,k3_xboole_0(esk4_0,X1))=k3_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_43, c_0_50])).
% 0.21/0.38  cnf(c_0_67, negated_conjecture, (k3_xboole_0(esk4_0,k3_subset_1(esk2_0,esk3_0))=esk4_0), inference(spm,[status(thm)],[c_0_44, c_0_63])).
% 0.21/0.38  cnf(c_0_68, plain, (X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,k3_subset_1(X2,X1))), inference(rw,[status(thm)],[c_0_64, c_0_65])).
% 0.21/0.38  cnf(c_0_69, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.38  cnf(c_0_70, negated_conjecture, (k3_xboole_0(esk3_0,k3_subset_1(esk2_0,esk3_0))=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_50])).
% 0.21/0.38  cnf(c_0_71, negated_conjecture, (~r1_tarski(esk3_0,k3_subset_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_59]), c_0_69])).
% 0.21/0.38  cnf(c_0_72, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_70]), c_0_71]), ['proof']).
% 0.21/0.38  # SZS output end CNFRefutation
% 0.21/0.38  # Proof object total steps             : 73
% 0.21/0.38  # Proof object clause steps            : 44
% 0.21/0.38  # Proof object formula steps           : 29
% 0.21/0.38  # Proof object conjectures             : 22
% 0.21/0.38  # Proof object clause conjectures      : 19
% 0.21/0.38  # Proof object formula conjectures     : 3
% 0.21/0.38  # Proof object initial clauses used    : 18
% 0.21/0.38  # Proof object initial formulas used   : 14
% 0.21/0.38  # Proof object generating inferences   : 22
% 0.21/0.38  # Proof object simplifying inferences  : 14
% 0.21/0.38  # Training examples: 0 positive, 0 negative
% 0.21/0.38  # Parsed axioms                        : 14
% 0.21/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.38  # Initial clauses                      : 24
% 0.21/0.38  # Removed in clause preprocessing      : 3
% 0.21/0.38  # Initial clauses in saturation        : 21
% 0.21/0.38  # Processed clauses                    : 159
% 0.21/0.38  # ...of these trivial                  : 16
% 0.21/0.38  # ...subsumed                          : 20
% 0.21/0.38  # ...remaining for further processing  : 123
% 0.21/0.38  # Other redundant clauses eliminated   : 3
% 0.21/0.38  # Clauses deleted for lack of memory   : 0
% 0.21/0.38  # Backward-subsumed                    : 0
% 0.21/0.38  # Backward-rewritten                   : 2
% 0.21/0.38  # Generated clauses                    : 521
% 0.21/0.38  # ...of the previous two non-trivial   : 321
% 0.21/0.38  # Contextual simplify-reflections      : 0
% 0.21/0.38  # Paramodulations                      : 518
% 0.21/0.38  # Factorizations                       : 0
% 0.21/0.38  # Equation resolutions                 : 3
% 0.21/0.38  # Propositional unsat checks           : 0
% 0.21/0.38  #    Propositional check models        : 0
% 0.21/0.38  #    Propositional check unsatisfiable : 0
% 0.21/0.38  #    Propositional clauses             : 0
% 0.21/0.38  #    Propositional clauses after purity: 0
% 0.21/0.38  #    Propositional unsat core size     : 0
% 0.21/0.38  #    Propositional preprocessing time  : 0.000
% 0.21/0.38  #    Propositional encoding time       : 0.000
% 0.21/0.38  #    Propositional solver time         : 0.000
% 0.21/0.38  #    Success case prop preproc time    : 0.000
% 0.21/0.38  #    Success case prop encoding time   : 0.000
% 0.21/0.38  #    Success case prop solver time     : 0.000
% 0.21/0.38  # Current number of processed clauses  : 97
% 0.21/0.38  #    Positive orientable unit clauses  : 63
% 0.21/0.38  #    Positive unorientable unit clauses: 1
% 0.21/0.38  #    Negative unit clauses             : 6
% 0.21/0.39  #    Non-unit-clauses                  : 27
% 0.21/0.39  # Current number of unprocessed clauses: 199
% 0.21/0.39  # ...number of literals in the above   : 286
% 0.21/0.39  # Current number of archived formulas  : 0
% 0.21/0.39  # Current number of archived clauses   : 26
% 0.21/0.39  # Clause-clause subsumption calls (NU) : 195
% 0.21/0.39  # Rec. Clause-clause subsumption calls : 168
% 0.21/0.39  # Non-unit clause-clause subsumptions  : 6
% 0.21/0.39  # Unit Clause-clause subsumption calls : 118
% 0.21/0.39  # Rewrite failures with RHS unbound    : 0
% 0.21/0.39  # BW rewrite match attempts            : 26
% 0.21/0.39  # BW rewrite match successes           : 16
% 0.21/0.39  # Condensation attempts                : 0
% 0.21/0.39  # Condensation successes               : 0
% 0.21/0.39  # Termbank termtop insertions          : 6520
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.033 s
% 0.21/0.39  # System time              : 0.006 s
% 0.21/0.39  # Total time               : 0.040 s
% 0.21/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
