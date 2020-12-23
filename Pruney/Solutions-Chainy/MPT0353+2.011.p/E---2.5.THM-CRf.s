%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:44 EST 2020

% Result     : Theorem 0.37s
% Output     : CNFRefutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 170 expanded)
%              Number of clauses        :   38 (  76 expanded)
%              Number of leaves         :   12 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :  126 ( 419 expanded)
%              Number of equality atoms :   43 ( 127 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t32_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => k7_subset_1(X1,X2,X3) = k9_subset_1(X1,X2,k3_subset_1(X1,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

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

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(t112_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => k7_subset_1(X1,X2,X3) = k9_subset_1(X1,X2,k3_subset_1(X1,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t32_subset_1])).

fof(c_0_13,plain,(
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

fof(c_0_14,plain,(
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

fof(c_0_15,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
    & k7_subset_1(esk2_0,esk3_0,esk4_0) != k9_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_16,plain,(
    ! [X26] : ~ v1_xboole_0(k1_zfmisc_1(X26)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X13,X14] : r1_tarski(k4_xboole_0(X13,X14),X13) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_22,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k5_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_23,plain,(
    ! [X11,X12] :
      ( ~ r1_tarski(X11,X12)
      | k3_xboole_0(X11,X12) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

fof(c_0_26,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_28,plain,(
    ! [X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(X24))
      | k3_subset_1(X24,X25) = k4_xboole_0(X24,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_35,plain,(
    ! [X8,X9,X10] : k5_xboole_0(k3_xboole_0(X8,X9),k3_xboole_0(X10,X9)) = k3_xboole_0(k5_xboole_0(X8,X10),X9) ),
    inference(variable_rename,[status(thm)],[t112_xboole_1])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_27]),c_0_20])).

fof(c_0_37,plain,(
    ! [X30,X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(X30))
      | k9_subset_1(X30,X31,X32) = k3_xboole_0(X31,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_38,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk4_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

fof(c_0_43,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(X27))
      | k7_subset_1(X27,X28,X29) = k4_xboole_0(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_44,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( k7_subset_1(esk2_0,esk3_0,esk4_0) != k9_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_47,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_38,c_0_31])).

cnf(c_0_49,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_20])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk2_0,esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_51,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_34])).

cnf(c_0_53,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk3_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_45]),c_0_34])).

cnf(c_0_54,negated_conjecture,
    ( k3_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0)) != k7_subset_1(esk2_0,esk3_0,esk4_0)
    | ~ m1_subset_1(k3_subset_1(esk2_0,esk4_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( k3_subset_1(esk2_0,esk4_0) = k5_xboole_0(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_42]),c_0_19])])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(k5_xboole_0(esk2_0,esk4_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,plain,
    ( k7_subset_1(X2,X1,X3) = k5_xboole_0(X1,k3_xboole_0(X1,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_51,c_0_31])).

cnf(c_0_58,negated_conjecture,
    ( k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1)) = k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_34])).

cnf(c_0_59,negated_conjecture,
    ( k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk4_0)) != k7_subset_1(esk2_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55]),c_0_55]),c_0_56])])).

cnf(c_0_60,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,X2) = k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,X2))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( k7_subset_1(X1,esk3_0,esk4_0) != k7_subset_1(esk2_0,esk3_0,esk4_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_61]),c_0_27])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:49:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.36  # No SInE strategy applied
% 0.14/0.36  # Trying AutoSched0 for 299 seconds
% 0.37/0.53  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.37/0.53  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.37/0.53  #
% 0.37/0.53  # Preprocessing time       : 0.027 s
% 0.37/0.53  # Presaturation interreduction done
% 0.37/0.53  
% 0.37/0.53  # Proof found!
% 0.37/0.53  # SZS status Theorem
% 0.37/0.53  # SZS output start CNFRefutation
% 0.37/0.53  fof(t32_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k9_subset_1(X1,X2,k3_subset_1(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_subset_1)).
% 0.37/0.53  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.37/0.53  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.37/0.53  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.37/0.53  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.37/0.53  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.37/0.53  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.37/0.53  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.37/0.53  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.37/0.53  fof(t112_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_xboole_1)).
% 0.37/0.53  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.37/0.53  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.37/0.53  fof(c_0_12, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k9_subset_1(X1,X2,k3_subset_1(X1,X3))))), inference(assume_negation,[status(cth)],[t32_subset_1])).
% 0.37/0.53  fof(c_0_13, plain, ![X15, X16, X17, X18, X19, X20]:(((~r2_hidden(X17,X16)|r1_tarski(X17,X15)|X16!=k1_zfmisc_1(X15))&(~r1_tarski(X18,X15)|r2_hidden(X18,X16)|X16!=k1_zfmisc_1(X15)))&((~r2_hidden(esk1_2(X19,X20),X20)|~r1_tarski(esk1_2(X19,X20),X19)|X20=k1_zfmisc_1(X19))&(r2_hidden(esk1_2(X19,X20),X20)|r1_tarski(esk1_2(X19,X20),X19)|X20=k1_zfmisc_1(X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.37/0.53  fof(c_0_14, plain, ![X22, X23]:(((~m1_subset_1(X23,X22)|r2_hidden(X23,X22)|v1_xboole_0(X22))&(~r2_hidden(X23,X22)|m1_subset_1(X23,X22)|v1_xboole_0(X22)))&((~m1_subset_1(X23,X22)|v1_xboole_0(X23)|~v1_xboole_0(X22))&(~v1_xboole_0(X23)|m1_subset_1(X23,X22)|~v1_xboole_0(X22)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.37/0.53  fof(c_0_15, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))&k7_subset_1(esk2_0,esk3_0,esk4_0)!=k9_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.37/0.53  fof(c_0_16, plain, ![X26]:~v1_xboole_0(k1_zfmisc_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.37/0.53  cnf(c_0_17, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.37/0.53  cnf(c_0_18, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.37/0.53  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.37/0.53  cnf(c_0_20, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.37/0.53  fof(c_0_21, plain, ![X13, X14]:r1_tarski(k4_xboole_0(X13,X14),X13), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.37/0.53  fof(c_0_22, plain, ![X6, X7]:k4_xboole_0(X6,X7)=k5_xboole_0(X6,k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.37/0.53  fof(c_0_23, plain, ![X11, X12]:(~r1_tarski(X11,X12)|k3_xboole_0(X11,X12)=X11), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.37/0.53  cnf(c_0_24, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_17])).
% 0.37/0.53  cnf(c_0_25, negated_conjecture, (r2_hidden(esk4_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 0.37/0.53  fof(c_0_26, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.37/0.53  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.37/0.53  fof(c_0_28, plain, ![X24, X25]:(~m1_subset_1(X25,k1_zfmisc_1(X24))|k3_subset_1(X24,X25)=k4_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.37/0.53  cnf(c_0_29, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.37/0.53  cnf(c_0_30, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.37/0.53  cnf(c_0_31, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.37/0.53  cnf(c_0_32, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.37/0.53  cnf(c_0_33, negated_conjecture, (r1_tarski(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.37/0.53  cnf(c_0_34, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.37/0.53  fof(c_0_35, plain, ![X8, X9, X10]:k5_xboole_0(k3_xboole_0(X8,X9),k3_xboole_0(X10,X9))=k3_xboole_0(k5_xboole_0(X8,X10),X9), inference(variable_rename,[status(thm)],[t112_xboole_1])).
% 0.37/0.53  cnf(c_0_36, negated_conjecture, (r2_hidden(esk3_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_27]), c_0_20])).
% 0.37/0.53  fof(c_0_37, plain, ![X30, X31, X32]:(~m1_subset_1(X32,k1_zfmisc_1(X30))|k9_subset_1(X30,X31,X32)=k3_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.37/0.53  cnf(c_0_38, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.37/0.53  cnf(c_0_39, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.37/0.53  cnf(c_0_40, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_29])).
% 0.37/0.53  cnf(c_0_41, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 0.37/0.53  cnf(c_0_42, negated_conjecture, (k3_xboole_0(esk2_0,esk4_0)=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])).
% 0.37/0.53  fof(c_0_43, plain, ![X27, X28, X29]:(~m1_subset_1(X28,k1_zfmisc_1(X27))|k7_subset_1(X27,X28,X29)=k4_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.37/0.53  cnf(c_0_44, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.37/0.53  cnf(c_0_45, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_24, c_0_36])).
% 0.37/0.53  cnf(c_0_46, negated_conjecture, (k7_subset_1(esk2_0,esk3_0,esk4_0)!=k9_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.37/0.53  cnf(c_0_47, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.37/0.53  cnf(c_0_48, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_38, c_0_31])).
% 0.37/0.53  cnf(c_0_49, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_20])).
% 0.37/0.53  cnf(c_0_50, negated_conjecture, (r1_tarski(k5_xboole_0(esk2_0,esk4_0),esk2_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.37/0.53  cnf(c_0_51, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.37/0.53  cnf(c_0_52, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3))=k3_xboole_0(k5_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_44, c_0_34])).
% 0.37/0.53  cnf(c_0_53, negated_conjecture, (k3_xboole_0(esk2_0,esk3_0)=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_45]), c_0_34])).
% 0.37/0.53  cnf(c_0_54, negated_conjecture, (k3_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0))!=k7_subset_1(esk2_0,esk3_0,esk4_0)|~m1_subset_1(k3_subset_1(esk2_0,esk4_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.37/0.53  cnf(c_0_55, negated_conjecture, (k3_subset_1(esk2_0,esk4_0)=k5_xboole_0(esk2_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_42]), c_0_19])])).
% 0.37/0.53  cnf(c_0_56, negated_conjecture, (m1_subset_1(k5_xboole_0(esk2_0,esk4_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.37/0.53  cnf(c_0_57, plain, (k7_subset_1(X2,X1,X3)=k5_xboole_0(X1,k3_xboole_0(X1,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_51, c_0_31])).
% 0.37/0.53  cnf(c_0_58, negated_conjecture, (k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1))=k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_34])).
% 0.37/0.53  cnf(c_0_59, negated_conjecture, (k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk4_0))!=k7_subset_1(esk2_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55]), c_0_55]), c_0_56])])).
% 0.37/0.53  cnf(c_0_60, negated_conjecture, (k7_subset_1(X1,esk3_0,X2)=k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,X2))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.37/0.53  cnf(c_0_61, negated_conjecture, (k7_subset_1(X1,esk3_0,esk4_0)!=k7_subset_1(esk2_0,esk3_0,esk4_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.37/0.53  cnf(c_0_62, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_61]), c_0_27])]), ['proof']).
% 0.37/0.53  # SZS output end CNFRefutation
% 0.37/0.53  # Proof object total steps             : 63
% 0.37/0.53  # Proof object clause steps            : 38
% 0.37/0.53  # Proof object formula steps           : 25
% 0.37/0.53  # Proof object conjectures             : 21
% 0.37/0.53  # Proof object clause conjectures      : 18
% 0.37/0.53  # Proof object formula conjectures     : 3
% 0.37/0.53  # Proof object initial clauses used    : 16
% 0.37/0.53  # Proof object initial formulas used   : 12
% 0.37/0.53  # Proof object generating inferences   : 16
% 0.37/0.53  # Proof object simplifying inferences  : 19
% 0.37/0.53  # Training examples: 0 positive, 0 negative
% 0.37/0.53  # Parsed axioms                        : 12
% 0.37/0.53  # Removed by relevancy pruning/SinE    : 0
% 0.37/0.53  # Initial clauses                      : 20
% 0.37/0.53  # Removed in clause preprocessing      : 1
% 0.37/0.53  # Initial clauses in saturation        : 19
% 0.37/0.53  # Processed clauses                    : 1454
% 0.37/0.53  # ...of these trivial                  : 185
% 0.37/0.53  # ...subsumed                          : 685
% 0.37/0.53  # ...remaining for further processing  : 584
% 0.37/0.53  # Other redundant clauses eliminated   : 2
% 0.37/0.53  # Clauses deleted for lack of memory   : 0
% 0.37/0.53  # Backward-subsumed                    : 23
% 0.37/0.53  # Backward-rewritten                   : 38
% 0.37/0.53  # Generated clauses                    : 11856
% 0.37/0.53  # ...of the previous two non-trivial   : 10458
% 0.37/0.53  # Contextual simplify-reflections      : 2
% 0.37/0.53  # Paramodulations                      : 11851
% 0.37/0.53  # Factorizations                       : 2
% 0.37/0.53  # Equation resolutions                 : 3
% 0.37/0.53  # Propositional unsat checks           : 0
% 0.37/0.53  #    Propositional check models        : 0
% 0.37/0.53  #    Propositional check unsatisfiable : 0
% 0.37/0.53  #    Propositional clauses             : 0
% 0.37/0.53  #    Propositional clauses after purity: 0
% 0.37/0.53  #    Propositional unsat core size     : 0
% 0.37/0.53  #    Propositional preprocessing time  : 0.000
% 0.37/0.53  #    Propositional encoding time       : 0.000
% 0.37/0.53  #    Propositional solver time         : 0.000
% 0.37/0.53  #    Success case prop preproc time    : 0.000
% 0.37/0.53  #    Success case prop encoding time   : 0.000
% 0.37/0.53  #    Success case prop solver time     : 0.000
% 0.37/0.53  # Current number of processed clauses  : 502
% 0.37/0.53  #    Positive orientable unit clauses  : 323
% 0.37/0.53  #    Positive unorientable unit clauses: 1
% 0.37/0.53  #    Negative unit clauses             : 4
% 0.37/0.53  #    Non-unit-clauses                  : 174
% 0.37/0.53  # Current number of unprocessed clauses: 8993
% 0.37/0.53  # ...number of literals in the above   : 13862
% 0.37/0.53  # Current number of archived formulas  : 0
% 0.37/0.53  # Current number of archived clauses   : 81
% 0.37/0.53  # Clause-clause subsumption calls (NU) : 9254
% 0.37/0.53  # Rec. Clause-clause subsumption calls : 8870
% 0.37/0.53  # Non-unit clause-clause subsumptions  : 617
% 0.37/0.53  # Unit Clause-clause subsumption calls : 219
% 0.37/0.53  # Rewrite failures with RHS unbound    : 0
% 0.37/0.53  # BW rewrite match attempts            : 2286
% 0.37/0.53  # BW rewrite match successes           : 41
% 0.37/0.53  # Condensation attempts                : 0
% 0.37/0.53  # Condensation successes               : 0
% 0.37/0.53  # Termbank termtop insertions          : 226717
% 0.37/0.53  
% 0.37/0.53  # -------------------------------------------------
% 0.37/0.53  # User time                : 0.175 s
% 0.37/0.53  # System time              : 0.006 s
% 0.37/0.53  # Total time               : 0.181 s
% 0.37/0.53  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
