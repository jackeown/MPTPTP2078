%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:53 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 411 expanded)
%              Number of clauses        :   38 ( 188 expanded)
%              Number of leaves         :   12 ( 104 expanded)
%              Depth                    :   12
%              Number of atoms          :  155 (1223 expanded)
%              Number of equality atoms :   44 ( 249 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t38_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( r1_tarski(X2,k3_subset_1(X1,X2))
      <=> X2 = k1_subset_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

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

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

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

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ( r1_tarski(X2,k3_subset_1(X1,X2))
        <=> X2 = k1_subset_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t38_subset_1])).

fof(c_0_13,plain,(
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

fof(c_0_14,plain,(
    ! [X27,X28] :
      ( ( ~ m1_subset_1(X28,X27)
        | r2_hidden(X28,X27)
        | v1_xboole_0(X27) )
      & ( ~ r2_hidden(X28,X27)
        | m1_subset_1(X28,X27)
        | v1_xboole_0(X27) )
      & ( ~ m1_subset_1(X28,X27)
        | v1_xboole_0(X28)
        | ~ v1_xboole_0(X27) )
      & ( ~ v1_xboole_0(X28)
        | m1_subset_1(X28,X27)
        | ~ v1_xboole_0(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_15,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))
    & ( ~ r1_tarski(esk4_0,k3_subset_1(esk3_0,esk4_0))
      | esk4_0 != k1_subset_1(esk3_0) )
    & ( r1_tarski(esk4_0,k3_subset_1(esk3_0,esk4_0))
      | esk4_0 = k1_subset_1(esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_16,plain,(
    ! [X32] : ~ v1_xboole_0(k1_zfmisc_1(X32)) ),
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
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X12,X13,X14] :
      ( ( ~ r2_hidden(X12,X13)
        | ~ r2_hidden(X12,X14)
        | ~ r2_hidden(X12,k5_xboole_0(X13,X14)) )
      & ( r2_hidden(X12,X13)
        | r2_hidden(X12,X14)
        | ~ r2_hidden(X12,k5_xboole_0(X13,X14)) )
      & ( ~ r2_hidden(X12,X13)
        | r2_hidden(X12,X14)
        | r2_hidden(X12,k5_xboole_0(X13,X14)) )
      & ( ~ r2_hidden(X12,X14)
        | r2_hidden(X12,X13)
        | r2_hidden(X12,k5_xboole_0(X13,X14)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

fof(c_0_22,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_23,plain,(
    ! [X29] : k1_subset_1(X29) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

fof(c_0_24,plain,(
    ! [X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(X30))
      | k3_subset_1(X30,X31) = k4_xboole_0(X30,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_25,plain,(
    ! [X15,X16] : k4_xboole_0(X15,X16) = k5_xboole_0(X15,k3_xboole_0(X15,X16)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_26,plain,(
    ! [X17,X18] :
      ( ~ r1_tarski(X17,X18)
      | k3_xboole_0(X17,X18) = X17 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk4_0,k1_zfmisc_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk4_0,k3_subset_1(esk3_0,esk4_0))
    | esk4_0 = k1_subset_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_35,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_38,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),k5_xboole_0(X3,X1))
    | ~ r2_hidden(esk1_2(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_40,plain,(
    ! [X19] : k5_xboole_0(X19,k1_xboole_0) = X19 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_41,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(esk4_0,k3_subset_1(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_42,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk3_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_37])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),k5_xboole_0(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_30])).

cnf(c_0_47,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(X1,k3_subset_1(esk3_0,esk4_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( k3_subset_1(esk3_0,esk4_0) = k5_xboole_0(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_19]),c_0_43]),c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,X1),esk3_0)
    | r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_30])).

cnf(c_0_51,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_30])).

cnf(c_0_52,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(X1,k5_xboole_0(esk3_0,esk4_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(rw,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | ~ r2_hidden(esk1_2(esk4_0,X1),k5_xboole_0(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k3_subset_1(esk3_0,esk4_0))
    | esk4_0 != k1_subset_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_55,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(esk4_0,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_30]),c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    | ~ r1_tarski(esk4_0,k3_subset_1(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_54,c_0_32])).

cnf(c_0_58,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( k3_xboole_0(esk4_0,X1) = esk4_0
    | esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    | ~ r1_tarski(esk4_0,k5_xboole_0(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_57,c_0_49])).

cnf(c_0_61,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61]),c_0_61]),c_0_61]),c_0_47]),c_0_51])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:26:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S4b
% 0.19/0.37  # and selection function SelectCQIPrecW.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.028 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t38_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X2))<=>X2=k1_subset_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 0.19/0.37  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.19/0.37  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.19/0.37  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.19/0.37  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 0.19/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.37  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 0.19/0.37  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.19/0.37  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.37  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.19/0.37  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.37  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.19/0.37  fof(c_0_12, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X2))<=>X2=k1_subset_1(X1)))), inference(assume_negation,[status(cth)],[t38_subset_1])).
% 0.19/0.37  fof(c_0_13, plain, ![X20, X21, X22, X23, X24, X25]:(((~r2_hidden(X22,X21)|r1_tarski(X22,X20)|X21!=k1_zfmisc_1(X20))&(~r1_tarski(X23,X20)|r2_hidden(X23,X21)|X21!=k1_zfmisc_1(X20)))&((~r2_hidden(esk2_2(X24,X25),X25)|~r1_tarski(esk2_2(X24,X25),X24)|X25=k1_zfmisc_1(X24))&(r2_hidden(esk2_2(X24,X25),X25)|r1_tarski(esk2_2(X24,X25),X24)|X25=k1_zfmisc_1(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.19/0.37  fof(c_0_14, plain, ![X27, X28]:(((~m1_subset_1(X28,X27)|r2_hidden(X28,X27)|v1_xboole_0(X27))&(~r2_hidden(X28,X27)|m1_subset_1(X28,X27)|v1_xboole_0(X27)))&((~m1_subset_1(X28,X27)|v1_xboole_0(X28)|~v1_xboole_0(X27))&(~v1_xboole_0(X28)|m1_subset_1(X28,X27)|~v1_xboole_0(X27)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.19/0.37  fof(c_0_15, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))&((~r1_tarski(esk4_0,k3_subset_1(esk3_0,esk4_0))|esk4_0!=k1_subset_1(esk3_0))&(r1_tarski(esk4_0,k3_subset_1(esk3_0,esk4_0))|esk4_0=k1_subset_1(esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.19/0.37  fof(c_0_16, plain, ![X32]:~v1_xboole_0(k1_zfmisc_1(X32)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.19/0.37  cnf(c_0_17, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_18, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.37  cnf(c_0_20, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.37  fof(c_0_21, plain, ![X12, X13, X14]:(((~r2_hidden(X12,X13)|~r2_hidden(X12,X14)|~r2_hidden(X12,k5_xboole_0(X13,X14)))&(r2_hidden(X12,X13)|r2_hidden(X12,X14)|~r2_hidden(X12,k5_xboole_0(X13,X14))))&((~r2_hidden(X12,X13)|r2_hidden(X12,X14)|r2_hidden(X12,k5_xboole_0(X13,X14)))&(~r2_hidden(X12,X14)|r2_hidden(X12,X13)|r2_hidden(X12,k5_xboole_0(X13,X14))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 0.19/0.37  fof(c_0_22, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.37  fof(c_0_23, plain, ![X29]:k1_subset_1(X29)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.19/0.37  fof(c_0_24, plain, ![X30, X31]:(~m1_subset_1(X31,k1_zfmisc_1(X30))|k3_subset_1(X30,X31)=k4_xboole_0(X30,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.19/0.37  fof(c_0_25, plain, ![X15, X16]:k4_xboole_0(X15,X16)=k5_xboole_0(X15,k3_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.37  fof(c_0_26, plain, ![X17, X18]:(~r1_tarski(X17,X18)|k3_xboole_0(X17,X18)=X17), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.19/0.37  cnf(c_0_27, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_17])).
% 0.19/0.37  cnf(c_0_28, negated_conjecture, (r2_hidden(esk4_0,k1_zfmisc_1(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 0.19/0.37  cnf(c_0_29, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.37  cnf(c_0_30, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.37  cnf(c_0_31, negated_conjecture, (r1_tarski(esk4_0,k3_subset_1(esk3_0,esk4_0))|esk4_0=k1_subset_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.37  cnf(c_0_32, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.37  cnf(c_0_33, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.37  cnf(c_0_34, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.37  fof(c_0_35, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.37  cnf(c_0_36, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.37  cnf(c_0_37, negated_conjecture, (r1_tarski(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.37  cnf(c_0_38, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.37  cnf(c_0_39, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),k5_xboole_0(X3,X1))|~r2_hidden(esk1_2(X1,X2),X3)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.37  fof(c_0_40, plain, ![X19]:k5_xboole_0(X19,k1_xboole_0)=X19, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.19/0.37  cnf(c_0_41, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(esk4_0,k3_subset_1(esk3_0,esk4_0))), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.37  cnf(c_0_42, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.37  cnf(c_0_43, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.37  cnf(c_0_44, negated_conjecture, (k3_xboole_0(esk4_0,esk3_0)=esk4_0), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.37  cnf(c_0_45, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_38, c_0_37])).
% 0.19/0.37  cnf(c_0_46, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),k5_xboole_0(X1,X1))), inference(spm,[status(thm)],[c_0_39, c_0_30])).
% 0.19/0.37  cnf(c_0_47, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.37  cnf(c_0_48, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(X1,k3_subset_1(esk3_0,esk4_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_38, c_0_41])).
% 0.19/0.37  cnf(c_0_49, negated_conjecture, (k3_subset_1(esk3_0,esk4_0)=k5_xboole_0(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_19]), c_0_43]), c_0_44])).
% 0.19/0.37  cnf(c_0_50, negated_conjecture, (r2_hidden(esk1_2(esk4_0,X1),esk3_0)|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_45, c_0_30])).
% 0.19/0.37  cnf(c_0_51, plain, (r1_tarski(k1_xboole_0,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_30])).
% 0.19/0.37  cnf(c_0_52, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(X1,k5_xboole_0(esk3_0,esk4_0))|~r2_hidden(X1,esk4_0)), inference(rw,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.37  cnf(c_0_53, negated_conjecture, (r1_tarski(esk4_0,X1)|~r2_hidden(esk1_2(esk4_0,X1),k5_xboole_0(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_39, c_0_50])).
% 0.19/0.37  cnf(c_0_54, negated_conjecture, (~r1_tarski(esk4_0,k3_subset_1(esk3_0,esk4_0))|esk4_0!=k1_subset_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.37  cnf(c_0_55, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_51])).
% 0.19/0.37  cnf(c_0_56, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(esk4_0,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_30]), c_0_53])).
% 0.19/0.37  cnf(c_0_57, negated_conjecture, (esk4_0!=k1_xboole_0|~r1_tarski(esk4_0,k3_subset_1(esk3_0,esk4_0))), inference(rw,[status(thm)],[c_0_54, c_0_32])).
% 0.19/0.37  cnf(c_0_58, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_55])).
% 0.19/0.37  cnf(c_0_59, negated_conjecture, (k3_xboole_0(esk4_0,X1)=esk4_0|esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_56])).
% 0.19/0.37  cnf(c_0_60, negated_conjecture, (esk4_0!=k1_xboole_0|~r1_tarski(esk4_0,k5_xboole_0(esk3_0,esk4_0))), inference(rw,[status(thm)],[c_0_57, c_0_49])).
% 0.19/0.37  cnf(c_0_61, negated_conjecture, (esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.37  cnf(c_0_62, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61]), c_0_61]), c_0_61]), c_0_47]), c_0_51])]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 63
% 0.19/0.37  # Proof object clause steps            : 38
% 0.19/0.37  # Proof object formula steps           : 25
% 0.19/0.37  # Proof object conjectures             : 22
% 0.19/0.37  # Proof object clause conjectures      : 19
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 15
% 0.19/0.37  # Proof object initial formulas used   : 12
% 0.19/0.37  # Proof object generating inferences   : 16
% 0.19/0.37  # Proof object simplifying inferences  : 17
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 12
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 25
% 0.19/0.37  # Removed in clause preprocessing      : 2
% 0.19/0.37  # Initial clauses in saturation        : 23
% 0.19/0.37  # Processed clauses                    : 172
% 0.19/0.37  # ...of these trivial                  : 1
% 0.19/0.37  # ...subsumed                          : 36
% 0.19/0.37  # ...remaining for further processing  : 135
% 0.19/0.37  # Other redundant clauses eliminated   : 2
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 4
% 0.19/0.37  # Backward-rewritten                   : 55
% 0.19/0.37  # Generated clauses                    : 254
% 0.19/0.37  # ...of the previous two non-trivial   : 241
% 0.19/0.37  # Contextual simplify-reflections      : 2
% 0.19/0.37  # Paramodulations                      : 250
% 0.19/0.37  # Factorizations                       : 2
% 0.19/0.37  # Equation resolutions                 : 2
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 51
% 0.19/0.37  #    Positive orientable unit clauses  : 13
% 0.19/0.37  #    Positive unorientable unit clauses: 1
% 0.19/0.37  #    Negative unit clauses             : 3
% 0.19/0.37  #    Non-unit-clauses                  : 34
% 0.19/0.37  # Current number of unprocessed clauses: 100
% 0.19/0.37  # ...number of literals in the above   : 306
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 84
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 624
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 566
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 30
% 0.19/0.37  # Unit Clause-clause subsumption calls : 81
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 26
% 0.19/0.37  # BW rewrite match successes           : 6
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 5200
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.038 s
% 0.19/0.37  # System time              : 0.004 s
% 0.19/0.37  # Total time               : 0.042 s
% 0.19/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
