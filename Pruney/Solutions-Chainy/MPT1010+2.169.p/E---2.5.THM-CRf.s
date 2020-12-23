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
% DateTime   : Thu Dec  3 11:05:35 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 230 expanded)
%              Number of clauses        :   33 (  98 expanded)
%              Number of leaves         :    9 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  125 ( 642 expanded)
%              Number of equality atoms :   80 ( 273 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t65_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,k1_tarski(X2))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
     => ( r2_hidden(X3,X1)
       => k1_funct_1(X4,X3) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t82_enumset1,axiom,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(t7_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_hidden(X3,X1)
       => ( X2 = k1_xboole_0
          | r2_hidden(k1_funct_1(X4,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(t75_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(X1,k2_tarski(X2,X3)) = k1_xboole_0
    <=> ~ ( X1 != k1_xboole_0
          & X1 != k1_tarski(X2)
          & X1 != k1_tarski(X3)
          & X1 != k2_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_zfmisc_1)).

fof(t208_relat_1,axiom,(
    ! [X1] : k3_relat_1(k1_tarski(k4_tarski(X1,X1))) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t208_relat_1)).

fof(t32_relat_1,axiom,(
    ! [X1,X2] : k3_relat_1(k1_tarski(k4_tarski(X1,X2))) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relat_1)).

fof(t20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,k1_tarski(X2))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
       => ( r2_hidden(X3,X1)
         => k1_funct_1(X4,X3) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t65_funct_2])).

fof(c_0_10,plain,(
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

fof(c_0_11,plain,(
    ! [X17] : k2_enumset1(X17,X17,X17,X17) = k1_tarski(X17) ),
    inference(variable_rename,[status(thm)],[t82_enumset1])).

fof(c_0_12,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk2_0,k1_tarski(esk3_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_tarski(esk3_0))))
    & r2_hidden(esk4_0,esk2_0)
    & k1_funct_1(esk5_0,esk4_0) != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_13,plain,(
    ! [X12,X13] : k2_tarski(X12,X13) = k2_xboole_0(k1_tarski(X12),k1_tarski(X13)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

cnf(c_0_14,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k2_enumset1(X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X32,X33,X34,X35] :
      ( ~ v1_funct_1(X35)
      | ~ v1_funct_2(X35,X32,X33)
      | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | ~ r2_hidden(X34,X32)
      | X33 = k1_xboole_0
      | r2_hidden(k1_funct_1(X35,X34),X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_tarski(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_2(esk5_0,esk2_0,k1_tarski(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_19,plain,(
    ! [X22,X23,X24] :
      ( ( k4_xboole_0(X22,k2_tarski(X23,X24)) != k1_xboole_0
        | X22 = k1_xboole_0
        | X22 = k1_tarski(X23)
        | X22 = k1_tarski(X24)
        | X22 = k2_tarski(X23,X24) )
      & ( X22 != k1_xboole_0
        | k4_xboole_0(X22,k2_tarski(X23,X24)) = k1_xboole_0 )
      & ( X22 != k1_tarski(X23)
        | k4_xboole_0(X22,k2_tarski(X23,X24)) = k1_xboole_0 )
      & ( X22 != k1_tarski(X24)
        | k4_xboole_0(X22,k2_tarski(X23,X24)) = k1_xboole_0 )
      & ( X22 != k2_tarski(X23,X24)
        | k4_xboole_0(X22,k2_tarski(X23,X24)) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t75_zfmisc_1])])])).

cnf(c_0_20,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,plain,
    ( X3 = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X4),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_17,c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_2(esk5_0,esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_18,c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k2_tarski(X2,X3)) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_15]),c_0_15])).

cnf(c_0_28,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) = k1_xboole_0
    | r2_hidden(k1_funct_1(esk5_0,X1),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])])).

fof(c_0_30,plain,(
    ! [X25] : k3_relat_1(k1_tarski(k4_tarski(X25,X25))) = k1_tarski(X25) ),
    inference(variable_rename,[status(thm)],[t208_relat_1])).

fof(c_0_31,plain,(
    ! [X26,X27] : k3_relat_1(k1_tarski(k4_tarski(X26,X27))) = k2_tarski(X26,X27) ),
    inference(variable_rename,[status(thm)],[t32_relat_1])).

fof(c_0_32,plain,(
    ! [X20,X21] :
      ( ( k4_xboole_0(k1_tarski(X20),k1_tarski(X21)) != k1_tarski(X20)
        | X20 != X21 )
      & ( X20 = X21
        | k4_xboole_0(k1_tarski(X20),k1_tarski(X21)) = k1_tarski(X20) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3))) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) = k1_xboole_0
    | k1_funct_1(esk5_0,X1) = esk3_0
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_36,negated_conjecture,
    ( k1_funct_1(esk5_0,esk4_0) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_37,plain,
    ( k3_relat_1(k1_tarski(k4_tarski(X1,X1))) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( k3_relat_1(k1_tarski(k4_tarski(X1,X2))) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) != k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_42,plain,
    ( k3_relat_1(k2_enumset1(k4_tarski(X1,X1),k4_tarski(X1,X1),k4_tarski(X1,X1),k4_tarski(X1,X1))) = k2_enumset1(X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_15]),c_0_15])).

cnf(c_0_43,plain,
    ( k3_relat_1(k2_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2))) = k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_15]),c_0_27])).

cnf(c_0_44,plain,
    ( X1 != X2
    | k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) != k2_enumset1(X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_15]),c_0_15]),c_0_15])).

cnf(c_0_45,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k2_enumset1(X1,X1,X1,X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,plain,
    ( k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) = k2_enumset1(X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_47,plain,
    ( k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) != k2_enumset1(X1,X1,X1,X1) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49]),c_0_50]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:03:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.19/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.027 s
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t65_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 0.19/0.38  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.19/0.38  fof(t82_enumset1, axiom, ![X1]:k2_enumset1(X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_enumset1)).
% 0.19/0.38  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 0.19/0.38  fof(t7_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_hidden(X3,X1)=>(X2=k1_xboole_0|r2_hidden(k1_funct_1(X4,X3),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 0.19/0.38  fof(t75_zfmisc_1, axiom, ![X1, X2, X3]:(k4_xboole_0(X1,k2_tarski(X2,X3))=k1_xboole_0<=>~((((X1!=k1_xboole_0&X1!=k1_tarski(X2))&X1!=k1_tarski(X3))&X1!=k2_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_zfmisc_1)).
% 0.19/0.38  fof(t208_relat_1, axiom, ![X1]:k3_relat_1(k1_tarski(k4_tarski(X1,X1)))=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t208_relat_1)).
% 0.19/0.38  fof(t32_relat_1, axiom, ![X1, X2]:k3_relat_1(k1_tarski(k4_tarski(X1,X2)))=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_relat_1)).
% 0.19/0.38  fof(t20_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 0.19/0.38  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2))), inference(assume_negation,[status(cth)],[t65_funct_2])).
% 0.19/0.38  fof(c_0_10, plain, ![X5, X6, X7, X8, X9, X10]:(((~r2_hidden(X7,X6)|X7=X5|X6!=k1_tarski(X5))&(X8!=X5|r2_hidden(X8,X6)|X6!=k1_tarski(X5)))&((~r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)!=X9|X10=k1_tarski(X9))&(r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)=X9|X10=k1_tarski(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.19/0.38  fof(c_0_11, plain, ![X17]:k2_enumset1(X17,X17,X17,X17)=k1_tarski(X17), inference(variable_rename,[status(thm)],[t82_enumset1])).
% 0.19/0.38  fof(c_0_12, negated_conjecture, (((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk2_0,k1_tarski(esk3_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_tarski(esk3_0)))))&(r2_hidden(esk4_0,esk2_0)&k1_funct_1(esk5_0,esk4_0)!=esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.19/0.38  fof(c_0_13, plain, ![X12, X13]:k2_tarski(X12,X13)=k2_xboole_0(k1_tarski(X12),k1_tarski(X13)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.19/0.38  cnf(c_0_14, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_15, plain, (k2_enumset1(X1,X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  fof(c_0_16, plain, ![X32, X33, X34, X35]:(~v1_funct_1(X35)|~v1_funct_2(X35,X32,X33)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|(~r2_hidden(X34,X32)|(X33=k1_xboole_0|r2_hidden(k1_funct_1(X35,X34),X33)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).
% 0.19/0.38  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_tarski(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_18, negated_conjecture, (v1_funct_2(esk5_0,esk2_0,k1_tarski(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  fof(c_0_19, plain, ![X22, X23, X24]:((k4_xboole_0(X22,k2_tarski(X23,X24))!=k1_xboole_0|(X22=k1_xboole_0|X22=k1_tarski(X23)|X22=k1_tarski(X24)|X22=k2_tarski(X23,X24)))&((((X22!=k1_xboole_0|k4_xboole_0(X22,k2_tarski(X23,X24))=k1_xboole_0)&(X22!=k1_tarski(X23)|k4_xboole_0(X22,k2_tarski(X23,X24))=k1_xboole_0))&(X22!=k1_tarski(X24)|k4_xboole_0(X22,k2_tarski(X23,X24))=k1_xboole_0))&(X22!=k2_tarski(X23,X24)|k4_xboole_0(X22,k2_tarski(X23,X24))=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t75_zfmisc_1])])])).
% 0.19/0.38  cnf(c_0_20, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_21, plain, (X1=X3|X2!=k2_enumset1(X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.38  cnf(c_0_22, plain, (X3=k1_xboole_0|r2_hidden(k1_funct_1(X1,X4),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))))), inference(rw,[status(thm)],[c_0_17, c_0_15])).
% 0.19/0.38  cnf(c_0_24, negated_conjecture, (v1_funct_2(esk5_0,esk2_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))), inference(rw,[status(thm)],[c_0_18, c_0_15])).
% 0.19/0.38  cnf(c_0_25, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_26, plain, (k4_xboole_0(X1,k2_tarski(X2,X3))=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_27, plain, (k2_tarski(X1,X2)=k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_15]), c_0_15])).
% 0.19/0.38  cnf(c_0_28, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_21])).
% 0.19/0.38  cnf(c_0_29, negated_conjecture, (k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)=k1_xboole_0|r2_hidden(k1_funct_1(esk5_0,X1),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))|~r2_hidden(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25])])).
% 0.19/0.38  fof(c_0_30, plain, ![X25]:k3_relat_1(k1_tarski(k4_tarski(X25,X25)))=k1_tarski(X25), inference(variable_rename,[status(thm)],[t208_relat_1])).
% 0.19/0.38  fof(c_0_31, plain, ![X26, X27]:k3_relat_1(k1_tarski(k4_tarski(X26,X27)))=k2_tarski(X26,X27), inference(variable_rename,[status(thm)],[t32_relat_1])).
% 0.19/0.38  fof(c_0_32, plain, ![X20, X21]:((k4_xboole_0(k1_tarski(X20),k1_tarski(X21))!=k1_tarski(X20)|X20!=X21)&(X20=X21|k4_xboole_0(k1_tarski(X20),k1_tarski(X21))=k1_tarski(X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).
% 0.19/0.38  cnf(c_0_33, plain, (k4_xboole_0(X1,k2_xboole_0(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3)))=k1_xboole_0|X1!=k1_xboole_0), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.38  cnf(c_0_34, negated_conjecture, (k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)=k1_xboole_0|k1_funct_1(esk5_0,X1)=esk3_0|~r2_hidden(X1,esk2_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (r2_hidden(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (k1_funct_1(esk5_0,esk4_0)!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_37, plain, (k3_relat_1(k1_tarski(k4_tarski(X1,X1)))=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.38  cnf(c_0_38, plain, (k3_relat_1(k1_tarski(k4_tarski(X1,X2)))=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.38  cnf(c_0_39, plain, (k4_xboole_0(k1_tarski(X1),k1_tarski(X2))!=k1_tarski(X1)|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.38  cnf(c_0_40, plain, (k4_xboole_0(k1_xboole_0,k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)))=k1_xboole_0), inference(er,[status(thm)],[c_0_33])).
% 0.19/0.38  cnf(c_0_41, negated_conjecture, (k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 0.19/0.38  cnf(c_0_42, plain, (k3_relat_1(k2_enumset1(k4_tarski(X1,X1),k4_tarski(X1,X1),k4_tarski(X1,X1),k4_tarski(X1,X1)))=k2_enumset1(X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_15]), c_0_15])).
% 0.19/0.38  cnf(c_0_43, plain, (k3_relat_1(k2_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2)))=k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_15]), c_0_27])).
% 0.19/0.38  cnf(c_0_44, plain, (X1!=X2|k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))!=k2_enumset1(X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_15]), c_0_15]), c_0_15])).
% 0.19/0.38  cnf(c_0_45, negated_conjecture, (k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k2_enumset1(X1,X1,X1,X1)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.38  cnf(c_0_46, plain, (k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))=k2_enumset1(X1,X1,X1,X1)), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.38  cnf(c_0_47, plain, (k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))!=k2_enumset1(X1,X1,X1,X1)), inference(er,[status(thm)],[c_0_44])).
% 0.19/0.38  cnf(c_0_48, negated_conjecture, (k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_45, c_0_41])).
% 0.19/0.38  cnf(c_0_49, negated_conjecture, (k2_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_46, c_0_41])).
% 0.19/0.38  cnf(c_0_50, negated_conjecture, (k4_xboole_0(k1_xboole_0,k1_xboole_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_41])).
% 0.19/0.38  cnf(c_0_51, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49]), c_0_50]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 52
% 0.19/0.38  # Proof object clause steps            : 33
% 0.19/0.38  # Proof object formula steps           : 19
% 0.19/0.38  # Proof object conjectures             : 18
% 0.19/0.38  # Proof object clause conjectures      : 15
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 13
% 0.19/0.38  # Proof object initial formulas used   : 9
% 0.19/0.38  # Proof object generating inferences   : 7
% 0.19/0.38  # Proof object simplifying inferences  : 23
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 12
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 24
% 0.19/0.38  # Removed in clause preprocessing      : 3
% 0.19/0.38  # Initial clauses in saturation        : 21
% 0.19/0.38  # Processed clauses                    : 76
% 0.19/0.38  # ...of these trivial                  : 1
% 0.19/0.38  # ...subsumed                          : 17
% 0.19/0.38  # ...remaining for further processing  : 58
% 0.19/0.38  # Other redundant clauses eliminated   : 20
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 7
% 0.19/0.38  # Generated clauses                    : 420
% 0.19/0.38  # ...of the previous two non-trivial   : 345
% 0.19/0.38  # Contextual simplify-reflections      : 0
% 0.19/0.38  # Paramodulations                      : 396
% 0.19/0.38  # Factorizations                       : 5
% 0.19/0.38  # Equation resolutions                 : 20
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 47
% 0.19/0.38  #    Positive orientable unit clauses  : 13
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 3
% 0.19/0.38  #    Non-unit-clauses                  : 31
% 0.19/0.38  # Current number of unprocessed clauses: 281
% 0.19/0.38  # ...number of literals in the above   : 1417
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 10
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 213
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 98
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 13
% 0.19/0.38  # Unit Clause-clause subsumption calls : 7
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 5
% 0.19/0.38  # BW rewrite match successes           : 3
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 7984
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.037 s
% 0.19/0.38  # System time              : 0.006 s
% 0.19/0.38  # Total time               : 0.043 s
% 0.19/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
