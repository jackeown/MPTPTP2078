%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:41 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 121 expanded)
%              Number of clauses        :   23 (  49 expanded)
%              Number of leaves         :   10 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :  122 ( 349 expanded)
%              Number of equality atoms :   37 ( 132 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t46_setfam_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ~ ( X2 != k1_xboole_0
          & k7_setfam_1(X1,X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

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

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(involutiveness_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k7_setfam_1(X1,k7_setfam_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(c_0_10,plain,(
    ! [X14,X15] : k4_xboole_0(X14,k2_xboole_0(X14,X15)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_11,plain,(
    ! [X11,X12] : k4_xboole_0(X11,X12) = k5_xboole_0(X11,k3_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_12,plain,(
    ! [X16,X17] :
      ( ( ~ r1_xboole_0(X16,X17)
        | k4_xboole_0(X16,X17) = X16 )
      & ( k4_xboole_0(X16,X17) != X16
        | r1_xboole_0(X16,X17) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_13,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X13] : k2_xboole_0(X13,k1_xboole_0) = X13 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ~ ( X2 != k1_xboole_0
            & k7_setfam_1(X1,X2) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t46_setfam_1])).

cnf(c_0_17,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X19,X20,X21,X22] :
      ( ( ~ r2_hidden(X22,X21)
        | r2_hidden(k3_subset_1(X19,X22),X20)
        | ~ m1_subset_1(X22,k1_zfmisc_1(X19))
        | X21 != k7_setfam_1(X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X19)))
        | ~ m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(X19))) )
      & ( ~ r2_hidden(k3_subset_1(X19,X22),X20)
        | r2_hidden(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(X19))
        | X21 != k7_setfam_1(X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X19)))
        | ~ m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(X19))) )
      & ( m1_subset_1(esk2_3(X19,X20,X21),k1_zfmisc_1(X19))
        | X21 = k7_setfam_1(X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X19)))
        | ~ m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(X19))) )
      & ( ~ r2_hidden(esk2_3(X19,X20,X21),X21)
        | ~ r2_hidden(k3_subset_1(X19,esk2_3(X19,X20,X21)),X20)
        | X21 = k7_setfam_1(X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X19)))
        | ~ m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(X19))) )
      & ( r2_hidden(esk2_3(X19,X20,X21),X21)
        | r2_hidden(k3_subset_1(X19,esk2_3(X19,X20,X21)),X20)
        | X21 = k7_setfam_1(X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X19)))
        | ~ m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(X19))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_setfam_1])])])])])).

fof(c_0_21,plain,(
    ! [X26,X27,X28] :
      ( ~ r2_hidden(X26,X27)
      | ~ m1_subset_1(X27,k1_zfmisc_1(X28))
      | m1_subset_1(X26,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_22,plain,(
    ! [X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24)))
      | k7_setfam_1(X24,k7_setfam_1(X24,X25)) = X25 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).

fof(c_0_23,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))
    & esk4_0 != k1_xboole_0
    & k7_setfam_1(esk3_0,esk4_0) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_24,plain,(
    ! [X5,X6,X8,X9,X10] :
      ( ( r2_hidden(esk1_2(X5,X6),X5)
        | r1_xboole_0(X5,X6) )
      & ( r2_hidden(esk1_2(X5,X6),X6)
        | r1_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | ~ r1_xboole_0(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_25,plain,
    ( r1_xboole_0(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != X1 ),
    inference(rw,[status(thm)],[c_0_17,c_0_14])).

cnf(c_0_26,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,plain,
    ( r2_hidden(k3_subset_1(X3,X1),X4)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | X2 != k7_setfam_1(X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k7_setfam_1(X2,k7_setfam_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( k7_setfam_1(esk3_0,esk4_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_32,plain,(
    ! [X18] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X18)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26])])).

cnf(c_0_35,plain,
    ( r2_hidden(k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(k7_setfam_1(X1,X3),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X2,k7_setfam_1(X1,X3)) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_27,c_0_28])])).

cnf(c_0_36,negated_conjecture,
    ( k7_setfam_1(esk3_0,k1_xboole_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_37,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(k3_subset_1(X1,esk2_3(X1,X2,X3)),X2)
    | X3 = k7_setfam_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_40,negated_conjecture,
    ( ~ r2_hidden(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_30]),c_0_37])]),c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_3(esk3_0,esk4_0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk3_0))) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_30]),c_0_31]),c_0_40])).

cnf(c_0_42,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_30]),c_0_42]),c_0_40]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n021.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 11:32:19 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  # Version: 2.5pre002
% 0.12/0.32  # No SInE strategy applied
% 0.12/0.32  # Trying AutoSched0 for 299 seconds
% 0.12/0.35  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.12/0.35  # and selection function SelectNegativeLiterals.
% 0.12/0.35  #
% 0.12/0.35  # Preprocessing time       : 0.027 s
% 0.12/0.35  # Presaturation interreduction done
% 0.12/0.35  
% 0.12/0.35  # Proof found!
% 0.12/0.35  # SZS status Theorem
% 0.12/0.35  # SZS output start CNFRefutation
% 0.12/0.35  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.12/0.35  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.12/0.35  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.12/0.35  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.12/0.35  fof(t46_setfam_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>~((X2!=k1_xboole_0&k7_setfam_1(X1,X2)=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_setfam_1)).
% 0.12/0.35  fof(d8_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(X3=k7_setfam_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>(r2_hidden(X4,X3)<=>r2_hidden(k3_subset_1(X1,X4),X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_setfam_1)).
% 0.12/0.35  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.12/0.35  fof(involutiveness_k7_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k7_setfam_1(X1,k7_setfam_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 0.12/0.35  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.12/0.35  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.12/0.35  fof(c_0_10, plain, ![X14, X15]:k4_xboole_0(X14,k2_xboole_0(X14,X15))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.12/0.35  fof(c_0_11, plain, ![X11, X12]:k4_xboole_0(X11,X12)=k5_xboole_0(X11,k3_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.12/0.35  fof(c_0_12, plain, ![X16, X17]:((~r1_xboole_0(X16,X17)|k4_xboole_0(X16,X17)=X16)&(k4_xboole_0(X16,X17)!=X16|r1_xboole_0(X16,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.12/0.35  cnf(c_0_13, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.35  cnf(c_0_14, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.35  fof(c_0_15, plain, ![X13]:k2_xboole_0(X13,k1_xboole_0)=X13, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.12/0.35  fof(c_0_16, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>~((X2!=k1_xboole_0&k7_setfam_1(X1,X2)=k1_xboole_0)))), inference(assume_negation,[status(cth)],[t46_setfam_1])).
% 0.12/0.35  cnf(c_0_17, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.35  cnf(c_0_18, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k2_xboole_0(X1,X2)))=k1_xboole_0), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.12/0.35  cnf(c_0_19, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.35  fof(c_0_20, plain, ![X19, X20, X21, X22]:(((~r2_hidden(X22,X21)|r2_hidden(k3_subset_1(X19,X22),X20)|~m1_subset_1(X22,k1_zfmisc_1(X19))|X21!=k7_setfam_1(X19,X20)|~m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X19)))|~m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(X19))))&(~r2_hidden(k3_subset_1(X19,X22),X20)|r2_hidden(X22,X21)|~m1_subset_1(X22,k1_zfmisc_1(X19))|X21!=k7_setfam_1(X19,X20)|~m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X19)))|~m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(X19)))))&((m1_subset_1(esk2_3(X19,X20,X21),k1_zfmisc_1(X19))|X21=k7_setfam_1(X19,X20)|~m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X19)))|~m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(X19))))&((~r2_hidden(esk2_3(X19,X20,X21),X21)|~r2_hidden(k3_subset_1(X19,esk2_3(X19,X20,X21)),X20)|X21=k7_setfam_1(X19,X20)|~m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X19)))|~m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(X19))))&(r2_hidden(esk2_3(X19,X20,X21),X21)|r2_hidden(k3_subset_1(X19,esk2_3(X19,X20,X21)),X20)|X21=k7_setfam_1(X19,X20)|~m1_subset_1(X21,k1_zfmisc_1(k1_zfmisc_1(X19)))|~m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(X19))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_setfam_1])])])])])).
% 0.12/0.35  fof(c_0_21, plain, ![X26, X27, X28]:(~r2_hidden(X26,X27)|~m1_subset_1(X27,k1_zfmisc_1(X28))|m1_subset_1(X26,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.12/0.35  fof(c_0_22, plain, ![X24, X25]:(~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24)))|k7_setfam_1(X24,k7_setfam_1(X24,X25))=X25), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).
% 0.12/0.35  fof(c_0_23, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))&(esk4_0!=k1_xboole_0&k7_setfam_1(esk3_0,esk4_0)=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.12/0.35  fof(c_0_24, plain, ![X5, X6, X8, X9, X10]:(((r2_hidden(esk1_2(X5,X6),X5)|r1_xboole_0(X5,X6))&(r2_hidden(esk1_2(X5,X6),X6)|r1_xboole_0(X5,X6)))&(~r2_hidden(X10,X8)|~r2_hidden(X10,X9)|~r1_xboole_0(X8,X9))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.12/0.35  cnf(c_0_25, plain, (r1_xboole_0(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=X1), inference(rw,[status(thm)],[c_0_17, c_0_14])).
% 0.12/0.35  cnf(c_0_26, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.12/0.35  cnf(c_0_27, plain, (r2_hidden(k3_subset_1(X3,X1),X4)|~r2_hidden(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X3))|X2!=k7_setfam_1(X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.35  cnf(c_0_28, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.35  cnf(c_0_29, plain, (k7_setfam_1(X2,k7_setfam_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.35  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.35  cnf(c_0_31, negated_conjecture, (k7_setfam_1(esk3_0,esk4_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.35  fof(c_0_32, plain, ![X18]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X18)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.12/0.35  cnf(c_0_33, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.35  cnf(c_0_34, plain, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26])])).
% 0.12/0.35  cnf(c_0_35, plain, (r2_hidden(k3_subset_1(X1,X2),X3)|~m1_subset_1(k7_setfam_1(X1,X3),k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))|~r2_hidden(X2,k7_setfam_1(X1,X3))), inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_27, c_0_28])])).
% 0.12/0.35  cnf(c_0_36, negated_conjecture, (k7_setfam_1(esk3_0,k1_xboole_0)=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 0.12/0.35  cnf(c_0_37, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.35  cnf(c_0_38, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.12/0.35  cnf(c_0_39, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(k3_subset_1(X1,esk2_3(X1,X2,X3)),X2)|X3=k7_setfam_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.35  cnf(c_0_40, negated_conjecture, (~r2_hidden(X1,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_30]), c_0_37])]), c_0_38])).
% 0.12/0.35  cnf(c_0_41, negated_conjecture, (X1=k1_xboole_0|r2_hidden(esk2_3(esk3_0,esk4_0,X1),X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_30]), c_0_31]), c_0_40])).
% 0.12/0.35  cnf(c_0_42, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.35  cnf(c_0_43, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_30]), c_0_42]), c_0_40]), ['proof']).
% 0.12/0.35  # SZS output end CNFRefutation
% 0.12/0.35  # Proof object total steps             : 44
% 0.12/0.35  # Proof object clause steps            : 23
% 0.12/0.35  # Proof object formula steps           : 21
% 0.12/0.35  # Proof object conjectures             : 10
% 0.12/0.35  # Proof object clause conjectures      : 7
% 0.12/0.35  # Proof object formula conjectures     : 3
% 0.12/0.35  # Proof object initial clauses used    : 13
% 0.12/0.35  # Proof object initial formulas used   : 10
% 0.12/0.35  # Proof object generating inferences   : 7
% 0.12/0.35  # Proof object simplifying inferences  : 14
% 0.12/0.35  # Training examples: 0 positive, 0 negative
% 0.12/0.35  # Parsed axioms                        : 10
% 0.12/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.35  # Initial clauses                      : 19
% 0.12/0.35  # Removed in clause preprocessing      : 1
% 0.12/0.35  # Initial clauses in saturation        : 18
% 0.12/0.35  # Processed clauses                    : 54
% 0.12/0.35  # ...of these trivial                  : 0
% 0.12/0.35  # ...subsumed                          : 2
% 0.12/0.35  # ...remaining for further processing  : 52
% 0.12/0.35  # Other redundant clauses eliminated   : 4
% 0.12/0.35  # Clauses deleted for lack of memory   : 0
% 0.12/0.35  # Backward-subsumed                    : 0
% 0.12/0.35  # Backward-rewritten                   : 0
% 0.12/0.35  # Generated clauses                    : 36
% 0.12/0.35  # ...of the previous two non-trivial   : 26
% 0.12/0.35  # Contextual simplify-reflections      : 1
% 0.12/0.35  # Paramodulations                      : 32
% 0.12/0.35  # Factorizations                       : 0
% 0.12/0.35  # Equation resolutions                 : 4
% 0.12/0.35  # Propositional unsat checks           : 0
% 0.12/0.35  #    Propositional check models        : 0
% 0.12/0.35  #    Propositional check unsatisfiable : 0
% 0.12/0.35  #    Propositional clauses             : 0
% 0.12/0.35  #    Propositional clauses after purity: 0
% 0.12/0.35  #    Propositional unsat core size     : 0
% 0.12/0.35  #    Propositional preprocessing time  : 0.000
% 0.12/0.35  #    Propositional encoding time       : 0.000
% 0.12/0.35  #    Propositional solver time         : 0.000
% 0.12/0.35  #    Success case prop preproc time    : 0.000
% 0.12/0.35  #    Success case prop encoding time   : 0.000
% 0.12/0.35  #    Success case prop solver time     : 0.000
% 0.12/0.35  # Current number of processed clauses  : 32
% 0.12/0.35  #    Positive orientable unit clauses  : 11
% 0.12/0.35  #    Positive unorientable unit clauses: 0
% 0.12/0.35  #    Negative unit clauses             : 3
% 0.12/0.35  #    Non-unit-clauses                  : 18
% 0.12/0.35  # Current number of unprocessed clauses: 8
% 0.12/0.35  # ...number of literals in the above   : 21
% 0.12/0.35  # Current number of archived formulas  : 0
% 0.12/0.35  # Current number of archived clauses   : 19
% 0.12/0.35  # Clause-clause subsumption calls (NU) : 77
% 0.12/0.35  # Rec. Clause-clause subsumption calls : 30
% 0.12/0.35  # Non-unit clause-clause subsumptions  : 1
% 0.12/0.35  # Unit Clause-clause subsumption calls : 14
% 0.12/0.35  # Rewrite failures with RHS unbound    : 0
% 0.12/0.35  # BW rewrite match attempts            : 2
% 0.12/0.35  # BW rewrite match successes           : 0
% 0.12/0.35  # Condensation attempts                : 0
% 0.12/0.35  # Condensation successes               : 0
% 0.12/0.35  # Termbank termtop insertions          : 2159
% 0.12/0.35  
% 0.12/0.35  # -------------------------------------------------
% 0.12/0.35  # User time                : 0.027 s
% 0.12/0.35  # System time              : 0.006 s
% 0.12/0.35  # Total time               : 0.033 s
% 0.12/0.35  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
