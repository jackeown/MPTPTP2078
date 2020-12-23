%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:12:55 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   28 (  55 expanded)
%              Number of clauses        :   15 (  22 expanded)
%              Number of leaves         :    6 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :   95 ( 196 expanded)
%              Number of equality atoms :   39 ( 112 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(t10_tops_2,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( ~ ( X2 != k1_xboole_0
            & k7_setfam_1(X1,X2) = k1_xboole_0 )
        & ~ ( k7_setfam_1(X1,X2) != k1_xboole_0
            & X2 = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tops_2)).

fof(t46_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ~ ( X2 != k1_xboole_0
          & k7_setfam_1(X1,X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_6,plain,(
    ! [X7,X8,X9,X10] :
      ( ( ~ r2_hidden(X10,X9)
        | r2_hidden(k3_subset_1(X7,X10),X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(X7))
        | X9 != k7_setfam_1(X7,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X7)))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(X7))) )
      & ( ~ r2_hidden(k3_subset_1(X7,X10),X8)
        | r2_hidden(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(X7))
        | X9 != k7_setfam_1(X7,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X7)))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(X7))) )
      & ( m1_subset_1(esk1_3(X7,X8,X9),k1_zfmisc_1(X7))
        | X9 = k7_setfam_1(X7,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X7)))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(X7))) )
      & ( ~ r2_hidden(esk1_3(X7,X8,X9),X9)
        | ~ r2_hidden(k3_subset_1(X7,esk1_3(X7,X8,X9)),X8)
        | X9 = k7_setfam_1(X7,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X7)))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(X7))) )
      & ( r2_hidden(esk1_3(X7,X8,X9),X9)
        | r2_hidden(k3_subset_1(X7,esk1_3(X7,X8,X9)),X8)
        | X9 = k7_setfam_1(X7,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X7)))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(X7))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_setfam_1])])])])])).

fof(c_0_7,plain,(
    ! [X6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X6)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ( ~ ( X2 != k1_xboole_0
              & k7_setfam_1(X1,X2) = k1_xboole_0 )
          & ~ ( k7_setfam_1(X1,X2) != k1_xboole_0
              & X2 = k1_xboole_0 ) ) ) ),
    inference(assume_negation,[status(cth)],[t10_tops_2])).

cnf(c_0_9,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(k3_subset_1(X1,esk1_3(X1,X2,X3)),X2)
    | X3 = k7_setfam_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(X12)))
      | X13 = k1_xboole_0
      | k7_setfam_1(X12,X13) != k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_setfam_1])])).

fof(c_0_12,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))
    & ( k7_setfam_1(esk2_0,esk3_0) != k1_xboole_0
      | esk3_0 != k1_xboole_0 )
    & ( esk3_0 = k1_xboole_0
      | esk3_0 != k1_xboole_0 )
    & ( k7_setfam_1(esk2_0,esk3_0) != k1_xboole_0
      | k7_setfam_1(esk2_0,esk3_0) = k1_xboole_0 )
    & ( esk3_0 = k1_xboole_0
      | k7_setfam_1(esk2_0,esk3_0) = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).

fof(c_0_13,plain,(
    ! [X17,X18] :
      ( ~ r2_hidden(X17,X18)
      | ~ r1_tarski(X18,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_14,plain,
    ( k7_setfam_1(X1,X2) = k1_xboole_0
    | r2_hidden(k3_subset_1(X1,esk1_3(X1,X2,k1_xboole_0)),X2)
    | r2_hidden(esk1_3(X1,X2,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

fof(c_0_15,plain,(
    ! [X5] : r1_tarski(k1_xboole_0,X5) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_16,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | k7_setfam_1(X2,X1) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | k7_setfam_1(esk2_0,esk3_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k7_setfam_1(X1,k1_xboole_0) = k1_xboole_0
    | r2_hidden(k3_subset_1(X1,esk1_3(X1,k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(esk1_3(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_10])).

cnf(c_0_21,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( k7_setfam_1(esk2_0,esk3_0) != k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_24,plain,
    ( k7_setfam_1(X1,k1_xboole_0) = k1_xboole_0
    | r2_hidden(esk1_3(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_25,negated_conjecture,
    ( k7_setfam_1(esk2_0,k1_xboole_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_23])])).

cnf(c_0_26,plain,
    ( k7_setfam_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_24]),c_0_21])])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:47:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S0U
% 0.14/0.38  # and selection function SelectComplexExceptRRHorn.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.027 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(d8_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(X3=k7_setfam_1(X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>(r2_hidden(X4,X3)<=>r2_hidden(k3_subset_1(X1,X4),X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_setfam_1)).
% 0.14/0.38  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.14/0.38  fof(t10_tops_2, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(~((X2!=k1_xboole_0&k7_setfam_1(X1,X2)=k1_xboole_0))&~((k7_setfam_1(X1,X2)!=k1_xboole_0&X2=k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_tops_2)).
% 0.14/0.38  fof(t46_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>~((X2!=k1_xboole_0&k7_setfam_1(X1,X2)=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_setfam_1)).
% 0.14/0.38  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.14/0.38  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.14/0.38  fof(c_0_6, plain, ![X7, X8, X9, X10]:(((~r2_hidden(X10,X9)|r2_hidden(k3_subset_1(X7,X10),X8)|~m1_subset_1(X10,k1_zfmisc_1(X7))|X9!=k7_setfam_1(X7,X8)|~m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X7)))|~m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(X7))))&(~r2_hidden(k3_subset_1(X7,X10),X8)|r2_hidden(X10,X9)|~m1_subset_1(X10,k1_zfmisc_1(X7))|X9!=k7_setfam_1(X7,X8)|~m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X7)))|~m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(X7)))))&((m1_subset_1(esk1_3(X7,X8,X9),k1_zfmisc_1(X7))|X9=k7_setfam_1(X7,X8)|~m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X7)))|~m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(X7))))&((~r2_hidden(esk1_3(X7,X8,X9),X9)|~r2_hidden(k3_subset_1(X7,esk1_3(X7,X8,X9)),X8)|X9=k7_setfam_1(X7,X8)|~m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X7)))|~m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(X7))))&(r2_hidden(esk1_3(X7,X8,X9),X9)|r2_hidden(k3_subset_1(X7,esk1_3(X7,X8,X9)),X8)|X9=k7_setfam_1(X7,X8)|~m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X7)))|~m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(X7))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_setfam_1])])])])])).
% 0.14/0.38  fof(c_0_7, plain, ![X6]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X6)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.14/0.38  fof(c_0_8, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(~((X2!=k1_xboole_0&k7_setfam_1(X1,X2)=k1_xboole_0))&~((k7_setfam_1(X1,X2)!=k1_xboole_0&X2=k1_xboole_0))))), inference(assume_negation,[status(cth)],[t10_tops_2])).
% 0.14/0.38  cnf(c_0_9, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(k3_subset_1(X1,esk1_3(X1,X2,X3)),X2)|X3=k7_setfam_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.38  cnf(c_0_10, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  fof(c_0_11, plain, ![X12, X13]:(~m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(X12)))|(X13=k1_xboole_0|k7_setfam_1(X12,X13)!=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_setfam_1])])).
% 0.14/0.38  fof(c_0_12, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))&(((k7_setfam_1(esk2_0,esk3_0)!=k1_xboole_0|esk3_0!=k1_xboole_0)&(esk3_0=k1_xboole_0|esk3_0!=k1_xboole_0))&((k7_setfam_1(esk2_0,esk3_0)!=k1_xboole_0|k7_setfam_1(esk2_0,esk3_0)=k1_xboole_0)&(esk3_0=k1_xboole_0|k7_setfam_1(esk2_0,esk3_0)=k1_xboole_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).
% 0.14/0.38  fof(c_0_13, plain, ![X17, X18]:(~r2_hidden(X17,X18)|~r1_tarski(X18,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.14/0.38  cnf(c_0_14, plain, (k7_setfam_1(X1,X2)=k1_xboole_0|r2_hidden(k3_subset_1(X1,esk1_3(X1,X2,k1_xboole_0)),X2)|r2_hidden(esk1_3(X1,X2,k1_xboole_0),k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.14/0.38  fof(c_0_15, plain, ![X5]:r1_tarski(k1_xboole_0,X5), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.14/0.38  cnf(c_0_16, plain, (X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))|k7_setfam_1(X2,X1)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_18, negated_conjecture, (esk3_0=k1_xboole_0|k7_setfam_1(esk2_0,esk3_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_19, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_20, plain, (k7_setfam_1(X1,k1_xboole_0)=k1_xboole_0|r2_hidden(k3_subset_1(X1,esk1_3(X1,k1_xboole_0,k1_xboole_0)),k1_xboole_0)|r2_hidden(esk1_3(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_14, c_0_10])).
% 0.14/0.38  cnf(c_0_21, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_22, negated_conjecture, (k7_setfam_1(esk2_0,esk3_0)!=k1_xboole_0|esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_23, negated_conjecture, (esk3_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])).
% 0.14/0.38  cnf(c_0_24, plain, (k7_setfam_1(X1,k1_xboole_0)=k1_xboole_0|r2_hidden(esk1_3(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 0.14/0.38  cnf(c_0_25, negated_conjecture, (k7_setfam_1(esk2_0,k1_xboole_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_23])])).
% 0.14/0.38  cnf(c_0_26, plain, (k7_setfam_1(X1,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_24]), c_0_21])])).
% 0.14/0.38  cnf(c_0_27, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26])]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 28
% 0.14/0.38  # Proof object clause steps            : 15
% 0.14/0.38  # Proof object formula steps           : 13
% 0.14/0.38  # Proof object conjectures             : 9
% 0.14/0.38  # Proof object clause conjectures      : 6
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 8
% 0.14/0.38  # Proof object initial formulas used   : 6
% 0.14/0.38  # Proof object generating inferences   : 5
% 0.14/0.38  # Proof object simplifying inferences  : 10
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 7
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 15
% 0.14/0.38  # Removed in clause preprocessing      : 2
% 0.14/0.38  # Initial clauses in saturation        : 13
% 0.14/0.38  # Processed clauses                    : 64
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 8
% 0.14/0.38  # ...remaining for further processing  : 56
% 0.14/0.38  # Other redundant clauses eliminated   : 2
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 1
% 0.14/0.38  # Backward-rewritten                   : 16
% 0.14/0.38  # Generated clauses                    : 95
% 0.14/0.38  # ...of the previous two non-trivial   : 93
% 0.14/0.38  # Contextual simplify-reflections      : 2
% 0.14/0.38  # Paramodulations                      : 93
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 2
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 24
% 0.14/0.38  #    Positive orientable unit clauses  : 4
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 0
% 0.14/0.38  #    Non-unit-clauses                  : 20
% 0.14/0.38  # Current number of unprocessed clauses: 47
% 0.14/0.38  # ...number of literals in the above   : 209
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 30
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 213
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 130
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 11
% 0.14/0.38  # Unit Clause-clause subsumption calls : 3
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 7
% 0.14/0.38  # BW rewrite match successes           : 7
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 3547
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.030 s
% 0.14/0.38  # System time              : 0.005 s
% 0.14/0.38  # Total time               : 0.035 s
% 0.14/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
