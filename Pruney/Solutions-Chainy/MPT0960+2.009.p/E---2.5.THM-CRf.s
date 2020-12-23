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
% DateTime   : Thu Dec  3 11:00:48 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   34 (  57 expanded)
%              Number of clauses        :   17 (  26 expanded)
%              Number of leaves         :    8 (  15 expanded)
%              Depth                    :    9
%              Number of atoms          :   92 ( 158 expanded)
%              Number of equality atoms :   24 (  45 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   33 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_wellord2,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k1_wellord2(X1)
      <=> ( k3_relat_1(X2) = X1
          & ! [X3,X4] :
              ( ( r2_hidden(X3,X1)
                & r2_hidden(X4,X1) )
             => ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> r1_tarski(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(t33_wellord2,conjecture,(
    ! [X1] : r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_wellord2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(c_0_8,plain,(
    ! [X15,X16,X17,X18] :
      ( ( k3_relat_1(X16) = X15
        | X16 != k1_wellord2(X15)
        | ~ v1_relat_1(X16) )
      & ( ~ r2_hidden(k4_tarski(X17,X18),X16)
        | r1_tarski(X17,X18)
        | ~ r2_hidden(X17,X15)
        | ~ r2_hidden(X18,X15)
        | X16 != k1_wellord2(X15)
        | ~ v1_relat_1(X16) )
      & ( ~ r1_tarski(X17,X18)
        | r2_hidden(k4_tarski(X17,X18),X16)
        | ~ r2_hidden(X17,X15)
        | ~ r2_hidden(X18,X15)
        | X16 != k1_wellord2(X15)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(esk1_2(X15,X16),X15)
        | k3_relat_1(X16) != X15
        | X16 = k1_wellord2(X15)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(esk2_2(X15,X16),X15)
        | k3_relat_1(X16) != X15
        | X16 = k1_wellord2(X15)
        | ~ v1_relat_1(X16) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X15,X16),esk2_2(X15,X16)),X16)
        | ~ r1_tarski(esk1_2(X15,X16),esk2_2(X15,X16))
        | k3_relat_1(X16) != X15
        | X16 = k1_wellord2(X15)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(k4_tarski(esk1_2(X15,X16),esk2_2(X15,X16)),X16)
        | r1_tarski(esk1_2(X15,X16),esk2_2(X15,X16))
        | k3_relat_1(X16) != X15
        | X16 = k1_wellord2(X15)
        | ~ v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).

fof(c_0_9,plain,(
    ! [X21] : v1_relat_1(k1_wellord2(X21)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_10,plain,(
    ! [X11] :
      ( ~ v1_relat_1(X11)
      | k3_relat_1(X11) = k2_xboole_0(k1_relat_1(X11),k2_relat_1(X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

cnf(c_0_11,plain,
    ( k3_relat_1(X1) = X2
    | X1 != k1_wellord2(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X7,X8] : r1_tarski(X7,k2_xboole_0(X7,X8)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_14,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k3_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_11]),c_0_12])])).

fof(c_0_16,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_17,plain,(
    ! [X12,X13,X14] :
      ( ~ v1_relat_1(X14)
      | ~ r1_tarski(k1_relat_1(X14),X12)
      | ~ r1_tarski(k2_relat_1(X14),X13)
      | m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k2_xboole_0(k1_relat_1(k1_wellord2(X1)),k2_relat_1(k1_wellord2(X1))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_12]),c_0_15])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( r1_tarski(k1_relat_1(k1_wellord2(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_20])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1] : r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1)) ),
    inference(assume_negation,[status(cth)],[t33_wellord2])).

fof(c_0_25,plain,(
    ! [X9,X10] :
      ( ( ~ m1_subset_1(X9,k1_zfmisc_1(X10))
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | m1_subset_1(X9,k1_zfmisc_1(X10)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_26,plain,
    ( m1_subset_1(k1_wellord2(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(k1_wellord2(X1)),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_12])])).

cnf(c_0_27,plain,
    ( r1_tarski(k2_relat_1(k1_wellord2(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_19])).

fof(c_0_28,negated_conjecture,(
    ~ r1_tarski(k1_wellord2(esk3_0),k2_zfmisc_1(esk3_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( m1_subset_1(k1_wellord2(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( ~ r1_tarski(k1_wellord2(esk3_0),k2_zfmisc_1(esk3_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,plain,
    ( r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:57:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.37  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 0.21/0.37  # and selection function SelectDiffNegLit.
% 0.21/0.37  #
% 0.21/0.37  # Preprocessing time       : 0.027 s
% 0.21/0.37  # Presaturation interreduction done
% 0.21/0.37  
% 0.21/0.37  # Proof found!
% 0.21/0.37  # SZS status Theorem
% 0.21/0.37  # SZS output start CNFRefutation
% 0.21/0.37  fof(d1_wellord2, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k1_wellord2(X1)<=>(k3_relat_1(X2)=X1&![X3, X4]:((r2_hidden(X3,X1)&r2_hidden(X4,X1))=>(r2_hidden(k4_tarski(X3,X4),X2)<=>r1_tarski(X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 0.21/0.37  fof(dt_k1_wellord2, axiom, ![X1]:v1_relat_1(k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 0.21/0.37  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 0.21/0.37  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.21/0.37  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.21/0.37  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 0.21/0.37  fof(t33_wellord2, conjecture, ![X1]:r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_wellord2)).
% 0.21/0.37  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.21/0.37  fof(c_0_8, plain, ![X15, X16, X17, X18]:(((k3_relat_1(X16)=X15|X16!=k1_wellord2(X15)|~v1_relat_1(X16))&((~r2_hidden(k4_tarski(X17,X18),X16)|r1_tarski(X17,X18)|(~r2_hidden(X17,X15)|~r2_hidden(X18,X15))|X16!=k1_wellord2(X15)|~v1_relat_1(X16))&(~r1_tarski(X17,X18)|r2_hidden(k4_tarski(X17,X18),X16)|(~r2_hidden(X17,X15)|~r2_hidden(X18,X15))|X16!=k1_wellord2(X15)|~v1_relat_1(X16))))&(((r2_hidden(esk1_2(X15,X16),X15)|k3_relat_1(X16)!=X15|X16=k1_wellord2(X15)|~v1_relat_1(X16))&(r2_hidden(esk2_2(X15,X16),X15)|k3_relat_1(X16)!=X15|X16=k1_wellord2(X15)|~v1_relat_1(X16)))&((~r2_hidden(k4_tarski(esk1_2(X15,X16),esk2_2(X15,X16)),X16)|~r1_tarski(esk1_2(X15,X16),esk2_2(X15,X16))|k3_relat_1(X16)!=X15|X16=k1_wellord2(X15)|~v1_relat_1(X16))&(r2_hidden(k4_tarski(esk1_2(X15,X16),esk2_2(X15,X16)),X16)|r1_tarski(esk1_2(X15,X16),esk2_2(X15,X16))|k3_relat_1(X16)!=X15|X16=k1_wellord2(X15)|~v1_relat_1(X16))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).
% 0.21/0.37  fof(c_0_9, plain, ![X21]:v1_relat_1(k1_wellord2(X21)), inference(variable_rename,[status(thm)],[dt_k1_wellord2])).
% 0.21/0.37  fof(c_0_10, plain, ![X11]:(~v1_relat_1(X11)|k3_relat_1(X11)=k2_xboole_0(k1_relat_1(X11),k2_relat_1(X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 0.21/0.37  cnf(c_0_11, plain, (k3_relat_1(X1)=X2|X1!=k1_wellord2(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.37  cnf(c_0_12, plain, (v1_relat_1(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.37  fof(c_0_13, plain, ![X7, X8]:r1_tarski(X7,k2_xboole_0(X7,X8)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.21/0.37  cnf(c_0_14, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.37  cnf(c_0_15, plain, (k3_relat_1(k1_wellord2(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_11]), c_0_12])])).
% 0.21/0.37  fof(c_0_16, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.21/0.37  fof(c_0_17, plain, ![X12, X13, X14]:(~v1_relat_1(X14)|(~r1_tarski(k1_relat_1(X14),X12)|~r1_tarski(k2_relat_1(X14),X13)|m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.21/0.37  cnf(c_0_18, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.37  cnf(c_0_19, plain, (k2_xboole_0(k1_relat_1(k1_wellord2(X1)),k2_relat_1(k1_wellord2(X1)))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_12]), c_0_15])).
% 0.21/0.37  cnf(c_0_20, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.37  cnf(c_0_21, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.37  cnf(c_0_22, plain, (r1_tarski(k1_relat_1(k1_wellord2(X1)),X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.21/0.37  cnf(c_0_23, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_18, c_0_20])).
% 0.21/0.37  fof(c_0_24, negated_conjecture, ~(![X1]:r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1))), inference(assume_negation,[status(cth)],[t33_wellord2])).
% 0.21/0.37  fof(c_0_25, plain, ![X9, X10]:((~m1_subset_1(X9,k1_zfmisc_1(X10))|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|m1_subset_1(X9,k1_zfmisc_1(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.21/0.37  cnf(c_0_26, plain, (m1_subset_1(k1_wellord2(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r1_tarski(k2_relat_1(k1_wellord2(X1)),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_12])])).
% 0.21/0.37  cnf(c_0_27, plain, (r1_tarski(k2_relat_1(k1_wellord2(X1)),X1)), inference(spm,[status(thm)],[c_0_23, c_0_19])).
% 0.21/0.37  fof(c_0_28, negated_conjecture, ~r1_tarski(k1_wellord2(esk3_0),k2_zfmisc_1(esk3_0,esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).
% 0.21/0.37  cnf(c_0_29, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.37  cnf(c_0_30, plain, (m1_subset_1(k1_wellord2(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.21/0.37  cnf(c_0_31, negated_conjecture, (~r1_tarski(k1_wellord2(esk3_0),k2_zfmisc_1(esk3_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.37  cnf(c_0_32, plain, (r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.21/0.37  cnf(c_0_33, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32])]), ['proof']).
% 0.21/0.37  # SZS output end CNFRefutation
% 0.21/0.37  # Proof object total steps             : 34
% 0.21/0.37  # Proof object clause steps            : 17
% 0.21/0.37  # Proof object formula steps           : 17
% 0.21/0.37  # Proof object conjectures             : 5
% 0.21/0.37  # Proof object clause conjectures      : 2
% 0.21/0.37  # Proof object formula conjectures     : 3
% 0.21/0.37  # Proof object initial clauses used    : 8
% 0.21/0.37  # Proof object initial formulas used   : 8
% 0.21/0.37  # Proof object generating inferences   : 8
% 0.21/0.37  # Proof object simplifying inferences  : 7
% 0.21/0.37  # Training examples: 0 positive, 0 negative
% 0.21/0.37  # Parsed axioms                        : 8
% 0.21/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.37  # Initial clauses                      : 15
% 0.21/0.37  # Removed in clause preprocessing      : 0
% 0.21/0.37  # Initial clauses in saturation        : 15
% 0.21/0.37  # Processed clauses                    : 48
% 0.21/0.37  # ...of these trivial                  : 5
% 0.21/0.37  # ...subsumed                          : 0
% 0.21/0.37  # ...remaining for further processing  : 43
% 0.21/0.37  # Other redundant clauses eliminated   : 3
% 0.21/0.37  # Clauses deleted for lack of memory   : 0
% 0.21/0.37  # Backward-subsumed                    : 0
% 0.21/0.37  # Backward-rewritten                   : 1
% 0.21/0.37  # Generated clauses                    : 40
% 0.21/0.37  # ...of the previous two non-trivial   : 24
% 0.21/0.37  # Contextual simplify-reflections      : 0
% 0.21/0.37  # Paramodulations                      : 33
% 0.21/0.37  # Factorizations                       : 0
% 0.21/0.37  # Equation resolutions                 : 7
% 0.21/0.37  # Propositional unsat checks           : 0
% 0.21/0.37  #    Propositional check models        : 0
% 0.21/0.37  #    Propositional check unsatisfiable : 0
% 0.21/0.37  #    Propositional clauses             : 0
% 0.21/0.37  #    Propositional clauses after purity: 0
% 0.21/0.37  #    Propositional unsat core size     : 0
% 0.21/0.37  #    Propositional preprocessing time  : 0.000
% 0.21/0.37  #    Propositional encoding time       : 0.000
% 0.21/0.37  #    Propositional solver time         : 0.000
% 0.21/0.37  #    Success case prop preproc time    : 0.000
% 0.21/0.37  #    Success case prop encoding time   : 0.000
% 0.21/0.37  #    Success case prop solver time     : 0.000
% 0.21/0.37  # Current number of processed clauses  : 27
% 0.21/0.37  #    Positive orientable unit clauses  : 13
% 0.21/0.37  #    Positive unorientable unit clauses: 1
% 0.21/0.37  #    Negative unit clauses             : 0
% 0.21/0.37  #    Non-unit-clauses                  : 13
% 0.21/0.37  # Current number of unprocessed clauses: 6
% 0.21/0.37  # ...number of literals in the above   : 15
% 0.21/0.37  # Current number of archived formulas  : 0
% 0.21/0.37  # Current number of archived clauses   : 16
% 0.21/0.37  # Clause-clause subsumption calls (NU) : 82
% 0.21/0.37  # Rec. Clause-clause subsumption calls : 16
% 0.21/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.21/0.37  # Unit Clause-clause subsumption calls : 8
% 0.21/0.37  # Rewrite failures with RHS unbound    : 0
% 0.21/0.37  # BW rewrite match attempts            : 8
% 0.21/0.37  # BW rewrite match successes           : 5
% 0.21/0.37  # Condensation attempts                : 0
% 0.21/0.37  # Condensation successes               : 0
% 0.21/0.37  # Termbank termtop insertions          : 1699
% 0.21/0.37  
% 0.21/0.37  # -------------------------------------------------
% 0.21/0.37  # User time                : 0.029 s
% 0.21/0.37  # System time              : 0.004 s
% 0.21/0.37  # Total time               : 0.032 s
% 0.21/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
