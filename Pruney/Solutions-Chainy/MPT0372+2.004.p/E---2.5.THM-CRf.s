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
% DateTime   : Thu Dec  3 10:46:48 EST 2020

% Result     : Theorem 53.18s
% Output     : CNFRefutation 53.18s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 276 expanded)
%              Number of clauses        :   30 ( 118 expanded)
%              Number of leaves         :    7 (  67 expanded)
%              Depth                    :   11
%              Number of atoms          :  153 (1107 expanded)
%              Number of equality atoms :   29 ( 247 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t53_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => ~ ( r2_hidden(X4,X2)
                  <=> r2_hidden(X4,X3) ) )
           => X2 = k3_subset_1(X1,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(c_0_7,plain,(
    ! [X22,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(X22))
      | k3_subset_1(X22,X23) = k4_xboole_0(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_8,plain,(
    ! [X18,X19] : k4_xboole_0(X18,X19) = k5_xboole_0(X18,k3_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_9,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15,X16] :
      ( ( r2_hidden(X12,X9)
        | ~ r2_hidden(X12,X11)
        | X11 != k4_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X12,X10)
        | ~ r2_hidden(X12,X11)
        | X11 != k4_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X13,X9)
        | r2_hidden(X13,X10)
        | r2_hidden(X13,X11)
        | X11 != k4_xboole_0(X9,X10) )
      & ( ~ r2_hidden(esk2_3(X14,X15,X16),X16)
        | ~ r2_hidden(esk2_3(X14,X15,X16),X14)
        | r2_hidden(esk2_3(X14,X15,X16),X15)
        | X16 = k4_xboole_0(X14,X15) )
      & ( r2_hidden(esk2_3(X14,X15,X16),X14)
        | r2_hidden(esk2_3(X14,X15,X16),X16)
        | X16 = k4_xboole_0(X14,X15) )
      & ( ~ r2_hidden(esk2_3(X14,X15,X16),X15)
        | r2_hidden(esk2_3(X14,X15,X16),X16)
        | X16 = k4_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( ! [X4] :
                  ( m1_subset_1(X4,X1)
                 => ~ ( r2_hidden(X4,X2)
                    <=> r2_hidden(X4,X3) ) )
             => X2 = k3_subset_1(X1,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t53_subset_1])).

fof(c_0_11,plain,(
    ! [X20,X21] :
      ( ( ~ m1_subset_1(X21,X20)
        | r2_hidden(X21,X20)
        | v1_xboole_0(X20) )
      & ( ~ r2_hidden(X21,X20)
        | m1_subset_1(X21,X20)
        | v1_xboole_0(X20) )
      & ( ~ m1_subset_1(X21,X20)
        | v1_xboole_0(X21)
        | ~ v1_xboole_0(X20) )
      & ( ~ v1_xboole_0(X21)
        | m1_subset_1(X21,X20)
        | ~ v1_xboole_0(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_12,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_13,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_16,negated_conjecture,(
    ! [X30] :
      ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))
      & m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))
      & ( ~ r2_hidden(X30,esk4_0)
        | ~ r2_hidden(X30,esk5_0)
        | ~ m1_subset_1(X30,esk3_0) )
      & ( r2_hidden(X30,esk4_0)
        | r2_hidden(X30,esk5_0)
        | ~ m1_subset_1(X30,esk3_0) )
      & esk4_0 != k3_subset_1(esk3_0,esk5_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])])).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_15,c_0_14])).

fof(c_0_21,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(X24))
      | ~ r2_hidden(X26,X25)
      | r2_hidden(X26,X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_22,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | r2_hidden(X1,esk5_0)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( X1 = k3_subset_1(X2,X3)
    | r2_hidden(esk2_3(X2,X3,X1),X1)
    | r2_hidden(esk2_3(X2,X3,X1),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_22,c_0_14])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( esk4_0 != k3_subset_1(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_32,negated_conjecture,
    ( X1 = k3_subset_1(esk3_0,esk5_0)
    | r2_hidden(esk2_3(esk3_0,esk5_0,X1),esk3_0)
    | r2_hidden(esk2_3(esk3_0,esk5_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = esk4_0
    | r2_hidden(esk2_3(X1,X2,esk4_0),esk5_0)
    | r2_hidden(esk2_3(X1,X2,esk4_0),X2)
    | ~ r2_hidden(esk2_3(X1,X2,esk4_0),esk3_0)
    | ~ r2_hidden(esk2_3(X1,X2,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,esk5_0,esk4_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32])]),c_0_33])).

cnf(c_0_36,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_37,negated_conjecture,
    ( k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk5_0)) = esk4_0
    | r2_hidden(esk2_3(esk3_0,esk5_0,esk4_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_35])])).

cnf(c_0_38,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_36,c_0_14])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,esk5_0,esk4_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_37]),c_0_26])]),c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( ~ r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk5_0)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_41,negated_conjecture,
    ( k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk5_0)) = esk4_0
    | r2_hidden(esk2_3(esk3_0,esk5_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( ~ r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_24])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,esk5_0,esk4_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_41]),c_0_26])]),c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_39]),c_0_35])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n021.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 19:30:34 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 53.18/53.36  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 53.18/53.36  # and selection function SelectMaxLComplexAvoidPosPred.
% 53.18/53.36  #
% 53.18/53.36  # Preprocessing time       : 0.028 s
% 53.18/53.36  
% 53.18/53.36  # Proof found!
% 53.18/53.36  # SZS status Theorem
% 53.18/53.36  # SZS output start CNFRefutation
% 53.18/53.36  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 53.18/53.36  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 53.18/53.36  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 53.18/53.36  fof(t53_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>~((r2_hidden(X4,X2)<=>r2_hidden(X4,X3))))=>X2=k3_subset_1(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_subset_1)).
% 53.18/53.36  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 53.18/53.36  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 53.18/53.36  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 53.18/53.36  fof(c_0_7, plain, ![X22, X23]:(~m1_subset_1(X23,k1_zfmisc_1(X22))|k3_subset_1(X22,X23)=k4_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 53.18/53.36  fof(c_0_8, plain, ![X18, X19]:k4_xboole_0(X18,X19)=k5_xboole_0(X18,k3_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 53.18/53.36  fof(c_0_9, plain, ![X9, X10, X11, X12, X13, X14, X15, X16]:((((r2_hidden(X12,X9)|~r2_hidden(X12,X11)|X11!=k4_xboole_0(X9,X10))&(~r2_hidden(X12,X10)|~r2_hidden(X12,X11)|X11!=k4_xboole_0(X9,X10)))&(~r2_hidden(X13,X9)|r2_hidden(X13,X10)|r2_hidden(X13,X11)|X11!=k4_xboole_0(X9,X10)))&((~r2_hidden(esk2_3(X14,X15,X16),X16)|(~r2_hidden(esk2_3(X14,X15,X16),X14)|r2_hidden(esk2_3(X14,X15,X16),X15))|X16=k4_xboole_0(X14,X15))&((r2_hidden(esk2_3(X14,X15,X16),X14)|r2_hidden(esk2_3(X14,X15,X16),X16)|X16=k4_xboole_0(X14,X15))&(~r2_hidden(esk2_3(X14,X15,X16),X15)|r2_hidden(esk2_3(X14,X15,X16),X16)|X16=k4_xboole_0(X14,X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 53.18/53.36  fof(c_0_10, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>~((r2_hidden(X4,X2)<=>r2_hidden(X4,X3))))=>X2=k3_subset_1(X1,X3))))), inference(assume_negation,[status(cth)],[t53_subset_1])).
% 53.18/53.36  fof(c_0_11, plain, ![X20, X21]:(((~m1_subset_1(X21,X20)|r2_hidden(X21,X20)|v1_xboole_0(X20))&(~r2_hidden(X21,X20)|m1_subset_1(X21,X20)|v1_xboole_0(X20)))&((~m1_subset_1(X21,X20)|v1_xboole_0(X21)|~v1_xboole_0(X20))&(~v1_xboole_0(X21)|m1_subset_1(X21,X20)|~v1_xboole_0(X20)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 53.18/53.36  fof(c_0_12, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 53.18/53.36  cnf(c_0_13, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 53.18/53.36  cnf(c_0_14, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 53.18/53.36  cnf(c_0_15, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 53.18/53.36  fof(c_0_16, negated_conjecture, ![X30]:(m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))&(((~r2_hidden(X30,esk4_0)|~r2_hidden(X30,esk5_0)|~m1_subset_1(X30,esk3_0))&(r2_hidden(X30,esk4_0)|r2_hidden(X30,esk5_0)|~m1_subset_1(X30,esk3_0)))&esk4_0!=k3_subset_1(esk3_0,esk5_0)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])])).
% 53.18/53.36  cnf(c_0_17, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 53.18/53.36  cnf(c_0_18, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 53.18/53.36  cnf(c_0_19, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 53.18/53.36  cnf(c_0_20, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_15, c_0_14])).
% 53.18/53.36  fof(c_0_21, plain, ![X24, X25, X26]:(~m1_subset_1(X25,k1_zfmisc_1(X24))|(~r2_hidden(X26,X25)|r2_hidden(X26,X24))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 53.18/53.36  cnf(c_0_22, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 53.18/53.36  cnf(c_0_23, negated_conjecture, (r2_hidden(X1,esk4_0)|r2_hidden(X1,esk5_0)|~m1_subset_1(X1,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 53.18/53.36  cnf(c_0_24, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_17, c_0_18])).
% 53.18/53.36  cnf(c_0_25, plain, (X1=k3_subset_1(X2,X3)|r2_hidden(esk2_3(X2,X3,X1),X1)|r2_hidden(esk2_3(X2,X3,X1),X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 53.18/53.36  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 53.18/53.36  cnf(c_0_27, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 53.18/53.36  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 53.18/53.36  cnf(c_0_29, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_22, c_0_14])).
% 53.18/53.36  cnf(c_0_30, negated_conjecture, (r2_hidden(X1,esk4_0)|r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 53.18/53.36  cnf(c_0_31, negated_conjecture, (esk4_0!=k3_subset_1(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 53.18/53.36  cnf(c_0_32, negated_conjecture, (X1=k3_subset_1(esk3_0,esk5_0)|r2_hidden(esk2_3(esk3_0,esk5_0,X1),esk3_0)|r2_hidden(esk2_3(esk3_0,esk5_0,X1),X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 53.18/53.36  cnf(c_0_33, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 53.18/53.36  cnf(c_0_34, negated_conjecture, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=esk4_0|r2_hidden(esk2_3(X1,X2,esk4_0),esk5_0)|r2_hidden(esk2_3(X1,X2,esk4_0),X2)|~r2_hidden(esk2_3(X1,X2,esk4_0),esk3_0)|~r2_hidden(esk2_3(X1,X2,esk4_0),X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 53.18/53.36  cnf(c_0_35, negated_conjecture, (r2_hidden(esk2_3(esk3_0,esk5_0,esk4_0),esk3_0)), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32])]), c_0_33])).
% 53.18/53.36  cnf(c_0_36, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 53.18/53.36  cnf(c_0_37, negated_conjecture, (k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk5_0))=esk4_0|r2_hidden(esk2_3(esk3_0,esk5_0,esk4_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_35])])).
% 53.18/53.36  cnf(c_0_38, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_36, c_0_14])).
% 53.18/53.36  cnf(c_0_39, negated_conjecture, (r2_hidden(esk2_3(esk3_0,esk5_0,esk4_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_37]), c_0_26])]), c_0_31])).
% 53.18/53.36  cnf(c_0_40, negated_conjecture, (~r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk5_0)|~m1_subset_1(X1,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 53.18/53.36  cnf(c_0_41, negated_conjecture, (k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk5_0))=esk4_0|r2_hidden(esk2_3(esk3_0,esk5_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 53.18/53.36  cnf(c_0_42, negated_conjecture, (~r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_40, c_0_24])).
% 53.18/53.36  cnf(c_0_43, negated_conjecture, (r2_hidden(esk2_3(esk3_0,esk5_0,esk4_0),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_41]), c_0_26])]), c_0_31])).
% 53.18/53.36  cnf(c_0_44, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_39]), c_0_35])]), ['proof']).
% 53.18/53.36  # SZS output end CNFRefutation
% 53.18/53.36  # Proof object total steps             : 45
% 53.18/53.36  # Proof object clause steps            : 30
% 53.18/53.36  # Proof object formula steps           : 15
% 53.18/53.36  # Proof object conjectures             : 19
% 53.18/53.36  # Proof object clause conjectures      : 16
% 53.18/53.36  # Proof object formula conjectures     : 3
% 53.18/53.36  # Proof object initial clauses used    : 13
% 53.18/53.36  # Proof object initial formulas used   : 7
% 53.18/53.36  # Proof object generating inferences   : 12
% 53.18/53.36  # Proof object simplifying inferences  : 18
% 53.18/53.36  # Training examples: 0 positive, 0 negative
% 53.18/53.36  # Parsed axioms                        : 7
% 53.18/53.36  # Removed by relevancy pruning/SinE    : 0
% 53.18/53.36  # Initial clauses                      : 20
% 53.18/53.36  # Removed in clause preprocessing      : 1
% 53.18/53.36  # Initial clauses in saturation        : 19
% 53.18/53.36  # Processed clauses                    : 35333
% 53.18/53.36  # ...of these trivial                  : 198
% 53.18/53.36  # ...subsumed                          : 31138
% 53.18/53.36  # ...remaining for further processing  : 3997
% 53.18/53.36  # Other redundant clauses eliminated   : 28
% 53.18/53.36  # Clauses deleted for lack of memory   : 100036
% 53.18/53.36  # Backward-subsumed                    : 948
% 53.18/53.36  # Backward-rewritten                   : 820
% 53.18/53.36  # Generated clauses                    : 2475487
% 53.18/53.36  # ...of the previous two non-trivial   : 2421709
% 53.18/53.36  # Contextual simplify-reflections      : 330
% 53.18/53.36  # Paramodulations                      : 2474483
% 53.18/53.36  # Factorizations                       : 896
% 53.18/53.36  # Equation resolutions                 : 28
% 53.18/53.36  # Propositional unsat checks           : 0
% 53.18/53.36  #    Propositional check models        : 0
% 53.18/53.36  #    Propositional check unsatisfiable : 0
% 53.18/53.36  #    Propositional clauses             : 0
% 53.18/53.36  #    Propositional clauses after purity: 0
% 53.18/53.36  #    Propositional unsat core size     : 0
% 53.18/53.36  #    Propositional preprocessing time  : 0.000
% 53.18/53.36  #    Propositional encoding time       : 0.000
% 53.18/53.36  #    Propositional solver time         : 0.000
% 53.18/53.36  #    Success case prop preproc time    : 0.000
% 53.18/53.36  #    Success case prop encoding time   : 0.000
% 53.18/53.36  #    Success case prop solver time     : 0.000
% 53.18/53.36  # Current number of processed clauses  : 2146
% 53.18/53.36  #    Positive orientable unit clauses  : 75
% 53.18/53.36  #    Positive unorientable unit clauses: 2
% 53.18/53.36  #    Negative unit clauses             : 16
% 53.18/53.36  #    Non-unit-clauses                  : 2053
% 53.18/53.36  # Current number of unprocessed clauses: 1446067
% 53.18/53.36  # ...number of literals in the above   : 9376740
% 53.18/53.36  # Current number of archived formulas  : 0
% 53.18/53.36  # Current number of archived clauses   : 1849
% 53.18/53.36  # Clause-clause subsumption calls (NU) : 1995195
% 53.18/53.36  # Rec. Clause-clause subsumption calls : 815359
% 53.18/53.36  # Non-unit clause-clause subsumptions  : 27688
% 53.18/53.36  # Unit Clause-clause subsumption calls : 27510
% 53.18/53.36  # Rewrite failures with RHS unbound    : 38
% 53.18/53.36  # BW rewrite match attempts            : 913
% 53.18/53.36  # BW rewrite match successes           : 75
% 53.18/53.36  # Condensation attempts                : 0
% 53.18/53.36  # Condensation successes               : 0
% 53.18/53.36  # Termbank termtop insertions          : 102433501
% 53.25/53.45  
% 53.25/53.45  # -------------------------------------------------
% 53.25/53.45  # User time                : 52.126 s
% 53.25/53.45  # System time              : 0.997 s
% 53.25/53.45  # Total time               : 53.122 s
% 53.25/53.45  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
