%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:46:48 EST 2020

% Result     : Theorem 56.00s
% Output     : CNFRefutation 56.00s
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

fof(t52_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => ( ~ r2_hidden(X4,X2)
                <=> r2_hidden(X4,X3) ) )
           => X2 = k3_subset_1(X1,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_subset_1)).

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
                 => ( ~ r2_hidden(X4,X2)
                  <=> r2_hidden(X4,X3) ) )
             => X2 = k3_subset_1(X1,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_subset_1])).

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
      & ( r2_hidden(X30,esk4_0)
        | r2_hidden(X30,esk5_0)
        | ~ m1_subset_1(X30,esk3_0) )
      & ( ~ r2_hidden(X30,esk5_0)
        | ~ r2_hidden(X30,esk4_0)
        | ~ m1_subset_1(X30,esk3_0) )
      & esk4_0 != k3_subset_1(esk3_0,esk5_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])])).

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
    ( ~ r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk4_0)
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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:47:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 56.00/56.26  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 56.00/56.26  # and selection function SelectMaxLComplexAvoidPosPred.
% 56.00/56.26  #
% 56.00/56.26  # Preprocessing time       : 0.028 s
% 56.00/56.26  
% 56.00/56.26  # Proof found!
% 56.00/56.26  # SZS status Theorem
% 56.00/56.26  # SZS output start CNFRefutation
% 56.00/56.26  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 56.00/56.26  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 56.00/56.26  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 56.00/56.26  fof(t52_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(~(r2_hidden(X4,X2))<=>r2_hidden(X4,X3)))=>X2=k3_subset_1(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_subset_1)).
% 56.00/56.26  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 56.00/56.26  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 56.00/56.26  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 56.00/56.26  fof(c_0_7, plain, ![X22, X23]:(~m1_subset_1(X23,k1_zfmisc_1(X22))|k3_subset_1(X22,X23)=k4_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 56.00/56.26  fof(c_0_8, plain, ![X18, X19]:k4_xboole_0(X18,X19)=k5_xboole_0(X18,k3_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 56.00/56.26  fof(c_0_9, plain, ![X9, X10, X11, X12, X13, X14, X15, X16]:((((r2_hidden(X12,X9)|~r2_hidden(X12,X11)|X11!=k4_xboole_0(X9,X10))&(~r2_hidden(X12,X10)|~r2_hidden(X12,X11)|X11!=k4_xboole_0(X9,X10)))&(~r2_hidden(X13,X9)|r2_hidden(X13,X10)|r2_hidden(X13,X11)|X11!=k4_xboole_0(X9,X10)))&((~r2_hidden(esk2_3(X14,X15,X16),X16)|(~r2_hidden(esk2_3(X14,X15,X16),X14)|r2_hidden(esk2_3(X14,X15,X16),X15))|X16=k4_xboole_0(X14,X15))&((r2_hidden(esk2_3(X14,X15,X16),X14)|r2_hidden(esk2_3(X14,X15,X16),X16)|X16=k4_xboole_0(X14,X15))&(~r2_hidden(esk2_3(X14,X15,X16),X15)|r2_hidden(esk2_3(X14,X15,X16),X16)|X16=k4_xboole_0(X14,X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 56.00/56.26  fof(c_0_10, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(~(r2_hidden(X4,X2))<=>r2_hidden(X4,X3)))=>X2=k3_subset_1(X1,X3))))), inference(assume_negation,[status(cth)],[t52_subset_1])).
% 56.00/56.26  fof(c_0_11, plain, ![X20, X21]:(((~m1_subset_1(X21,X20)|r2_hidden(X21,X20)|v1_xboole_0(X20))&(~r2_hidden(X21,X20)|m1_subset_1(X21,X20)|v1_xboole_0(X20)))&((~m1_subset_1(X21,X20)|v1_xboole_0(X21)|~v1_xboole_0(X20))&(~v1_xboole_0(X21)|m1_subset_1(X21,X20)|~v1_xboole_0(X20)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 56.00/56.26  fof(c_0_12, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 56.00/56.26  cnf(c_0_13, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 56.00/56.26  cnf(c_0_14, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 56.00/56.26  cnf(c_0_15, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 56.00/56.26  fof(c_0_16, negated_conjecture, ![X30]:(m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))&(((r2_hidden(X30,esk4_0)|r2_hidden(X30,esk5_0)|~m1_subset_1(X30,esk3_0))&(~r2_hidden(X30,esk5_0)|~r2_hidden(X30,esk4_0)|~m1_subset_1(X30,esk3_0)))&esk4_0!=k3_subset_1(esk3_0,esk5_0)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])])).
% 56.00/56.26  cnf(c_0_17, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 56.00/56.26  cnf(c_0_18, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 56.00/56.26  cnf(c_0_19, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 56.00/56.26  cnf(c_0_20, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_15, c_0_14])).
% 56.00/56.26  fof(c_0_21, plain, ![X24, X25, X26]:(~m1_subset_1(X25,k1_zfmisc_1(X24))|(~r2_hidden(X26,X25)|r2_hidden(X26,X24))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 56.00/56.26  cnf(c_0_22, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 56.00/56.26  cnf(c_0_23, negated_conjecture, (r2_hidden(X1,esk4_0)|r2_hidden(X1,esk5_0)|~m1_subset_1(X1,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 56.00/56.26  cnf(c_0_24, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_17, c_0_18])).
% 56.00/56.26  cnf(c_0_25, plain, (X1=k3_subset_1(X2,X3)|r2_hidden(esk2_3(X2,X3,X1),X1)|r2_hidden(esk2_3(X2,X3,X1),X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 56.00/56.26  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 56.00/56.26  cnf(c_0_27, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 56.00/56.26  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 56.00/56.26  cnf(c_0_29, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_22, c_0_14])).
% 56.00/56.26  cnf(c_0_30, negated_conjecture, (r2_hidden(X1,esk4_0)|r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 56.00/56.26  cnf(c_0_31, negated_conjecture, (esk4_0!=k3_subset_1(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 56.00/56.26  cnf(c_0_32, negated_conjecture, (X1=k3_subset_1(esk3_0,esk5_0)|r2_hidden(esk2_3(esk3_0,esk5_0,X1),esk3_0)|r2_hidden(esk2_3(esk3_0,esk5_0,X1),X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 56.00/56.26  cnf(c_0_33, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 56.00/56.26  cnf(c_0_34, negated_conjecture, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=esk4_0|r2_hidden(esk2_3(X1,X2,esk4_0),esk5_0)|r2_hidden(esk2_3(X1,X2,esk4_0),X2)|~r2_hidden(esk2_3(X1,X2,esk4_0),esk3_0)|~r2_hidden(esk2_3(X1,X2,esk4_0),X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 56.00/56.26  cnf(c_0_35, negated_conjecture, (r2_hidden(esk2_3(esk3_0,esk5_0,esk4_0),esk3_0)), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32])]), c_0_33])).
% 56.00/56.26  cnf(c_0_36, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 56.00/56.26  cnf(c_0_37, negated_conjecture, (k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk5_0))=esk4_0|r2_hidden(esk2_3(esk3_0,esk5_0,esk4_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_35])])).
% 56.00/56.26  cnf(c_0_38, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_36, c_0_14])).
% 56.00/56.26  cnf(c_0_39, negated_conjecture, (r2_hidden(esk2_3(esk3_0,esk5_0,esk4_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_37]), c_0_26])]), c_0_31])).
% 56.00/56.26  cnf(c_0_40, negated_conjecture, (~r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk4_0)|~m1_subset_1(X1,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 56.00/56.26  cnf(c_0_41, negated_conjecture, (k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk5_0))=esk4_0|r2_hidden(esk2_3(esk3_0,esk5_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 56.00/56.26  cnf(c_0_42, negated_conjecture, (~r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_40, c_0_24])).
% 56.00/56.26  cnf(c_0_43, negated_conjecture, (r2_hidden(esk2_3(esk3_0,esk5_0,esk4_0),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_41]), c_0_26])]), c_0_31])).
% 56.00/56.26  cnf(c_0_44, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_39]), c_0_35])]), ['proof']).
% 56.00/56.26  # SZS output end CNFRefutation
% 56.00/56.26  # Proof object total steps             : 45
% 56.00/56.26  # Proof object clause steps            : 30
% 56.00/56.26  # Proof object formula steps           : 15
% 56.00/56.26  # Proof object conjectures             : 19
% 56.00/56.26  # Proof object clause conjectures      : 16
% 56.00/56.26  # Proof object formula conjectures     : 3
% 56.00/56.26  # Proof object initial clauses used    : 13
% 56.00/56.26  # Proof object initial formulas used   : 7
% 56.00/56.26  # Proof object generating inferences   : 12
% 56.00/56.26  # Proof object simplifying inferences  : 18
% 56.00/56.26  # Training examples: 0 positive, 0 negative
% 56.00/56.26  # Parsed axioms                        : 7
% 56.00/56.26  # Removed by relevancy pruning/SinE    : 0
% 56.00/56.26  # Initial clauses                      : 20
% 56.00/56.26  # Removed in clause preprocessing      : 1
% 56.00/56.26  # Initial clauses in saturation        : 19
% 56.00/56.26  # Processed clauses                    : 35326
% 56.00/56.26  # ...of these trivial                  : 208
% 56.00/56.26  # ...subsumed                          : 31119
% 56.00/56.26  # ...remaining for further processing  : 3999
% 56.00/56.26  # Other redundant clauses eliminated   : 28
% 56.00/56.26  # Clauses deleted for lack of memory   : 99534
% 56.00/56.26  # Backward-subsumed                    : 960
% 56.00/56.26  # Backward-rewritten                   : 814
% 56.00/56.26  # Generated clauses                    : 2477094
% 56.00/56.26  # ...of the previous two non-trivial   : 2423210
% 56.00/56.26  # Contextual simplify-reflections      : 332
% 56.00/56.26  # Paramodulations                      : 2476090
% 56.00/56.26  # Factorizations                       : 896
% 56.00/56.26  # Equation resolutions                 : 28
% 56.00/56.26  # Propositional unsat checks           : 0
% 56.00/56.26  #    Propositional check models        : 0
% 56.00/56.26  #    Propositional check unsatisfiable : 0
% 56.00/56.26  #    Propositional clauses             : 0
% 56.00/56.26  #    Propositional clauses after purity: 0
% 56.00/56.26  #    Propositional unsat core size     : 0
% 56.00/56.26  #    Propositional preprocessing time  : 0.000
% 56.00/56.26  #    Propositional encoding time       : 0.000
% 56.00/56.26  #    Propositional solver time         : 0.000
% 56.00/56.26  #    Success case prop preproc time    : 0.000
% 56.00/56.26  #    Success case prop encoding time   : 0.000
% 56.00/56.26  #    Success case prop solver time     : 0.000
% 56.00/56.26  # Current number of processed clauses  : 2142
% 56.00/56.26  #    Positive orientable unit clauses  : 75
% 56.00/56.26  #    Positive unorientable unit clauses: 2
% 56.00/56.26  #    Negative unit clauses             : 15
% 56.00/56.26  #    Non-unit-clauses                  : 2050
% 56.00/56.26  # Current number of unprocessed clauses: 1445431
% 56.00/56.26  # ...number of literals in the above   : 9361364
% 56.00/56.26  # Current number of archived formulas  : 0
% 56.00/56.26  # Current number of archived clauses   : 1855
% 56.00/56.26  # Clause-clause subsumption calls (NU) : 2045195
% 56.00/56.26  # Rec. Clause-clause subsumption calls : 843418
% 56.00/56.26  # Non-unit clause-clause subsumptions  : 27717
% 56.00/56.26  # Unit Clause-clause subsumption calls : 27503
% 56.00/56.26  # Rewrite failures with RHS unbound    : 38
% 56.00/56.26  # BW rewrite match attempts            : 917
% 56.00/56.26  # BW rewrite match successes           : 75
% 56.00/56.26  # Condensation attempts                : 0
% 56.00/56.26  # Condensation successes               : 0
% 56.00/56.26  # Termbank termtop insertions          : 102479899
% 56.12/56.33  
% 56.12/56.33  # -------------------------------------------------
% 56.12/56.33  # User time                : 55.011 s
% 56.12/56.33  # System time              : 0.952 s
% 56.12/56.33  # Total time               : 55.963 s
% 56.12/56.33  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
