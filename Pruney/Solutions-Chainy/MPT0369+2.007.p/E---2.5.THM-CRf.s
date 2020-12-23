%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:46:43 EST 2020

% Result     : Theorem 0.16s
% Output     : CNFRefutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   58 (  70 expanded)
%              Number of clauses        :   29 (  29 expanded)
%              Number of leaves         :   14 (  18 expanded)
%              Depth                    :   10
%              Number of atoms          :  133 ( 193 expanded)
%              Number of equality atoms :   34 (  46 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t22_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(t43_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_xboole_0(X2,X3)
          <=> r1_tarski(X2,k3_subset_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t50_subset_1,conjecture,(
    ! [X1] :
      ( X1 != k1_xboole_0
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => ! [X3] :
              ( m1_subset_1(X3,X1)
             => ( ~ r2_hidden(X3,X2)
               => r2_hidden(X3,k3_subset_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(c_0_14,plain,(
    ! [X21] : k2_subset_1(X21) = k3_subset_1(X21,k1_subset_1(X21)) ),
    inference(variable_rename,[status(thm)],[t22_subset_1])).

fof(c_0_15,plain,(
    ! [X18] : k2_subset_1(X18) = X18 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_16,plain,(
    ! [X17] : k1_subset_1(X17) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

fof(c_0_17,plain,(
    ! [X22,X23,X24] :
      ( ( ~ r1_xboole_0(X23,X24)
        | r1_tarski(X23,k3_subset_1(X22,X24))
        | ~ m1_subset_1(X24,k1_zfmisc_1(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(X22)) )
      & ( ~ r1_tarski(X23,k3_subset_1(X22,X24))
        | r1_xboole_0(X23,X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(X22)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_subset_1])])])])).

cnf(c_0_18,plain,
    ( k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X25] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X25)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_22,plain,(
    ! [X14] : r1_xboole_0(X14,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_23,plain,(
    ! [X12,X13] :
      ( ~ r1_tarski(X12,X13)
      | k3_xboole_0(X12,X13) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,k3_subset_1(X3,X2))
    | ~ r1_xboole_0(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( X1 = k3_subset_1(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_26,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_28,plain,(
    ! [X19,X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(X19))
      | k3_subset_1(X19,X20) = k4_xboole_0(X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_29,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_30,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27])])).

cnf(c_0_33,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_37,negated_conjecture,(
    ~ ! [X1] :
        ( X1 != k1_xboole_0
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X1))
           => ! [X3] :
                ( m1_subset_1(X3,X1)
               => ( ~ r2_hidden(X3,X2)
                 => r2_hidden(X3,k3_subset_1(X1,X2)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_subset_1])).

cnf(c_0_38,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_40,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    & m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))
    & m1_subset_1(esk3_0,esk1_0)
    & ~ r2_hidden(esk3_0,esk2_0)
    & ~ r2_hidden(esk3_0,k3_subset_1(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_37])])])])).

fof(c_0_41,plain,(
    ! [X15,X16] :
      ( ( ~ m1_subset_1(X16,X15)
        | r2_hidden(X16,X15)
        | v1_xboole_0(X15) )
      & ( ~ r2_hidden(X16,X15)
        | m1_subset_1(X16,X15)
        | v1_xboole_0(X15) )
      & ( ~ m1_subset_1(X16,X15)
        | v1_xboole_0(X16)
        | ~ v1_xboole_0(X15) )
      & ( ~ v1_xboole_0(X16)
        | m1_subset_1(X16,X15)
        | ~ v1_xboole_0(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_42,plain,(
    ! [X7,X8,X9] :
      ( ( ~ r2_hidden(X7,X8)
        | ~ r2_hidden(X7,X9)
        | ~ r2_hidden(X7,k5_xboole_0(X8,X9)) )
      & ( r2_hidden(X7,X8)
        | r2_hidden(X7,X9)
        | ~ r2_hidden(X7,k5_xboole_0(X8,X9)) )
      & ( ~ r2_hidden(X7,X8)
        | r2_hidden(X7,X9)
        | r2_hidden(X7,k5_xboole_0(X8,X9)) )
      & ( ~ r2_hidden(X7,X9)
        | r2_hidden(X7,X8)
        | r2_hidden(X7,k5_xboole_0(X8,X9)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

cnf(c_0_43,plain,
    ( k5_xboole_0(X1,X2) = k3_subset_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_45,plain,(
    ! [X6] :
      ( ~ v1_xboole_0(X6)
      | X6 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( k5_xboole_0(esk1_0,esk2_0) = k3_subset_1(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk3_0,esk1_0)
    | v1_xboole_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_53,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k3_subset_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(X1,k3_subset_1(esk1_0,esk2_0))
    | r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk3_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])]),c_0_56]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.30  % Computer   : n008.cluster.edu
% 0.12/0.30  % Model      : x86_64 x86_64
% 0.12/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.30  % Memory     : 8042.1875MB
% 0.12/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.30  % CPULimit   : 60
% 0.12/0.30  % WCLimit    : 600
% 0.12/0.30  % DateTime   : Tue Dec  1 14:41:15 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.12/0.31  # Version: 2.5pre002
% 0.12/0.31  # No SInE strategy applied
% 0.12/0.31  # Trying AutoSched0 for 299 seconds
% 0.16/0.34  # AutoSched0-Mode selected heuristic G_E___103_C18_F1_PI_AE_Q4_CS_SP_S0Y
% 0.16/0.34  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.16/0.34  #
% 0.16/0.34  # Preprocessing time       : 0.027 s
% 0.16/0.34  
% 0.16/0.34  # Proof found!
% 0.16/0.34  # SZS status Theorem
% 0.16/0.34  # SZS output start CNFRefutation
% 0.16/0.34  fof(t22_subset_1, axiom, ![X1]:k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 0.16/0.34  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.16/0.34  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 0.16/0.34  fof(t43_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_xboole_0(X2,X3)<=>r1_tarski(X2,k3_subset_1(X1,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_subset_1)).
% 0.16/0.34  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.16/0.34  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.16/0.34  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.16/0.34  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.16/0.34  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.16/0.34  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.16/0.34  fof(t50_subset_1, conjecture, ![X1]:(X1!=k1_xboole_0=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,X1)=>(~(r2_hidden(X3,X2))=>r2_hidden(X3,k3_subset_1(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_subset_1)).
% 0.16/0.34  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.16/0.34  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 0.16/0.34  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.16/0.34  fof(c_0_14, plain, ![X21]:k2_subset_1(X21)=k3_subset_1(X21,k1_subset_1(X21)), inference(variable_rename,[status(thm)],[t22_subset_1])).
% 0.16/0.34  fof(c_0_15, plain, ![X18]:k2_subset_1(X18)=X18, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.16/0.34  fof(c_0_16, plain, ![X17]:k1_subset_1(X17)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.16/0.34  fof(c_0_17, plain, ![X22, X23, X24]:((~r1_xboole_0(X23,X24)|r1_tarski(X23,k3_subset_1(X22,X24))|~m1_subset_1(X24,k1_zfmisc_1(X22))|~m1_subset_1(X23,k1_zfmisc_1(X22)))&(~r1_tarski(X23,k3_subset_1(X22,X24))|r1_xboole_0(X23,X24)|~m1_subset_1(X24,k1_zfmisc_1(X22))|~m1_subset_1(X23,k1_zfmisc_1(X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_subset_1])])])])).
% 0.16/0.34  cnf(c_0_18, plain, (k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.16/0.34  cnf(c_0_19, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.16/0.34  cnf(c_0_20, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.16/0.34  fof(c_0_21, plain, ![X25]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X25)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.16/0.34  fof(c_0_22, plain, ![X14]:r1_xboole_0(X14,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.16/0.34  fof(c_0_23, plain, ![X12, X13]:(~r1_tarski(X12,X13)|k3_xboole_0(X12,X13)=X12), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.16/0.34  cnf(c_0_24, plain, (r1_tarski(X1,k3_subset_1(X3,X2))|~r1_xboole_0(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.16/0.34  cnf(c_0_25, plain, (X1=k3_subset_1(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 0.16/0.34  cnf(c_0_26, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.16/0.34  cnf(c_0_27, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.16/0.34  fof(c_0_28, plain, ![X19, X20]:(~m1_subset_1(X20,k1_zfmisc_1(X19))|k3_subset_1(X19,X20)=k4_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.16/0.34  fof(c_0_29, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.16/0.34  fof(c_0_30, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.16/0.34  cnf(c_0_31, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.16/0.34  cnf(c_0_32, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27])])).
% 0.16/0.34  cnf(c_0_33, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.16/0.34  cnf(c_0_34, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.16/0.34  cnf(c_0_35, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.16/0.34  cnf(c_0_36, plain, (k3_xboole_0(X1,X2)=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.16/0.34  fof(c_0_37, negated_conjecture, ~(![X1]:(X1!=k1_xboole_0=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,X1)=>(~(r2_hidden(X3,X2))=>r2_hidden(X3,k3_subset_1(X1,X2))))))), inference(assume_negation,[status(cth)],[t50_subset_1])).
% 0.16/0.34  cnf(c_0_38, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.16/0.34  cnf(c_0_39, plain, (k3_xboole_0(X1,X2)=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.16/0.34  fof(c_0_40, negated_conjecture, (esk1_0!=k1_xboole_0&(m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))&(m1_subset_1(esk3_0,esk1_0)&(~r2_hidden(esk3_0,esk2_0)&~r2_hidden(esk3_0,k3_subset_1(esk1_0,esk2_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_37])])])])).
% 0.16/0.34  fof(c_0_41, plain, ![X15, X16]:(((~m1_subset_1(X16,X15)|r2_hidden(X16,X15)|v1_xboole_0(X15))&(~r2_hidden(X16,X15)|m1_subset_1(X16,X15)|v1_xboole_0(X15)))&((~m1_subset_1(X16,X15)|v1_xboole_0(X16)|~v1_xboole_0(X15))&(~v1_xboole_0(X16)|m1_subset_1(X16,X15)|~v1_xboole_0(X15)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.16/0.34  fof(c_0_42, plain, ![X7, X8, X9]:(((~r2_hidden(X7,X8)|~r2_hidden(X7,X9)|~r2_hidden(X7,k5_xboole_0(X8,X9)))&(r2_hidden(X7,X8)|r2_hidden(X7,X9)|~r2_hidden(X7,k5_xboole_0(X8,X9))))&((~r2_hidden(X7,X8)|r2_hidden(X7,X9)|r2_hidden(X7,k5_xboole_0(X8,X9)))&(~r2_hidden(X7,X9)|r2_hidden(X7,X8)|r2_hidden(X7,k5_xboole_0(X8,X9))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 0.16/0.34  cnf(c_0_43, plain, (k5_xboole_0(X1,X2)=k3_subset_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.16/0.34  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.16/0.34  fof(c_0_45, plain, ![X6]:(~v1_xboole_0(X6)|X6=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.16/0.34  cnf(c_0_46, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.16/0.34  cnf(c_0_47, negated_conjecture, (m1_subset_1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.16/0.34  cnf(c_0_48, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.16/0.34  cnf(c_0_49, negated_conjecture, (k5_xboole_0(esk1_0,esk2_0)=k3_subset_1(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.16/0.34  cnf(c_0_50, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.16/0.34  cnf(c_0_51, negated_conjecture, (r2_hidden(esk3_0,esk1_0)|v1_xboole_0(esk1_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.16/0.34  cnf(c_0_52, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.16/0.34  cnf(c_0_53, negated_conjecture, (~r2_hidden(esk3_0,k3_subset_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.16/0.34  cnf(c_0_54, negated_conjecture, (r2_hidden(X1,k3_subset_1(esk1_0,esk2_0))|r2_hidden(X1,esk2_0)|~r2_hidden(X1,esk1_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.16/0.34  cnf(c_0_55, negated_conjecture, (r2_hidden(esk3_0,esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])).
% 0.16/0.34  cnf(c_0_56, negated_conjecture, (~r2_hidden(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.16/0.34  cnf(c_0_57, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])]), c_0_56]), ['proof']).
% 0.16/0.34  # SZS output end CNFRefutation
% 0.16/0.34  # Proof object total steps             : 58
% 0.16/0.34  # Proof object clause steps            : 29
% 0.16/0.34  # Proof object formula steps           : 29
% 0.16/0.34  # Proof object conjectures             : 13
% 0.16/0.34  # Proof object clause conjectures      : 10
% 0.16/0.34  # Proof object formula conjectures     : 3
% 0.16/0.34  # Proof object initial clauses used    : 18
% 0.16/0.34  # Proof object initial formulas used   : 14
% 0.16/0.34  # Proof object generating inferences   : 9
% 0.16/0.34  # Proof object simplifying inferences  : 10
% 0.16/0.34  # Training examples: 0 positive, 0 negative
% 0.16/0.34  # Parsed axioms                        : 14
% 0.16/0.34  # Removed by relevancy pruning/SinE    : 0
% 0.16/0.34  # Initial clauses                      : 25
% 0.16/0.34  # Removed in clause preprocessing      : 3
% 0.16/0.34  # Initial clauses in saturation        : 22
% 0.16/0.34  # Processed clauses                    : 68
% 0.16/0.34  # ...of these trivial                  : 0
% 0.16/0.34  # ...subsumed                          : 6
% 0.16/0.34  # ...remaining for further processing  : 62
% 0.16/0.34  # Other redundant clauses eliminated   : 0
% 0.16/0.34  # Clauses deleted for lack of memory   : 0
% 0.16/0.34  # Backward-subsumed                    : 0
% 0.16/0.34  # Backward-rewritten                   : 1
% 0.16/0.34  # Generated clauses                    : 122
% 0.16/0.34  # ...of the previous two non-trivial   : 92
% 0.16/0.34  # Contextual simplify-reflections      : 1
% 0.16/0.34  # Paramodulations                      : 122
% 0.16/0.34  # Factorizations                       : 0
% 0.16/0.34  # Equation resolutions                 : 0
% 0.16/0.34  # Propositional unsat checks           : 0
% 0.16/0.34  #    Propositional check models        : 0
% 0.16/0.34  #    Propositional check unsatisfiable : 0
% 0.16/0.34  #    Propositional clauses             : 0
% 0.16/0.34  #    Propositional clauses after purity: 0
% 0.16/0.34  #    Propositional unsat core size     : 0
% 0.16/0.34  #    Propositional preprocessing time  : 0.000
% 0.16/0.34  #    Propositional encoding time       : 0.000
% 0.16/0.34  #    Propositional solver time         : 0.000
% 0.16/0.34  #    Success case prop preproc time    : 0.000
% 0.16/0.34  #    Success case prop encoding time   : 0.000
% 0.16/0.34  #    Success case prop solver time     : 0.000
% 0.16/0.34  # Current number of processed clauses  : 61
% 0.16/0.34  #    Positive orientable unit clauses  : 8
% 0.16/0.34  #    Positive unorientable unit clauses: 1
% 0.16/0.34  #    Negative unit clauses             : 4
% 0.16/0.34  #    Non-unit-clauses                  : 48
% 0.16/0.34  # Current number of unprocessed clauses: 45
% 0.16/0.34  # ...number of literals in the above   : 184
% 0.16/0.34  # Current number of archived formulas  : 0
% 0.16/0.34  # Current number of archived clauses   : 4
% 0.16/0.34  # Clause-clause subsumption calls (NU) : 162
% 0.16/0.34  # Rec. Clause-clause subsumption calls : 116
% 0.16/0.34  # Non-unit clause-clause subsumptions  : 7
% 0.16/0.34  # Unit Clause-clause subsumption calls : 9
% 0.16/0.34  # Rewrite failures with RHS unbound    : 0
% 0.16/0.34  # BW rewrite match attempts            : 3
% 0.16/0.34  # BW rewrite match successes           : 3
% 0.16/0.34  # Condensation attempts                : 0
% 0.16/0.34  # Condensation successes               : 0
% 0.16/0.34  # Termbank termtop insertions          : 2903
% 0.16/0.34  
% 0.16/0.34  # -------------------------------------------------
% 0.16/0.34  # User time                : 0.030 s
% 0.16/0.34  # System time              : 0.004 s
% 0.16/0.34  # Total time               : 0.035 s
% 0.16/0.34  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
