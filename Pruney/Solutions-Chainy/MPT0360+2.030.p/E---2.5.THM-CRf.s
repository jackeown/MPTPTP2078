%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:46:13 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   43 (  71 expanded)
%              Number of clauses        :   24 (  33 expanded)
%              Number of leaves         :    9 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :  139 ( 243 expanded)
%              Number of equality atoms :   29 (  47 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(t40_subset_1,conjecture,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => ( ( r1_tarski(X2,X3)
          & r1_tarski(X2,k3_subset_1(X1,X3)) )
       => X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(c_0_9,plain,(
    ! [X29,X30] :
      ( ( ~ m1_subset_1(X30,X29)
        | r2_hidden(X30,X29)
        | v1_xboole_0(X29) )
      & ( ~ r2_hidden(X30,X29)
        | m1_subset_1(X30,X29)
        | v1_xboole_0(X29) )
      & ( ~ m1_subset_1(X30,X29)
        | v1_xboole_0(X30)
        | ~ v1_xboole_0(X29) )
      & ( ~ v1_xboole_0(X30)
        | m1_subset_1(X30,X29)
        | ~ v1_xboole_0(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_10,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_11,plain,(
    ! [X22,X23,X24,X25,X26,X27] :
      ( ( ~ r2_hidden(X24,X23)
        | r1_tarski(X24,X22)
        | X23 != k1_zfmisc_1(X22) )
      & ( ~ r1_tarski(X25,X22)
        | r2_hidden(X25,X23)
        | X23 != k1_zfmisc_1(X22) )
      & ( ~ r2_hidden(esk4_2(X26,X27),X27)
        | ~ r1_tarski(esk4_2(X26,X27),X26)
        | X27 = k1_zfmisc_1(X26) )
      & ( r2_hidden(esk4_2(X26,X27),X27)
        | r1_tarski(esk4_2(X26,X27),X26)
        | X27 = k1_zfmisc_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_12,plain,(
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

fof(c_0_13,plain,(
    ! [X20,X21] : k4_xboole_0(X20,X21) = k5_xboole_0(X20,k3_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_14,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(X31))
      | k3_subset_1(X31,X32) = k4_xboole_0(X31,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_20,plain,(
    ! [X33,X34,X35] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(X33))
      | ~ r2_hidden(X35,X34)
      | r2_hidden(X35,X33) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_21,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_16])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(X1))
       => ( ( r1_tarski(X2,X3)
            & r1_tarski(X2,k3_subset_1(X1,X3)) )
         => X2 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t40_subset_1])).

cnf(c_0_24,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_28,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(esk5_0))
    & r1_tarski(esk6_0,esk7_0)
    & r1_tarski(esk6_0,k3_subset_1(esk5_0,esk7_0))
    & esk6_0 != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_18])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(esk6_0,k3_subset_1(esk5_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,k3_subset_1(X2,X1))
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(X1,k3_subset_1(esk5_0,esk7_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_33])).

fof(c_0_38,plain,(
    ! [X18] :
      ( X18 = k1_xboole_0
      | r2_hidden(esk3_1(X18),X18) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_39,negated_conjecture,
    ( ~ r2_hidden(X1,esk6_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_40,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.32  % Computer   : n002.cluster.edu
% 0.14/0.32  % Model      : x86_64 x86_64
% 0.14/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.32  % Memory     : 8042.1875MB
% 0.14/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.32  % CPULimit   : 60
% 0.14/0.32  % WCLimit    : 600
% 0.14/0.32  % DateTime   : Tue Dec  1 14:41:36 EST 2020
% 0.14/0.32  % CPUTime    : 
% 0.14/0.32  # Version: 2.5pre002
% 0.14/0.32  # No SInE strategy applied
% 0.14/0.32  # Trying AutoSched0 for 299 seconds
% 0.19/0.36  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.19/0.36  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.36  #
% 0.19/0.36  # Preprocessing time       : 0.028 s
% 0.19/0.36  
% 0.19/0.36  # Proof found!
% 0.19/0.36  # SZS status Theorem
% 0.19/0.36  # SZS output start CNFRefutation
% 0.19/0.36  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.19/0.36  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.36  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.19/0.36  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.19/0.36  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.36  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.19/0.36  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.19/0.36  fof(t40_subset_1, conjecture, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>((r1_tarski(X2,X3)&r1_tarski(X2,k3_subset_1(X1,X3)))=>X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 0.19/0.36  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.19/0.36  fof(c_0_9, plain, ![X29, X30]:(((~m1_subset_1(X30,X29)|r2_hidden(X30,X29)|v1_xboole_0(X29))&(~r2_hidden(X30,X29)|m1_subset_1(X30,X29)|v1_xboole_0(X29)))&((~m1_subset_1(X30,X29)|v1_xboole_0(X30)|~v1_xboole_0(X29))&(~v1_xboole_0(X30)|m1_subset_1(X30,X29)|~v1_xboole_0(X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.19/0.36  fof(c_0_10, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.36  fof(c_0_11, plain, ![X22, X23, X24, X25, X26, X27]:(((~r2_hidden(X24,X23)|r1_tarski(X24,X22)|X23!=k1_zfmisc_1(X22))&(~r1_tarski(X25,X22)|r2_hidden(X25,X23)|X23!=k1_zfmisc_1(X22)))&((~r2_hidden(esk4_2(X26,X27),X27)|~r1_tarski(esk4_2(X26,X27),X26)|X27=k1_zfmisc_1(X26))&(r2_hidden(esk4_2(X26,X27),X27)|r1_tarski(esk4_2(X26,X27),X26)|X27=k1_zfmisc_1(X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.19/0.36  fof(c_0_12, plain, ![X9, X10, X11, X12, X13, X14, X15, X16]:((((r2_hidden(X12,X9)|~r2_hidden(X12,X11)|X11!=k4_xboole_0(X9,X10))&(~r2_hidden(X12,X10)|~r2_hidden(X12,X11)|X11!=k4_xboole_0(X9,X10)))&(~r2_hidden(X13,X9)|r2_hidden(X13,X10)|r2_hidden(X13,X11)|X11!=k4_xboole_0(X9,X10)))&((~r2_hidden(esk2_3(X14,X15,X16),X16)|(~r2_hidden(esk2_3(X14,X15,X16),X14)|r2_hidden(esk2_3(X14,X15,X16),X15))|X16=k4_xboole_0(X14,X15))&((r2_hidden(esk2_3(X14,X15,X16),X14)|r2_hidden(esk2_3(X14,X15,X16),X16)|X16=k4_xboole_0(X14,X15))&(~r2_hidden(esk2_3(X14,X15,X16),X15)|r2_hidden(esk2_3(X14,X15,X16),X16)|X16=k4_xboole_0(X14,X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.19/0.36  fof(c_0_13, plain, ![X20, X21]:k4_xboole_0(X20,X21)=k5_xboole_0(X20,k3_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.36  cnf(c_0_14, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.36  cnf(c_0_15, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.36  cnf(c_0_16, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.36  cnf(c_0_17, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.36  cnf(c_0_18, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.36  fof(c_0_19, plain, ![X31, X32]:(~m1_subset_1(X32,k1_zfmisc_1(X31))|k3_subset_1(X31,X32)=k4_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.19/0.36  fof(c_0_20, plain, ![X33, X34, X35]:(~m1_subset_1(X34,k1_zfmisc_1(X33))|(~r2_hidden(X35,X34)|r2_hidden(X35,X33))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.19/0.36  cnf(c_0_21, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.36  cnf(c_0_22, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_16])).
% 0.19/0.36  fof(c_0_23, negated_conjecture, ~(![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>((r1_tarski(X2,X3)&r1_tarski(X2,k3_subset_1(X1,X3)))=>X2=k1_xboole_0))), inference(assume_negation,[status(cth)],[t40_subset_1])).
% 0.19/0.36  cnf(c_0_24, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.36  cnf(c_0_25, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.36  cnf(c_0_26, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.36  cnf(c_0_27, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.36  fof(c_0_28, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(esk5_0))&((r1_tarski(esk6_0,esk7_0)&r1_tarski(esk6_0,k3_subset_1(esk5_0,esk7_0)))&esk6_0!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.19/0.36  cnf(c_0_29, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_24])).
% 0.19/0.36  cnf(c_0_30, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_25, c_0_18])).
% 0.19/0.36  cnf(c_0_31, plain, (r2_hidden(X1,X2)|~r1_tarski(X3,X2)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.36  cnf(c_0_32, negated_conjecture, (r1_tarski(esk6_0,k3_subset_1(esk5_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.36  cnf(c_0_33, negated_conjecture, (r1_tarski(esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.36  cnf(c_0_34, plain, (~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,k3_subset_1(X2,X1))|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.36  cnf(c_0_35, negated_conjecture, (r2_hidden(X1,k3_subset_1(esk5_0,esk7_0))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.36  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.36  cnf(c_0_37, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_31, c_0_33])).
% 0.19/0.36  fof(c_0_38, plain, ![X18]:(X18=k1_xboole_0|r2_hidden(esk3_1(X18),X18)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.19/0.36  cnf(c_0_39, negated_conjecture, (~r2_hidden(X1,esk6_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])]), c_0_37])).
% 0.19/0.36  cnf(c_0_40, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.36  cnf(c_0_41, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.36  cnf(c_0_42, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), ['proof']).
% 0.19/0.36  # SZS output end CNFRefutation
% 0.19/0.36  # Proof object total steps             : 43
% 0.19/0.36  # Proof object clause steps            : 24
% 0.19/0.36  # Proof object formula steps           : 19
% 0.19/0.36  # Proof object conjectures             : 11
% 0.19/0.36  # Proof object clause conjectures      : 8
% 0.19/0.36  # Proof object formula conjectures     : 3
% 0.19/0.36  # Proof object initial clauses used    : 12
% 0.19/0.36  # Proof object initial formulas used   : 9
% 0.19/0.36  # Proof object generating inferences   : 7
% 0.19/0.36  # Proof object simplifying inferences  : 9
% 0.19/0.36  # Training examples: 0 positive, 0 negative
% 0.19/0.36  # Parsed axioms                        : 9
% 0.19/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.36  # Initial clauses                      : 24
% 0.19/0.36  # Removed in clause preprocessing      : 1
% 0.19/0.36  # Initial clauses in saturation        : 23
% 0.19/0.36  # Processed clauses                    : 76
% 0.19/0.36  # ...of these trivial                  : 0
% 0.19/0.36  # ...subsumed                          : 17
% 0.19/0.36  # ...remaining for further processing  : 59
% 0.19/0.36  # Other redundant clauses eliminated   : 5
% 0.19/0.36  # Clauses deleted for lack of memory   : 0
% 0.19/0.36  # Backward-subsumed                    : 0
% 0.19/0.36  # Backward-rewritten                   : 0
% 0.19/0.36  # Generated clauses                    : 138
% 0.19/0.36  # ...of the previous two non-trivial   : 119
% 0.19/0.36  # Contextual simplify-reflections      : 2
% 0.19/0.36  # Paramodulations                      : 130
% 0.19/0.36  # Factorizations                       : 2
% 0.19/0.36  # Equation resolutions                 : 5
% 0.19/0.36  # Propositional unsat checks           : 0
% 0.19/0.36  #    Propositional check models        : 0
% 0.19/0.36  #    Propositional check unsatisfiable : 0
% 0.19/0.36  #    Propositional clauses             : 0
% 0.19/0.36  #    Propositional clauses after purity: 0
% 0.19/0.36  #    Propositional unsat core size     : 0
% 0.19/0.36  #    Propositional preprocessing time  : 0.000
% 0.19/0.36  #    Propositional encoding time       : 0.000
% 0.19/0.36  #    Propositional solver time         : 0.000
% 0.19/0.36  #    Success case prop preproc time    : 0.000
% 0.19/0.36  #    Success case prop encoding time   : 0.000
% 0.19/0.36  #    Success case prop solver time     : 0.000
% 0.19/0.36  # Current number of processed clauses  : 53
% 0.19/0.36  #    Positive orientable unit clauses  : 7
% 0.19/0.36  #    Positive unorientable unit clauses: 0
% 0.19/0.36  #    Negative unit clauses             : 4
% 0.19/0.36  #    Non-unit-clauses                  : 42
% 0.19/0.36  # Current number of unprocessed clauses: 64
% 0.19/0.36  # ...number of literals in the above   : 199
% 0.19/0.36  # Current number of archived formulas  : 0
% 0.19/0.36  # Current number of archived clauses   : 2
% 0.19/0.36  # Clause-clause subsumption calls (NU) : 295
% 0.19/0.36  # Rec. Clause-clause subsumption calls : 221
% 0.19/0.36  # Non-unit clause-clause subsumptions  : 9
% 0.19/0.36  # Unit Clause-clause subsumption calls : 74
% 0.19/0.36  # Rewrite failures with RHS unbound    : 0
% 0.19/0.36  # BW rewrite match attempts            : 0
% 0.19/0.36  # BW rewrite match successes           : 0
% 0.19/0.36  # Condensation attempts                : 0
% 0.19/0.36  # Condensation successes               : 0
% 0.19/0.36  # Termbank termtop insertions          : 2982
% 0.19/0.36  
% 0.19/0.36  # -------------------------------------------------
% 0.19/0.36  # User time                : 0.030 s
% 0.19/0.36  # System time              : 0.005 s
% 0.19/0.36  # Total time               : 0.036 s
% 0.19/0.36  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
