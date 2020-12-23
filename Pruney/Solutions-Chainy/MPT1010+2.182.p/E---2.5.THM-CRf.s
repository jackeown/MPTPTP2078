%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:05:36 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   41 (  80 expanded)
%              Number of clauses        :   22 (  31 expanded)
%              Number of leaves         :    9 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :  123 ( 210 expanded)
%              Number of equality atoms :   72 ( 111 expanded)
%              Maximal formula depth    :   27 (   4 average)
%              Maximal clause size      :   36 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(d2_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( X5 = k2_enumset1(X1,X2,X3,X4)
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X6 != X1
              & X6 != X2
              & X6 != X3
              & X6 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).

fof(t7_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_hidden(X3,X1)
       => ( X2 = k1_xboole_0
          | r2_hidden(k1_funct_1(X4,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,k1_tarski(X2))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
       => ( r2_hidden(X3,X1)
         => k1_funct_1(X4,X3) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t65_funct_2])).

fof(c_0_10,plain,(
    ! [X18,X19] : k2_xboole_0(k1_tarski(X18),X19) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

fof(c_0_11,plain,(
    ! [X8] : k2_tarski(X8,X8) = k1_tarski(X8) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_12,plain,(
    ! [X9,X10] : k1_enumset1(X9,X9,X10) = k2_tarski(X9,X10) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X11,X12,X13] : k2_enumset1(X11,X11,X12,X13) = k1_enumset1(X11,X12,X13) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_14,plain,(
    ! [X14,X15,X16,X17] : k3_enumset1(X14,X14,X15,X16,X17) = k2_enumset1(X14,X15,X16,X17) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_15,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk2_0,k1_tarski(esk3_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_tarski(esk3_0))))
    & r2_hidden(esk4_0,esk2_0)
    & k1_funct_1(esk5_0,esk4_0) != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_16,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,plain,(
    ! [X7] : k2_xboole_0(X7,k1_xboole_0) = X7 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_22,plain,(
    ! [X20,X21,X22,X23,X24,X25,X26,X27,X28,X29,X30,X31] :
      ( ( ~ r2_hidden(X25,X24)
        | X25 = X20
        | X25 = X21
        | X25 = X22
        | X25 = X23
        | X24 != k2_enumset1(X20,X21,X22,X23) )
      & ( X26 != X20
        | r2_hidden(X26,X24)
        | X24 != k2_enumset1(X20,X21,X22,X23) )
      & ( X26 != X21
        | r2_hidden(X26,X24)
        | X24 != k2_enumset1(X20,X21,X22,X23) )
      & ( X26 != X22
        | r2_hidden(X26,X24)
        | X24 != k2_enumset1(X20,X21,X22,X23) )
      & ( X26 != X23
        | r2_hidden(X26,X24)
        | X24 != k2_enumset1(X20,X21,X22,X23) )
      & ( esk1_5(X27,X28,X29,X30,X31) != X27
        | ~ r2_hidden(esk1_5(X27,X28,X29,X30,X31),X31)
        | X31 = k2_enumset1(X27,X28,X29,X30) )
      & ( esk1_5(X27,X28,X29,X30,X31) != X28
        | ~ r2_hidden(esk1_5(X27,X28,X29,X30,X31),X31)
        | X31 = k2_enumset1(X27,X28,X29,X30) )
      & ( esk1_5(X27,X28,X29,X30,X31) != X29
        | ~ r2_hidden(esk1_5(X27,X28,X29,X30,X31),X31)
        | X31 = k2_enumset1(X27,X28,X29,X30) )
      & ( esk1_5(X27,X28,X29,X30,X31) != X30
        | ~ r2_hidden(esk1_5(X27,X28,X29,X30,X31),X31)
        | X31 = k2_enumset1(X27,X28,X29,X30) )
      & ( r2_hidden(esk1_5(X27,X28,X29,X30,X31),X31)
        | esk1_5(X27,X28,X29,X30,X31) = X27
        | esk1_5(X27,X28,X29,X30,X31) = X28
        | esk1_5(X27,X28,X29,X30,X31) = X29
        | esk1_5(X27,X28,X29,X30,X31) = X30
        | X31 = k2_enumset1(X27,X28,X29,X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_enumset1])])])])])])).

fof(c_0_23,plain,(
    ! [X33,X34,X35,X36] :
      ( ~ v1_funct_1(X36)
      | ~ v1_funct_2(X36,X33,X34)
      | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | ~ r2_hidden(X35,X33)
      | X34 = k1_xboole_0
      | r2_hidden(k1_funct_1(X36,X35),X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_2(esk5_0,esk2_0,k1_tarski(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_tarski(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | X1 = X6
    | ~ r2_hidden(X1,X2)
    | X2 != k2_enumset1(X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( X3 = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X4),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_2(esk5_0,esk2_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_17]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_17]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_33,plain,
    ( k3_enumset1(X1,X1,X1,X1,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,plain,
    ( X1 = X6
    | X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k3_enumset1(X3,X3,X4,X5,X6)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_28,c_0_20])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,X1),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_37,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,k3_enumset1(X5,X5,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,esk4_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( k1_funct_1(esk5_0,esk4_0) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n013.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 11:33:54 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  # Version: 2.5pre002
% 0.12/0.32  # No SInE strategy applied
% 0.12/0.32  # Trying AutoSched0 for 299 seconds
% 0.12/0.35  # AutoSched0-Mode selected heuristic G_E___208_C12_02_nc_F1_SE_CS_SP_PS_S002A
% 0.12/0.35  # and selection function SelectNegativeLiterals.
% 0.12/0.35  #
% 0.12/0.35  # Preprocessing time       : 0.027 s
% 0.12/0.35  # Presaturation interreduction done
% 0.12/0.35  
% 0.12/0.35  # Proof found!
% 0.12/0.35  # SZS status Theorem
% 0.12/0.35  # SZS output start CNFRefutation
% 0.12/0.35  fof(t65_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 0.12/0.35  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.12/0.35  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.12/0.35  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.35  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.12/0.35  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.12/0.35  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.12/0.35  fof(d2_enumset1, axiom, ![X1, X2, X3, X4, X5]:(X5=k2_enumset1(X1,X2,X3,X4)<=>![X6]:(r2_hidden(X6,X5)<=>~((((X6!=X1&X6!=X2)&X6!=X3)&X6!=X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_enumset1)).
% 0.12/0.35  fof(t7_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_hidden(X3,X1)=>(X2=k1_xboole_0|r2_hidden(k1_funct_1(X4,X3),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 0.12/0.35  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2))), inference(assume_negation,[status(cth)],[t65_funct_2])).
% 0.12/0.35  fof(c_0_10, plain, ![X18, X19]:k2_xboole_0(k1_tarski(X18),X19)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.12/0.35  fof(c_0_11, plain, ![X8]:k2_tarski(X8,X8)=k1_tarski(X8), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.35  fof(c_0_12, plain, ![X9, X10]:k1_enumset1(X9,X9,X10)=k2_tarski(X9,X10), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.35  fof(c_0_13, plain, ![X11, X12, X13]:k2_enumset1(X11,X11,X12,X13)=k1_enumset1(X11,X12,X13), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.12/0.35  fof(c_0_14, plain, ![X14, X15, X16, X17]:k3_enumset1(X14,X14,X15,X16,X17)=k2_enumset1(X14,X15,X16,X17), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.12/0.35  fof(c_0_15, negated_conjecture, (((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk2_0,k1_tarski(esk3_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_tarski(esk3_0)))))&(r2_hidden(esk4_0,esk2_0)&k1_funct_1(esk5_0,esk4_0)!=esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.12/0.35  cnf(c_0_16, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.35  cnf(c_0_17, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.35  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.35  cnf(c_0_19, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.35  cnf(c_0_20, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.35  fof(c_0_21, plain, ![X7]:k2_xboole_0(X7,k1_xboole_0)=X7, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.12/0.35  fof(c_0_22, plain, ![X20, X21, X22, X23, X24, X25, X26, X27, X28, X29, X30, X31]:(((~r2_hidden(X25,X24)|(X25=X20|X25=X21|X25=X22|X25=X23)|X24!=k2_enumset1(X20,X21,X22,X23))&((((X26!=X20|r2_hidden(X26,X24)|X24!=k2_enumset1(X20,X21,X22,X23))&(X26!=X21|r2_hidden(X26,X24)|X24!=k2_enumset1(X20,X21,X22,X23)))&(X26!=X22|r2_hidden(X26,X24)|X24!=k2_enumset1(X20,X21,X22,X23)))&(X26!=X23|r2_hidden(X26,X24)|X24!=k2_enumset1(X20,X21,X22,X23))))&(((((esk1_5(X27,X28,X29,X30,X31)!=X27|~r2_hidden(esk1_5(X27,X28,X29,X30,X31),X31)|X31=k2_enumset1(X27,X28,X29,X30))&(esk1_5(X27,X28,X29,X30,X31)!=X28|~r2_hidden(esk1_5(X27,X28,X29,X30,X31),X31)|X31=k2_enumset1(X27,X28,X29,X30)))&(esk1_5(X27,X28,X29,X30,X31)!=X29|~r2_hidden(esk1_5(X27,X28,X29,X30,X31),X31)|X31=k2_enumset1(X27,X28,X29,X30)))&(esk1_5(X27,X28,X29,X30,X31)!=X30|~r2_hidden(esk1_5(X27,X28,X29,X30,X31),X31)|X31=k2_enumset1(X27,X28,X29,X30)))&(r2_hidden(esk1_5(X27,X28,X29,X30,X31),X31)|(esk1_5(X27,X28,X29,X30,X31)=X27|esk1_5(X27,X28,X29,X30,X31)=X28|esk1_5(X27,X28,X29,X30,X31)=X29|esk1_5(X27,X28,X29,X30,X31)=X30)|X31=k2_enumset1(X27,X28,X29,X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_enumset1])])])])])])).
% 0.12/0.35  fof(c_0_23, plain, ![X33, X34, X35, X36]:(~v1_funct_1(X36)|~v1_funct_2(X36,X33,X34)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|(~r2_hidden(X35,X33)|(X34=k1_xboole_0|r2_hidden(k1_funct_1(X36,X35),X34)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).
% 0.12/0.35  cnf(c_0_24, negated_conjecture, (v1_funct_2(esk5_0,esk2_0,k1_tarski(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.35  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_tarski(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.35  cnf(c_0_26, plain, (k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19]), c_0_20])).
% 0.12/0.35  cnf(c_0_27, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.35  cnf(c_0_28, plain, (X1=X3|X1=X4|X1=X5|X1=X6|~r2_hidden(X1,X2)|X2!=k2_enumset1(X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.35  cnf(c_0_29, plain, (X3=k1_xboole_0|r2_hidden(k1_funct_1(X1,X4),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.35  cnf(c_0_30, negated_conjecture, (v1_funct_2(esk5_0,esk2_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_17]), c_0_18]), c_0_19]), c_0_20])).
% 0.12/0.35  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_17]), c_0_18]), c_0_19]), c_0_20])).
% 0.12/0.35  cnf(c_0_32, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.35  cnf(c_0_33, plain, (k3_enumset1(X1,X1,X1,X1,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.12/0.35  cnf(c_0_34, plain, (X1=X6|X1=X5|X1=X4|X1=X3|X2!=k3_enumset1(X3,X3,X4,X5,X6)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_28, c_0_20])).
% 0.12/0.35  cnf(c_0_35, negated_conjecture, (r2_hidden(k1_funct_1(esk5_0,X1),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))|~r2_hidden(X1,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32])]), c_0_33])).
% 0.12/0.35  cnf(c_0_36, negated_conjecture, (r2_hidden(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.35  cnf(c_0_37, plain, (X1=X2|X1=X3|X1=X4|X1=X5|~r2_hidden(X1,k3_enumset1(X5,X5,X4,X3,X2))), inference(er,[status(thm)],[c_0_34])).
% 0.12/0.35  cnf(c_0_38, negated_conjecture, (r2_hidden(k1_funct_1(esk5_0,esk4_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.12/0.35  cnf(c_0_39, negated_conjecture, (k1_funct_1(esk5_0,esk4_0)!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.35  cnf(c_0_40, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), ['proof']).
% 0.12/0.35  # SZS output end CNFRefutation
% 0.12/0.35  # Proof object total steps             : 41
% 0.12/0.35  # Proof object clause steps            : 22
% 0.12/0.35  # Proof object formula steps           : 19
% 0.12/0.35  # Proof object conjectures             : 13
% 0.12/0.35  # Proof object clause conjectures      : 10
% 0.12/0.35  # Proof object formula conjectures     : 3
% 0.12/0.35  # Proof object initial clauses used    : 13
% 0.12/0.35  # Proof object initial formulas used   : 9
% 0.12/0.35  # Proof object generating inferences   : 4
% 0.12/0.35  # Proof object simplifying inferences  : 19
% 0.12/0.35  # Training examples: 0 positive, 0 negative
% 0.12/0.35  # Parsed axioms                        : 9
% 0.12/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.35  # Initial clauses                      : 22
% 0.12/0.35  # Removed in clause preprocessing      : 4
% 0.12/0.35  # Initial clauses in saturation        : 18
% 0.12/0.35  # Processed clauses                    : 39
% 0.12/0.35  # ...of these trivial                  : 0
% 0.12/0.35  # ...subsumed                          : 0
% 0.12/0.35  # ...remaining for further processing  : 39
% 0.12/0.35  # Other redundant clauses eliminated   : 9
% 0.12/0.35  # Clauses deleted for lack of memory   : 0
% 0.12/0.35  # Backward-subsumed                    : 0
% 0.12/0.35  # Backward-rewritten                   : 0
% 0.12/0.35  # Generated clauses                    : 9
% 0.12/0.35  # ...of the previous two non-trivial   : 8
% 0.12/0.35  # Contextual simplify-reflections      : 0
% 0.12/0.35  # Paramodulations                      : 4
% 0.12/0.35  # Factorizations                       : 0
% 0.12/0.35  # Equation resolutions                 : 9
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
% 0.12/0.35  # Current number of processed clauses  : 16
% 0.12/0.35  #    Positive orientable unit clauses  : 10
% 0.12/0.35  #    Positive unorientable unit clauses: 0
% 0.12/0.35  #    Negative unit clauses             : 3
% 0.12/0.35  #    Non-unit-clauses                  : 3
% 0.12/0.35  # Current number of unprocessed clauses: 5
% 0.12/0.35  # ...number of literals in the above   : 18
% 0.12/0.35  # Current number of archived formulas  : 0
% 0.12/0.35  # Current number of archived clauses   : 22
% 0.12/0.35  # Clause-clause subsumption calls (NU) : 12
% 0.12/0.35  # Rec. Clause-clause subsumption calls : 12
% 0.12/0.35  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.35  # Unit Clause-clause subsumption calls : 1
% 0.12/0.35  # Rewrite failures with RHS unbound    : 0
% 0.12/0.35  # BW rewrite match attempts            : 12
% 0.12/0.35  # BW rewrite match successes           : 0
% 0.12/0.35  # Condensation attempts                : 0
% 0.12/0.35  # Condensation successes               : 0
% 0.12/0.35  # Termbank termtop insertions          : 1393
% 0.12/0.35  
% 0.12/0.35  # -------------------------------------------------
% 0.12/0.35  # User time                : 0.026 s
% 0.12/0.35  # System time              : 0.005 s
% 0.12/0.35  # Total time               : 0.032 s
% 0.12/0.35  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
