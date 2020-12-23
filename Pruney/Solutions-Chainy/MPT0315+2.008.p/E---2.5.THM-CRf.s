%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:41 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 (1587 expanded)
%              Number of clauses        :   40 ( 772 expanded)
%              Number of leaves         :    8 ( 406 expanded)
%              Depth                    :   17
%              Number of atoms          :  104 (2530 expanded)
%              Number of equality atoms :   45 (1243 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t127_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_xboole_0(X1,X2)
        | r1_xboole_0(X3,X4) )
     => r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(c_0_8,plain,(
    ! [X7,X8,X10,X11,X12] :
      ( ( r1_xboole_0(X7,X8)
        | r2_hidden(esk1_2(X7,X8),k3_xboole_0(X7,X8)) )
      & ( ~ r2_hidden(X12,k3_xboole_0(X10,X11))
        | ~ r1_xboole_0(X10,X11) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_9,plain,(
    ! [X14,X15] : k4_xboole_0(X14,k4_xboole_0(X14,X15)) = k3_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_10,plain,(
    ! [X13] : k3_xboole_0(X13,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_11,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_15,plain,(
    ! [X16,X17] :
      ( ( ~ r1_xboole_0(X16,X17)
        | k4_xboole_0(X16,X17) = X16 )
      & ( k4_xboole_0(X16,X17) != X16
        | r1_xboole_0(X16,X17) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_16,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_13,c_0_12])).

cnf(c_0_18,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_14,c_0_12])).

fof(c_0_19,plain,(
    ! [X5,X6] :
      ( ~ r1_xboole_0(X5,X6)
      | r1_xboole_0(X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_20,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( r2_hidden(esk1_2(X1,k1_xboole_0),k1_xboole_0)
    | r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_17])).

cnf(c_0_23,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))
    | k1_xboole_0 != X1 ),
    inference(spm,[status(thm)],[c_0_20,c_0_17])).

fof(c_0_25,plain,(
    ! [X20,X21,X22,X23] : k2_zfmisc_1(k3_xboole_0(X20,X21),k3_xboole_0(X22,X23)) = k3_xboole_0(k2_zfmisc_1(X20,X22),k2_zfmisc_1(X21,X23)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,plain,
    ( r1_xboole_0(X1,k1_xboole_0)
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k1_xboole_0),X1)
    | k1_xboole_0 != X1 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_26])).

cnf(c_0_31,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,plain,
    ( k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,X4))) = k4_xboole_0(k2_zfmisc_1(X1,X3),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_12]),c_0_12]),c_0_12])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31])])).

cnf(c_0_34,plain,
    ( k2_zfmisc_1(k4_xboole_0(X1,k1_xboole_0),k4_xboole_0(X2,k1_xboole_0)) = k4_xboole_0(k2_zfmisc_1(X1,X2),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_33]),c_0_33])).

fof(c_0_35,plain,(
    ! [X18,X19] :
      ( ( k2_zfmisc_1(X18,X19) != k1_xboole_0
        | X18 = k1_xboole_0
        | X19 = k1_xboole_0 )
      & ( X18 != k1_xboole_0
        | k2_zfmisc_1(X18,X19) = k1_xboole_0 )
      & ( X19 != k1_xboole_0
        | k2_zfmisc_1(X18,X19) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_36,plain,
    ( k4_xboole_0(k2_zfmisc_1(X1,X2),k1_xboole_0) = k2_zfmisc_1(k4_xboole_0(X1,k1_xboole_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_26]),c_0_31])])).

cnf(c_0_37,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_38,plain,
    ( k2_zfmisc_1(k4_xboole_0(X1,k1_xboole_0),X2) = k2_zfmisc_1(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_36]),c_0_31])])).

cnf(c_0_39,plain,
    ( k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,X4))) = k1_xboole_0
    | X4 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_37]),c_0_17])).

cnf(c_0_40,plain,
    ( k4_xboole_0(k2_zfmisc_1(X1,X2),k1_xboole_0) = k2_zfmisc_1(X1,X2) ),
    inference(rw,[status(thm)],[c_0_36,c_0_38])).

fof(c_0_41,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_xboole_0(X1,X2)
          | r1_xboole_0(X3,X4) )
       => r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ) ),
    inference(assume_negation,[status(cth)],[t127_zfmisc_1])).

cnf(c_0_42,plain,
    ( k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_33])).

cnf(c_0_43,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_44,negated_conjecture,
    ( ( r1_xboole_0(esk2_0,esk3_0)
      | r1_xboole_0(esk4_0,esk5_0) )
    & ~ r1_xboole_0(k2_zfmisc_1(esk2_0,esk4_0),k2_zfmisc_1(esk3_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_41])])])).

cnf(c_0_45,plain,
    ( r2_hidden(esk1_2(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)),k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X3)),k4_xboole_0(X2,k4_xboole_0(X2,X4))))
    | r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_32])).

cnf(c_0_46,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_17]),c_0_38])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_31])])).

cnf(c_0_48,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | k4_xboole_0(X1,k1_xboole_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( ~ r1_xboole_0(k2_zfmisc_1(esk2_0,esk4_0),k2_zfmisc_1(esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,plain,
    ( r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
    | ~ r1_xboole_0(X2,X4) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_26]),c_0_33]),c_0_46]),c_0_47])).

cnf(c_0_51,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_33])).

cnf(c_0_52,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk3_0)
    | r1_xboole_0(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( ~ r1_xboole_0(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,plain,
    ( r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
    | ~ r1_xboole_0(X1,X3) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_26]),c_0_33]),c_0_51]),c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_54]),c_0_55])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.34  % Computer   : n024.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 16:47:06 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.43  # AutoSched0-Mode selected heuristic G_____X1276__C12_02_nc_F1_AE_CS_SP_RG_S04AN
% 0.21/0.43  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.43  #
% 0.21/0.43  # Preprocessing time       : 0.027 s
% 0.21/0.43  # Presaturation interreduction done
% 0.21/0.43  
% 0.21/0.43  # Proof found!
% 0.21/0.43  # SZS status Theorem
% 0.21/0.43  # SZS output start CNFRefutation
% 0.21/0.43  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.21/0.43  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.21/0.43  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.21/0.43  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.21/0.43  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.21/0.43  fof(t123_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 0.21/0.43  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.21/0.43  fof(t127_zfmisc_1, conjecture, ![X1, X2, X3, X4]:((r1_xboole_0(X1,X2)|r1_xboole_0(X3,X4))=>r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 0.21/0.43  fof(c_0_8, plain, ![X7, X8, X10, X11, X12]:((r1_xboole_0(X7,X8)|r2_hidden(esk1_2(X7,X8),k3_xboole_0(X7,X8)))&(~r2_hidden(X12,k3_xboole_0(X10,X11))|~r1_xboole_0(X10,X11))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.21/0.43  fof(c_0_9, plain, ![X14, X15]:k4_xboole_0(X14,k4_xboole_0(X14,X15))=k3_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.21/0.43  fof(c_0_10, plain, ![X13]:k3_xboole_0(X13,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.21/0.43  cnf(c_0_11, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.43  cnf(c_0_12, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.43  cnf(c_0_13, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.43  cnf(c_0_14, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.43  fof(c_0_15, plain, ![X16, X17]:((~r1_xboole_0(X16,X17)|k4_xboole_0(X16,X17)=X16)&(k4_xboole_0(X16,X17)!=X16|r1_xboole_0(X16,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.21/0.43  cnf(c_0_16, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 0.21/0.43  cnf(c_0_17, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_13, c_0_12])).
% 0.21/0.43  cnf(c_0_18, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_14, c_0_12])).
% 0.21/0.43  fof(c_0_19, plain, ![X5, X6]:(~r1_xboole_0(X5,X6)|r1_xboole_0(X6,X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.21/0.43  cnf(c_0_20, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.43  cnf(c_0_21, plain, (~r2_hidden(X1,k1_xboole_0)|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.21/0.43  cnf(c_0_22, plain, (r2_hidden(esk1_2(X1,k1_xboole_0),k1_xboole_0)|r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_18, c_0_17])).
% 0.21/0.43  cnf(c_0_23, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.43  cnf(c_0_24, plain, (r1_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))|k1_xboole_0!=X1), inference(spm,[status(thm)],[c_0_20, c_0_17])).
% 0.21/0.43  fof(c_0_25, plain, ![X20, X21, X22, X23]:k2_zfmisc_1(k3_xboole_0(X20,X21),k3_xboole_0(X22,X23))=k3_xboole_0(k2_zfmisc_1(X20,X22),k2_zfmisc_1(X21,X23)), inference(variable_rename,[status(thm)],[t123_zfmisc_1])).
% 0.21/0.43  cnf(c_0_26, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.43  cnf(c_0_27, plain, (r1_xboole_0(X1,k1_xboole_0)|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.21/0.43  cnf(c_0_28, plain, (r1_xboole_0(k4_xboole_0(X1,k1_xboole_0),X1)|k1_xboole_0!=X1), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.21/0.43  cnf(c_0_29, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.43  cnf(c_0_30, plain, (k4_xboole_0(X1,X1)=k1_xboole_0|~r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_17, c_0_26])).
% 0.21/0.43  cnf(c_0_31, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.21/0.43  cnf(c_0_32, plain, (k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,X4)))=k4_xboole_0(k2_zfmisc_1(X1,X3),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_12]), c_0_12]), c_0_12])).
% 0.21/0.43  cnf(c_0_33, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31])])).
% 0.21/0.43  cnf(c_0_34, plain, (k2_zfmisc_1(k4_xboole_0(X1,k1_xboole_0),k4_xboole_0(X2,k1_xboole_0))=k4_xboole_0(k2_zfmisc_1(X1,X2),k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_33]), c_0_33])).
% 0.21/0.43  fof(c_0_35, plain, ![X18, X19]:((k2_zfmisc_1(X18,X19)!=k1_xboole_0|(X18=k1_xboole_0|X19=k1_xboole_0))&((X18!=k1_xboole_0|k2_zfmisc_1(X18,X19)=k1_xboole_0)&(X19!=k1_xboole_0|k2_zfmisc_1(X18,X19)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.21/0.43  cnf(c_0_36, plain, (k4_xboole_0(k2_zfmisc_1(X1,X2),k1_xboole_0)=k2_zfmisc_1(k4_xboole_0(X1,k1_xboole_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_26]), c_0_31])])).
% 0.21/0.43  cnf(c_0_37, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.43  cnf(c_0_38, plain, (k2_zfmisc_1(k4_xboole_0(X1,k1_xboole_0),X2)=k2_zfmisc_1(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_36]), c_0_31])])).
% 0.21/0.43  cnf(c_0_39, plain, (k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,X4)))=k1_xboole_0|X4!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_37]), c_0_17])).
% 0.21/0.43  cnf(c_0_40, plain, (k4_xboole_0(k2_zfmisc_1(X1,X2),k1_xboole_0)=k2_zfmisc_1(X1,X2)), inference(rw,[status(thm)],[c_0_36, c_0_38])).
% 0.21/0.43  fof(c_0_41, negated_conjecture, ~(![X1, X2, X3, X4]:((r1_xboole_0(X1,X2)|r1_xboole_0(X3,X4))=>r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)))), inference(assume_negation,[status(cth)],[t127_zfmisc_1])).
% 0.21/0.43  cnf(c_0_42, plain, (k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_33])).
% 0.21/0.43  cnf(c_0_43, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.43  fof(c_0_44, negated_conjecture, ((r1_xboole_0(esk2_0,esk3_0)|r1_xboole_0(esk4_0,esk5_0))&~r1_xboole_0(k2_zfmisc_1(esk2_0,esk4_0),k2_zfmisc_1(esk3_0,esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_41])])])).
% 0.21/0.43  cnf(c_0_45, plain, (r2_hidden(esk1_2(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)),k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X3)),k4_xboole_0(X2,k4_xboole_0(X2,X4))))|r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))), inference(spm,[status(thm)],[c_0_18, c_0_32])).
% 0.21/0.43  cnf(c_0_46, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_17]), c_0_38])).
% 0.21/0.43  cnf(c_0_47, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_31])])).
% 0.21/0.43  cnf(c_0_48, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|k4_xboole_0(X1,k1_xboole_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_38])).
% 0.21/0.43  cnf(c_0_49, negated_conjecture, (~r1_xboole_0(k2_zfmisc_1(esk2_0,esk4_0),k2_zfmisc_1(esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.21/0.43  cnf(c_0_50, plain, (r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))|~r1_xboole_0(X2,X4)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_26]), c_0_33]), c_0_46]), c_0_47])).
% 0.21/0.43  cnf(c_0_51, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_48, c_0_33])).
% 0.21/0.43  cnf(c_0_52, negated_conjecture, (r1_xboole_0(esk2_0,esk3_0)|r1_xboole_0(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.21/0.43  cnf(c_0_53, negated_conjecture, (~r1_xboole_0(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.21/0.43  cnf(c_0_54, plain, (r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))|~r1_xboole_0(X1,X3)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_26]), c_0_33]), c_0_51]), c_0_47])).
% 0.21/0.43  cnf(c_0_55, negated_conjecture, (r1_xboole_0(esk2_0,esk3_0)), inference(sr,[status(thm)],[c_0_52, c_0_53])).
% 0.21/0.43  cnf(c_0_56, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_54]), c_0_55])]), ['proof']).
% 0.21/0.43  # SZS output end CNFRefutation
% 0.21/0.43  # Proof object total steps             : 57
% 0.21/0.43  # Proof object clause steps            : 40
% 0.21/0.43  # Proof object formula steps           : 17
% 0.21/0.43  # Proof object conjectures             : 8
% 0.21/0.43  # Proof object clause conjectures      : 5
% 0.21/0.43  # Proof object formula conjectures     : 3
% 0.21/0.43  # Proof object initial clauses used    : 12
% 0.21/0.43  # Proof object initial formulas used   : 8
% 0.21/0.43  # Proof object generating inferences   : 20
% 0.21/0.43  # Proof object simplifying inferences  : 29
% 0.21/0.43  # Training examples: 0 positive, 0 negative
% 0.21/0.43  # Parsed axioms                        : 8
% 0.21/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.43  # Initial clauses                      : 13
% 0.21/0.43  # Removed in clause preprocessing      : 1
% 0.21/0.43  # Initial clauses in saturation        : 12
% 0.21/0.43  # Processed clauses                    : 831
% 0.21/0.43  # ...of these trivial                  : 5
% 0.21/0.43  # ...subsumed                          : 643
% 0.21/0.43  # ...remaining for further processing  : 183
% 0.21/0.43  # Other redundant clauses eliminated   : 16
% 0.21/0.43  # Clauses deleted for lack of memory   : 0
% 0.21/0.43  # Backward-subsumed                    : 4
% 0.21/0.43  # Backward-rewritten                   : 22
% 0.21/0.43  # Generated clauses                    : 3862
% 0.21/0.43  # ...of the previous two non-trivial   : 2538
% 0.21/0.43  # Contextual simplify-reflections      : 0
% 0.21/0.43  # Paramodulations                      : 3842
% 0.21/0.43  # Factorizations                       : 3
% 0.21/0.43  # Equation resolutions                 : 16
% 0.21/0.43  # Propositional unsat checks           : 0
% 0.21/0.43  #    Propositional check models        : 0
% 0.21/0.43  #    Propositional check unsatisfiable : 0
% 0.21/0.43  #    Propositional clauses             : 0
% 0.21/0.43  #    Propositional clauses after purity: 0
% 0.21/0.43  #    Propositional unsat core size     : 0
% 0.21/0.43  #    Propositional preprocessing time  : 0.000
% 0.21/0.43  #    Propositional encoding time       : 0.000
% 0.21/0.43  #    Propositional solver time         : 0.000
% 0.21/0.43  #    Success case prop preproc time    : 0.000
% 0.21/0.43  #    Success case prop encoding time   : 0.000
% 0.21/0.43  #    Success case prop solver time     : 0.000
% 0.21/0.43  # Current number of processed clauses  : 144
% 0.21/0.43  #    Positive orientable unit clauses  : 15
% 0.21/0.43  #    Positive unorientable unit clauses: 0
% 0.21/0.43  #    Negative unit clauses             : 7
% 0.21/0.43  #    Non-unit-clauses                  : 122
% 0.21/0.43  # Current number of unprocessed clauses: 1629
% 0.21/0.43  # ...number of literals in the above   : 4419
% 0.21/0.43  # Current number of archived formulas  : 0
% 0.21/0.43  # Current number of archived clauses   : 40
% 0.21/0.43  # Clause-clause subsumption calls (NU) : 3241
% 0.21/0.43  # Rec. Clause-clause subsumption calls : 3122
% 0.21/0.43  # Non-unit clause-clause subsumptions  : 547
% 0.21/0.43  # Unit Clause-clause subsumption calls : 118
% 0.21/0.43  # Rewrite failures with RHS unbound    : 0
% 0.21/0.43  # BW rewrite match attempts            : 30
% 0.21/0.43  # BW rewrite match successes           : 13
% 0.21/0.43  # Condensation attempts                : 0
% 0.21/0.43  # Condensation successes               : 0
% 0.21/0.43  # Termbank termtop insertions          : 61936
% 0.21/0.43  
% 0.21/0.43  # -------------------------------------------------
% 0.21/0.43  # User time                : 0.075 s
% 0.21/0.43  # System time              : 0.008 s
% 0.21/0.43  # Total time               : 0.083 s
% 0.21/0.43  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
