%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:42 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 167 expanded)
%              Number of clauses        :   40 (  71 expanded)
%              Number of leaves         :   14 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :  102 ( 308 expanded)
%              Number of equality atoms :   52 ( 131 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t32_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => k7_subset_1(X1,X2,X3) = k9_subset_1(X1,X2,k3_subset_1(X1,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(t37_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(commutativity_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k9_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => k7_subset_1(X1,X2,X3) = k9_subset_1(X1,X2,k3_subset_1(X1,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t32_subset_1])).

fof(c_0_15,plain,(
    ! [X68,X69] :
      ( ~ m1_subset_1(X69,k1_zfmisc_1(X68))
      | m1_subset_1(k3_subset_1(X68,X69),k1_zfmisc_1(X68)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_16,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))
    & k7_subset_1(esk3_0,esk4_0,esk5_0) != k9_subset_1(esk3_0,esk4_0,k3_subset_1(esk3_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_17,plain,(
    ! [X66,X67] :
      ( ~ m1_subset_1(X67,k1_zfmisc_1(X66))
      | k3_subset_1(X66,X67) = k4_xboole_0(X66,X67) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_18,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X73,X74] :
      ( ~ m1_subset_1(X74,k1_zfmisc_1(X73))
      | k3_subset_1(X73,k3_subset_1(X73,X74)) = X74 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

fof(c_0_22,plain,(
    ! [X21,X22] : r1_tarski(k3_xboole_0(X21,X22),X21) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_23,plain,(
    ! [X36,X37] : k4_xboole_0(X36,k4_xboole_0(X36,X37)) = k3_xboole_0(X36,X37) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk3_0,esk4_0),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( k3_subset_1(esk3_0,esk4_0) = k4_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_19])).

cnf(c_0_26,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(k4_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( k3_subset_1(esk3_0,k4_xboole_0(esk3_0,esk4_0)) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_19]),c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_32,plain,(
    ! [X78,X79,X80] :
      ( ~ m1_subset_1(X80,k1_zfmisc_1(X78))
      | k9_subset_1(X78,X79,X80) = k3_xboole_0(X79,X80) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_33,plain,(
    ! [X45,X46,X47] : k4_xboole_0(X45,k4_xboole_0(X46,X47)) = k2_xboole_0(k4_xboole_0(X45,X46),k3_xboole_0(X45,X47)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

fof(c_0_34,plain,(
    ! [X25,X26] :
      ( ( k4_xboole_0(X25,X26) != k1_xboole_0
        | r1_tarski(X25,X26) )
      & ( ~ r1_tarski(X25,X26)
        | k4_xboole_0(X25,X26) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).

cnf(c_0_35,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_29]),c_0_30])).

fof(c_0_37,plain,(
    ! [X19,X20] :
      ( ~ r1_tarski(X19,X20)
      | k2_xboole_0(X19,X20) = X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_38,plain,(
    ! [X24] : r1_tarski(k1_xboole_0,X24) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_39,plain,(
    ! [X75,X76,X77] :
      ( ~ m1_subset_1(X76,k1_zfmisc_1(X75))
      | k7_subset_1(X75,X76,X77) = k4_xboole_0(X76,X77) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_40,plain,(
    ! [X63,X64,X65] :
      ( ~ m1_subset_1(X65,k1_zfmisc_1(X63))
      | k9_subset_1(X63,X64,X65) = k9_subset_1(X63,X65,X64) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk3_0,esk5_0),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( k3_subset_1(esk3_0,esk5_0) = k4_xboole_0(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_31])).

cnf(c_0_43,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_44,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_48,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_49,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,negated_conjecture,
    ( k7_subset_1(esk3_0,esk4_0,esk5_0) != k9_subset_1(esk3_0,esk4_0,k3_subset_1(esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_51,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_52,plain,
    ( k9_subset_1(X2,X3,X1) = k9_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(k4_xboole_0(esk3_0,esk5_0),k1_zfmisc_1(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_54,plain,
    ( k9_subset_1(X2,X3,X1) = k4_xboole_0(X3,k4_xboole_0(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_43,c_0_28])).

cnf(c_0_55,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_56,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[c_0_45,c_0_28])).

cnf(c_0_57,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_58,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( k3_subset_1(esk3_0,k4_xboole_0(esk3_0,esk5_0)) = esk5_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_31]),c_0_42])).

cnf(c_0_60,negated_conjecture,
    ( k7_subset_1(esk3_0,esk4_0,esk5_0) != k9_subset_1(esk3_0,esk4_0,k4_xboole_0(esk3_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_50,c_0_42])).

cnf(c_0_61,negated_conjecture,
    ( k7_subset_1(esk3_0,esk4_0,X1) = k4_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_19])).

cnf(c_0_62,negated_conjecture,
    ( k9_subset_1(esk3_0,k4_xboole_0(esk3_0,esk5_0),X1) = k9_subset_1(esk3_0,X1,k4_xboole_0(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_63,negated_conjecture,
    ( k9_subset_1(esk3_0,X1,esk4_0) = k4_xboole_0(X1,k4_xboole_0(X1,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_19])).

cnf(c_0_64,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_28]),c_0_28])).

cnf(c_0_65,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1)) = k4_xboole_0(esk4_0,k4_xboole_0(esk3_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])).

cnf(c_0_66,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0)) = esk5_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_53]),c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( k9_subset_1(esk3_0,esk4_0,k4_xboole_0(esk3_0,esk5_0)) != k4_xboole_0(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64]),c_0_65]),c_0_66]),c_0_67]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:15:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.35  # Version: 2.5pre002
% 0.21/0.35  # No SInE strategy applied
% 0.21/0.35  # Trying AutoSched0 for 299 seconds
% 1.65/1.83  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 1.65/1.83  # and selection function SelectNegativeLiterals.
% 1.65/1.83  #
% 1.65/1.83  # Preprocessing time       : 0.029 s
% 1.65/1.83  # Presaturation interreduction done
% 1.65/1.83  
% 1.65/1.83  # Proof found!
% 1.65/1.83  # SZS status Theorem
% 1.65/1.83  # SZS output start CNFRefutation
% 1.65/1.83  fof(t32_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k9_subset_1(X1,X2,k3_subset_1(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_subset_1)).
% 1.65/1.83  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 1.65/1.83  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 1.65/1.83  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 1.65/1.83  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.65/1.83  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.65/1.83  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 1.65/1.83  fof(t52_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 1.65/1.83  fof(t37_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 1.65/1.83  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.65/1.83  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.65/1.83  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 1.65/1.83  fof(commutativity_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k9_subset_1(X1,X3,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 1.65/1.83  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.65/1.83  fof(c_0_14, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k9_subset_1(X1,X2,k3_subset_1(X1,X3))))), inference(assume_negation,[status(cth)],[t32_subset_1])).
% 1.65/1.83  fof(c_0_15, plain, ![X68, X69]:(~m1_subset_1(X69,k1_zfmisc_1(X68))|m1_subset_1(k3_subset_1(X68,X69),k1_zfmisc_1(X68))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 1.65/1.83  fof(c_0_16, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))&k7_subset_1(esk3_0,esk4_0,esk5_0)!=k9_subset_1(esk3_0,esk4_0,k3_subset_1(esk3_0,esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 1.65/1.83  fof(c_0_17, plain, ![X66, X67]:(~m1_subset_1(X67,k1_zfmisc_1(X66))|k3_subset_1(X66,X67)=k4_xboole_0(X66,X67)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 1.65/1.83  cnf(c_0_18, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.65/1.83  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.65/1.83  cnf(c_0_20, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.65/1.83  fof(c_0_21, plain, ![X73, X74]:(~m1_subset_1(X74,k1_zfmisc_1(X73))|k3_subset_1(X73,k3_subset_1(X73,X74))=X74), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 1.65/1.83  fof(c_0_22, plain, ![X21, X22]:r1_tarski(k3_xboole_0(X21,X22),X21), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 1.65/1.83  fof(c_0_23, plain, ![X36, X37]:k4_xboole_0(X36,k4_xboole_0(X36,X37))=k3_xboole_0(X36,X37), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 1.65/1.83  cnf(c_0_24, negated_conjecture, (m1_subset_1(k3_subset_1(esk3_0,esk4_0),k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 1.65/1.83  cnf(c_0_25, negated_conjecture, (k3_subset_1(esk3_0,esk4_0)=k4_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_20, c_0_19])).
% 1.65/1.83  cnf(c_0_26, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.65/1.83  cnf(c_0_27, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.65/1.83  cnf(c_0_28, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.65/1.83  cnf(c_0_29, negated_conjecture, (m1_subset_1(k4_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk3_0))), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 1.65/1.83  cnf(c_0_30, negated_conjecture, (k3_subset_1(esk3_0,k4_xboole_0(esk3_0,esk4_0))=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_19]), c_0_25])).
% 1.65/1.83  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.65/1.83  fof(c_0_32, plain, ![X78, X79, X80]:(~m1_subset_1(X80,k1_zfmisc_1(X78))|k9_subset_1(X78,X79,X80)=k3_xboole_0(X79,X80)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 1.65/1.83  fof(c_0_33, plain, ![X45, X46, X47]:k4_xboole_0(X45,k4_xboole_0(X46,X47))=k2_xboole_0(k4_xboole_0(X45,X46),k3_xboole_0(X45,X47)), inference(variable_rename,[status(thm)],[t52_xboole_1])).
% 1.65/1.83  fof(c_0_34, plain, ![X25, X26]:((k4_xboole_0(X25,X26)!=k1_xboole_0|r1_tarski(X25,X26))&(~r1_tarski(X25,X26)|k4_xboole_0(X25,X26)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).
% 1.65/1.83  cnf(c_0_35, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 1.65/1.83  cnf(c_0_36, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_29]), c_0_30])).
% 1.65/1.83  fof(c_0_37, plain, ![X19, X20]:(~r1_tarski(X19,X20)|k2_xboole_0(X19,X20)=X20), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 1.65/1.83  fof(c_0_38, plain, ![X24]:r1_tarski(k1_xboole_0,X24), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 1.65/1.83  fof(c_0_39, plain, ![X75, X76, X77]:(~m1_subset_1(X76,k1_zfmisc_1(X75))|k7_subset_1(X75,X76,X77)=k4_xboole_0(X76,X77)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 1.65/1.83  fof(c_0_40, plain, ![X63, X64, X65]:(~m1_subset_1(X65,k1_zfmisc_1(X63))|k9_subset_1(X63,X64,X65)=k9_subset_1(X63,X65,X64)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).
% 1.65/1.83  cnf(c_0_41, negated_conjecture, (m1_subset_1(k3_subset_1(esk3_0,esk5_0),k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_18, c_0_31])).
% 1.65/1.83  cnf(c_0_42, negated_conjecture, (k3_subset_1(esk3_0,esk5_0)=k4_xboole_0(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_20, c_0_31])).
% 1.65/1.83  cnf(c_0_43, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.65/1.83  fof(c_0_44, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 1.65/1.83  cnf(c_0_45, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.65/1.83  cnf(c_0_46, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.65/1.83  cnf(c_0_47, negated_conjecture, (r1_tarski(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 1.65/1.83  cnf(c_0_48, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 1.65/1.83  cnf(c_0_49, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 1.65/1.83  cnf(c_0_50, negated_conjecture, (k7_subset_1(esk3_0,esk4_0,esk5_0)!=k9_subset_1(esk3_0,esk4_0,k3_subset_1(esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.65/1.83  cnf(c_0_51, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.65/1.83  cnf(c_0_52, plain, (k9_subset_1(X2,X3,X1)=k9_subset_1(X2,X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.65/1.83  cnf(c_0_53, negated_conjecture, (m1_subset_1(k4_xboole_0(esk3_0,esk5_0),k1_zfmisc_1(esk3_0))), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 1.65/1.83  cnf(c_0_54, plain, (k9_subset_1(X2,X3,X1)=k4_xboole_0(X3,k4_xboole_0(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_43, c_0_28])).
% 1.65/1.83  cnf(c_0_55, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 1.65/1.83  cnf(c_0_56, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3)))), inference(rw,[status(thm)],[c_0_45, c_0_28])).
% 1.65/1.83  cnf(c_0_57, negated_conjecture, (k4_xboole_0(esk4_0,esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 1.65/1.83  cnf(c_0_58, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 1.65/1.83  cnf(c_0_59, negated_conjecture, (k3_subset_1(esk3_0,k4_xboole_0(esk3_0,esk5_0))=esk5_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_31]), c_0_42])).
% 1.65/1.83  cnf(c_0_60, negated_conjecture, (k7_subset_1(esk3_0,esk4_0,esk5_0)!=k9_subset_1(esk3_0,esk4_0,k4_xboole_0(esk3_0,esk5_0))), inference(rw,[status(thm)],[c_0_50, c_0_42])).
% 1.65/1.83  cnf(c_0_61, negated_conjecture, (k7_subset_1(esk3_0,esk4_0,X1)=k4_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_51, c_0_19])).
% 1.65/1.83  cnf(c_0_62, negated_conjecture, (k9_subset_1(esk3_0,k4_xboole_0(esk3_0,esk5_0),X1)=k9_subset_1(esk3_0,X1,k4_xboole_0(esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 1.65/1.83  cnf(c_0_63, negated_conjecture, (k9_subset_1(esk3_0,X1,esk4_0)=k4_xboole_0(X1,k4_xboole_0(X1,esk4_0))), inference(spm,[status(thm)],[c_0_54, c_0_19])).
% 1.65/1.83  cnf(c_0_64, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_28]), c_0_28])).
% 1.65/1.83  cnf(c_0_65, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,X1))=k4_xboole_0(esk4_0,k4_xboole_0(esk3_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])).
% 1.65/1.83  cnf(c_0_66, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0))=esk5_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_53]), c_0_59])).
% 1.65/1.83  cnf(c_0_67, negated_conjecture, (k9_subset_1(esk3_0,esk4_0,k4_xboole_0(esk3_0,esk5_0))!=k4_xboole_0(esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_60, c_0_61])).
% 1.65/1.83  cnf(c_0_68, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64]), c_0_65]), c_0_66]), c_0_67]), ['proof']).
% 1.65/1.83  # SZS output end CNFRefutation
% 1.65/1.83  # Proof object total steps             : 69
% 1.65/1.83  # Proof object clause steps            : 40
% 1.65/1.83  # Proof object formula steps           : 29
% 1.65/1.83  # Proof object conjectures             : 25
% 1.65/1.83  # Proof object clause conjectures      : 22
% 1.65/1.83  # Proof object formula conjectures     : 3
% 1.65/1.83  # Proof object initial clauses used    : 16
% 1.65/1.83  # Proof object initial formulas used   : 14
% 1.65/1.83  # Proof object generating inferences   : 16
% 1.65/1.83  # Proof object simplifying inferences  : 18
% 1.65/1.83  # Training examples: 0 positive, 0 negative
% 1.65/1.83  # Parsed axioms                        : 34
% 1.65/1.83  # Removed by relevancy pruning/SinE    : 0
% 1.65/1.83  # Initial clauses                      : 46
% 1.65/1.83  # Removed in clause preprocessing      : 2
% 1.65/1.83  # Initial clauses in saturation        : 44
% 1.65/1.83  # Processed clauses                    : 6397
% 1.65/1.83  # ...of these trivial                  : 193
% 1.65/1.83  # ...subsumed                          : 4657
% 1.65/1.83  # ...remaining for further processing  : 1547
% 1.65/1.83  # Other redundant clauses eliminated   : 1329
% 1.65/1.83  # Clauses deleted for lack of memory   : 0
% 1.65/1.83  # Backward-subsumed                    : 83
% 1.65/1.83  # Backward-rewritten                   : 303
% 1.65/1.83  # Generated clauses                    : 118742
% 1.65/1.83  # ...of the previous two non-trivial   : 101609
% 1.65/1.83  # Contextual simplify-reflections      : 0
% 1.65/1.83  # Paramodulations                      : 117399
% 1.65/1.83  # Factorizations                       : 12
% 1.65/1.83  # Equation resolutions                 : 1331
% 1.65/1.83  # Propositional unsat checks           : 0
% 1.65/1.83  #    Propositional check models        : 0
% 1.65/1.83  #    Propositional check unsatisfiable : 0
% 1.65/1.83  #    Propositional clauses             : 0
% 1.65/1.83  #    Propositional clauses after purity: 0
% 1.65/1.83  #    Propositional unsat core size     : 0
% 1.65/1.83  #    Propositional preprocessing time  : 0.000
% 1.65/1.83  #    Propositional encoding time       : 0.000
% 1.65/1.83  #    Propositional solver time         : 0.000
% 1.65/1.83  #    Success case prop preproc time    : 0.000
% 1.65/1.83  #    Success case prop encoding time   : 0.000
% 1.65/1.83  #    Success case prop solver time     : 0.000
% 1.65/1.83  # Current number of processed clauses  : 1113
% 1.65/1.83  #    Positive orientable unit clauses  : 327
% 1.65/1.83  #    Positive unorientable unit clauses: 17
% 1.65/1.83  #    Negative unit clauses             : 11
% 1.65/1.83  #    Non-unit-clauses                  : 758
% 1.65/1.83  # Current number of unprocessed clauses: 94205
% 1.65/1.83  # ...number of literals in the above   : 238967
% 1.65/1.83  # Current number of archived formulas  : 0
% 1.65/1.83  # Current number of archived clauses   : 431
% 1.65/1.83  # Clause-clause subsumption calls (NU) : 60157
% 1.65/1.83  # Rec. Clause-clause subsumption calls : 52804
% 1.65/1.83  # Non-unit clause-clause subsumptions  : 3743
% 1.65/1.83  # Unit Clause-clause subsumption calls : 9646
% 1.65/1.83  # Rewrite failures with RHS unbound    : 1873
% 1.65/1.83  # BW rewrite match attempts            : 4006
% 1.65/1.83  # BW rewrite match successes           : 321
% 1.65/1.83  # Condensation attempts                : 0
% 1.65/1.83  # Condensation successes               : 0
% 1.65/1.83  # Termbank termtop insertions          : 1834001
% 1.65/1.84  
% 1.65/1.84  # -------------------------------------------------
% 1.65/1.84  # User time                : 1.432 s
% 1.65/1.84  # System time              : 0.059 s
% 1.65/1.84  # Total time               : 1.491 s
% 1.65/1.84  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
