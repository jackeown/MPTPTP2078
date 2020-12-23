%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:13 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   50 (  78 expanded)
%              Number of clauses        :   27 (  33 expanded)
%              Number of leaves         :   11 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :  113 ( 195 expanded)
%              Number of equality atoms :   43 (  68 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t139_zfmisc_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2,X3,X4] :
          ( ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
            | r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X4,X3)) )
         => r1_tarski(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_zfmisc_1)).

fof(t138_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
     => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
        | ( r1_tarski(X1,X3)
          & r1_tarski(X2,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t18_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k3_xboole_0(X2,X3))
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2,X3,X4] :
            ( ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
              | r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X4,X3)) )
           => r1_tarski(X2,X4) ) ) ),
    inference(assume_negation,[status(cth)],[t139_zfmisc_1])).

fof(c_0_12,plain,(
    ! [X28,X29,X30,X31] :
      ( ( r1_tarski(X28,X30)
        | k2_zfmisc_1(X28,X29) = k1_xboole_0
        | ~ r1_tarski(k2_zfmisc_1(X28,X29),k2_zfmisc_1(X30,X31)) )
      & ( r1_tarski(X29,X31)
        | k2_zfmisc_1(X28,X29) = k1_xboole_0
        | ~ r1_tarski(k2_zfmisc_1(X28,X29),k2_zfmisc_1(X30,X31)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_zfmisc_1])])])).

fof(c_0_13,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0)
    & ( r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))
      | r1_tarski(k2_zfmisc_1(esk4_0,esk3_0),k2_zfmisc_1(esk6_0,esk5_0)) )
    & ~ r1_tarski(esk4_0,esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X2)
    | k2_zfmisc_1(X1,X3) = k1_xboole_0
    | ~ r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))
    | r1_tarski(k2_zfmisc_1(esk4_0,esk3_0),k2_zfmisc_1(esk6_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( ~ r1_tarski(esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X17,X18] :
      ( ( k4_xboole_0(X17,X18) != k1_xboole_0
        | r1_tarski(X17,X18) )
      & ( ~ r1_tarski(X17,X18)
        | k4_xboole_0(X17,X18) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_18,plain,(
    ! [X19,X20] : k4_xboole_0(X19,X20) = k5_xboole_0(X19,k3_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_19,plain,(
    ! [X26,X27] :
      ( ( k2_zfmisc_1(X26,X27) != k1_xboole_0
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0 )
      & ( X26 != k1_xboole_0
        | k2_zfmisc_1(X26,X27) = k1_xboole_0 )
      & ( X27 != k1_xboole_0
        | k2_zfmisc_1(X26,X27) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X2)
    | k2_zfmisc_1(X3,X1) = k1_xboole_0
    | ~ r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( k2_zfmisc_1(esk4_0,esk3_0) = k1_xboole_0
    | r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

fof(c_0_22,plain,(
    ! [X21,X22,X23] :
      ( ~ r1_tarski(X21,k3_xboole_0(X22,X23))
      | r1_tarski(X21,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_xboole_1])])).

fof(c_0_23,plain,(
    ! [X24] : k3_xboole_0(X24,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
    ! [X25] : k5_xboole_0(X25,k1_xboole_0) = X25 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_27,plain,(
    ! [X9,X10] :
      ( ( ~ r1_xboole_0(X9,X10)
        | k3_xboole_0(X9,X10) = k1_xboole_0 )
      & ( k3_xboole_0(X9,X10) != k1_xboole_0
        | r1_xboole_0(X9,X10) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_28,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( k2_zfmisc_1(esk4_0,esk3_0) = k1_xboole_0
    | k2_zfmisc_1(esk3_0,esk4_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_16])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_34,plain,(
    ! [X11,X12,X14,X15,X16] :
      ( ( r1_xboole_0(X11,X12)
        | r2_hidden(esk2_2(X11,X12),k3_xboole_0(X11,X12)) )
      & ( ~ r2_hidden(X16,k3_xboole_0(X14,X15))
        | ~ r1_xboole_0(X14,X15) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_35,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_28])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(er,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_31]),c_0_33])])).

cnf(c_0_39,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_31])).

fof(c_0_41,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_42,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_36])).

cnf(c_0_43,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_31])).

cnf(c_0_45,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_47,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43])])).

cnf(c_0_48,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_48])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:04:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S053N
% 0.13/0.38  # and selection function HSelectMinInfpos.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t139_zfmisc_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2, X3, X4]:((r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))|r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X4,X3)))=>r1_tarski(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_zfmisc_1)).
% 0.13/0.38  fof(t138_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 0.13/0.38  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.13/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.13/0.38  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.13/0.38  fof(t18_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k3_xboole_0(X2,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 0.13/0.38  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.13/0.38  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.13/0.38  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.13/0.38  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.13/0.38  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.38  fof(c_0_11, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2, X3, X4]:((r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))|r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X4,X3)))=>r1_tarski(X2,X4)))), inference(assume_negation,[status(cth)],[t139_zfmisc_1])).
% 0.13/0.38  fof(c_0_12, plain, ![X28, X29, X30, X31]:((r1_tarski(X28,X30)|k2_zfmisc_1(X28,X29)=k1_xboole_0|~r1_tarski(k2_zfmisc_1(X28,X29),k2_zfmisc_1(X30,X31)))&(r1_tarski(X29,X31)|k2_zfmisc_1(X28,X29)=k1_xboole_0|~r1_tarski(k2_zfmisc_1(X28,X29),k2_zfmisc_1(X30,X31)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t138_zfmisc_1])])])).
% 0.13/0.38  fof(c_0_13, negated_conjecture, (~v1_xboole_0(esk3_0)&((r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))|r1_tarski(k2_zfmisc_1(esk4_0,esk3_0),k2_zfmisc_1(esk6_0,esk5_0)))&~r1_tarski(esk4_0,esk6_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.13/0.38  cnf(c_0_14, plain, (r1_tarski(X1,X2)|k2_zfmisc_1(X1,X3)=k1_xboole_0|~r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_15, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))|r1_tarski(k2_zfmisc_1(esk4_0,esk3_0),k2_zfmisc_1(esk6_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_16, negated_conjecture, (~r1_tarski(esk4_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  fof(c_0_17, plain, ![X17, X18]:((k4_xboole_0(X17,X18)!=k1_xboole_0|r1_tarski(X17,X18))&(~r1_tarski(X17,X18)|k4_xboole_0(X17,X18)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.13/0.38  fof(c_0_18, plain, ![X19, X20]:k4_xboole_0(X19,X20)=k5_xboole_0(X19,k3_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.13/0.38  fof(c_0_19, plain, ![X26, X27]:((k2_zfmisc_1(X26,X27)!=k1_xboole_0|(X26=k1_xboole_0|X27=k1_xboole_0))&((X26!=k1_xboole_0|k2_zfmisc_1(X26,X27)=k1_xboole_0)&(X27!=k1_xboole_0|k2_zfmisc_1(X26,X27)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.13/0.38  cnf(c_0_20, plain, (r1_tarski(X1,X2)|k2_zfmisc_1(X3,X1)=k1_xboole_0|~r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (k2_zfmisc_1(esk4_0,esk3_0)=k1_xboole_0|r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])).
% 0.13/0.38  fof(c_0_22, plain, ![X21, X22, X23]:(~r1_tarski(X21,k3_xboole_0(X22,X23))|r1_tarski(X21,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_xboole_1])])).
% 0.13/0.38  fof(c_0_23, plain, ![X24]:k3_xboole_0(X24,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.13/0.38  cnf(c_0_24, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_25, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  fof(c_0_26, plain, ![X25]:k5_xboole_0(X25,k1_xboole_0)=X25, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.13/0.38  fof(c_0_27, plain, ![X9, X10]:((~r1_xboole_0(X9,X10)|k3_xboole_0(X9,X10)=k1_xboole_0)&(k3_xboole_0(X9,X10)!=k1_xboole_0|r1_xboole_0(X9,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.13/0.38  cnf(c_0_28, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (k2_zfmisc_1(esk4_0,esk3_0)=k1_xboole_0|k2_zfmisc_1(esk3_0,esk4_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_16])).
% 0.13/0.38  cnf(c_0_30, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_31, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_32, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.13/0.38  cnf(c_0_33, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.38  fof(c_0_34, plain, ![X11, X12, X14, X15, X16]:((r1_xboole_0(X11,X12)|r2_hidden(esk2_2(X11,X12),k3_xboole_0(X11,X12)))&(~r2_hidden(X16,k3_xboole_0(X14,X15))|~r1_xboole_0(X14,X15))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.13/0.38  cnf(c_0_35, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (esk4_0=k1_xboole_0|esk3_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_28])).
% 0.13/0.38  cnf(c_0_37, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.38  cnf(c_0_38, plain, (r1_tarski(k1_xboole_0,k1_xboole_0)), inference(er,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_31]), c_0_33])])).
% 0.13/0.38  cnf(c_0_39, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.38  cnf(c_0_40, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_35, c_0_31])).
% 0.13/0.38  fof(c_0_41, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (esk3_0=k1_xboole_0|~r1_tarski(k1_xboole_0,esk6_0)), inference(spm,[status(thm)],[c_0_16, c_0_36])).
% 0.13/0.38  cnf(c_0_43, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.13/0.38  cnf(c_0_44, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_31])).
% 0.13/0.38  cnf(c_0_45, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, (esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43])])).
% 0.13/0.38  cnf(c_0_48, plain, (v1_xboole_0(k1_xboole_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_48])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 50
% 0.13/0.38  # Proof object clause steps            : 27
% 0.13/0.38  # Proof object formula steps           : 23
% 0.13/0.38  # Proof object conjectures             : 12
% 0.13/0.38  # Proof object clause conjectures      : 9
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 14
% 0.13/0.38  # Proof object initial formulas used   : 11
% 0.13/0.38  # Proof object generating inferences   : 10
% 0.13/0.38  # Proof object simplifying inferences  : 12
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 11
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 20
% 0.13/0.38  # Removed in clause preprocessing      : 1
% 0.13/0.38  # Initial clauses in saturation        : 19
% 0.13/0.38  # Processed clauses                    : 61
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 3
% 0.13/0.38  # ...remaining for further processing  : 58
% 0.13/0.38  # Other redundant clauses eliminated   : 5
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 3
% 0.13/0.38  # Backward-rewritten                   : 9
% 0.13/0.38  # Generated clauses                    : 52
% 0.13/0.38  # ...of the previous two non-trivial   : 37
% 0.13/0.38  # Contextual simplify-reflections      : 1
% 0.13/0.38  # Paramodulations                      : 39
% 0.13/0.38  # Factorizations                       : 8
% 0.13/0.38  # Equation resolutions                 : 5
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 25
% 0.13/0.38  #    Positive orientable unit clauses  : 8
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 2
% 0.13/0.38  #    Non-unit-clauses                  : 15
% 0.13/0.38  # Current number of unprocessed clauses: 13
% 0.13/0.38  # ...number of literals in the above   : 31
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 32
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 76
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 62
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 6
% 0.13/0.38  # Unit Clause-clause subsumption calls : 4
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 5
% 0.13/0.38  # BW rewrite match successes           : 5
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 1885
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.032 s
% 0.13/0.38  # System time              : 0.001 s
% 0.13/0.38  # Total time               : 0.033 s
% 0.13/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
