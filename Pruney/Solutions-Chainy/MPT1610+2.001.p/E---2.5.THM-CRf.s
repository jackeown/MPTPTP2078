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
% DateTime   : Thu Dec  3 11:15:49 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   55 (  63 expanded)
%              Number of clauses        :   28 (  32 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    9
%              Number of atoms          :  122 ( 155 expanded)
%              Number of equality atoms :   55 (  66 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t18_yellow_1,conjecture,(
    ! [X1] : k3_yellow_0(k3_yellow_1(X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow_1)).

fof(t4_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k2_yellow_1(k9_setfam_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).

fof(redefinition_k9_setfam_1,axiom,(
    ! [X1] : k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t83_zfmisc_1,axiom,(
    ! [X1,X2] : k1_zfmisc_1(k3_xboole_0(X1,X2)) = k3_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_zfmisc_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t13_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( r2_hidden(k1_xboole_0,X1)
       => k3_yellow_0(k2_yellow_1(X1)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(t46_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] : k3_yellow_0(k3_yellow_1(X1)) = k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t18_yellow_1])).

fof(c_0_14,plain,(
    ! [X35] : k3_yellow_1(X35) = k2_yellow_1(k9_setfam_1(X35)) ),
    inference(variable_rename,[status(thm)],[t4_yellow_1])).

fof(c_0_15,plain,(
    ! [X33] : k9_setfam_1(X33) = k1_zfmisc_1(X33) ),
    inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).

fof(c_0_16,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( r2_hidden(X10,X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | ~ r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k3_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k3_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X13)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k3_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_17,negated_conjecture,(
    k3_yellow_0(k3_yellow_1(esk3_0)) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_18,plain,
    ( k3_yellow_1(X1) = k2_yellow_1(k9_setfam_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X31,X32] : k1_zfmisc_1(k3_xboole_0(X31,X32)) = k3_xboole_0(k1_zfmisc_1(X31),k1_zfmisc_1(X32)) ),
    inference(variable_rename,[status(thm)],[t83_zfmisc_1])).

fof(c_0_22,plain,(
    ! [X19] : k3_xboole_0(X19,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_23,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_24,negated_conjecture,
    ( k3_yellow_0(k3_yellow_1(esk3_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k3_yellow_1(X1) = k2_yellow_1(k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_26,plain,(
    ! [X34] :
      ( v1_xboole_0(X34)
      | ~ r2_hidden(k1_xboole_0,X34)
      | k3_yellow_0(k2_yellow_1(X34)) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t13_yellow_1])])])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k1_zfmisc_1(k3_xboole_0(X1,X2)) = k3_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_31,plain,(
    ! [X20,X21,X22,X23,X24,X25] :
      ( ( ~ r2_hidden(X22,X21)
        | r1_tarski(X22,X20)
        | X21 != k1_zfmisc_1(X20) )
      & ( ~ r1_tarski(X23,X20)
        | r2_hidden(X23,X21)
        | X21 != k1_zfmisc_1(X20) )
      & ( ~ r2_hidden(esk2_2(X24,X25),X25)
        | ~ r1_tarski(esk2_2(X24,X25),X24)
        | X25 = k1_zfmisc_1(X24) )
      & ( r2_hidden(esk2_2(X24,X25),X25)
        | r1_tarski(esk2_2(X24,X25),X24)
        | X25 = k1_zfmisc_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_32,plain,(
    ! [X16] :
      ( ~ v1_xboole_0(X16)
      | X16 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_33,negated_conjecture,
    ( k3_yellow_0(k2_yellow_1(k1_zfmisc_1(esk3_0))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_34,plain,
    ( v1_xboole_0(X1)
    | k3_yellow_0(k2_yellow_1(X1)) = k1_xboole_0
    | ~ r2_hidden(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,k1_zfmisc_1(k3_xboole_0(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_38,plain,(
    ! [X17,X18] :
      ( ( r1_tarski(X17,X18)
        | X17 != X18 )
      & ( r1_tarski(X18,X17)
        | X17 != X18 )
      & ( ~ r1_tarski(X17,X18)
        | ~ r1_tarski(X18,X17)
        | X17 = X18 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_39,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(esk3_0))
    | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_44,plain,(
    ! [X29,X30] : k2_xboole_0(k1_tarski(X29),X30) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

fof(c_0_45,plain,(
    ! [X27,X28] :
      ( ~ r2_hidden(X27,X28)
      | k2_xboole_0(k1_tarski(X27),X28) = X28 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_zfmisc_1])])).

cnf(c_0_46,negated_conjecture,
    ( k1_zfmisc_1(esk3_0) = k1_xboole_0
    | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_49,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( k1_zfmisc_1(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])])).

cnf(c_0_52,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50])])).

cnf(c_0_53,negated_conjecture,
    ( ~ r1_tarski(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_51]),c_0_52])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_53,c_0_48]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.10  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.10/0.29  % Computer   : n021.cluster.edu
% 0.10/0.29  % Model      : x86_64 x86_64
% 0.10/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.29  % Memory     : 8042.1875MB
% 0.10/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.29  % CPULimit   : 60
% 0.10/0.29  % WCLimit    : 600
% 0.10/0.29  % DateTime   : Tue Dec  1 17:20:19 EST 2020
% 0.10/0.29  % CPUTime    : 
% 0.10/0.29  # Version: 2.5pre002
% 0.10/0.29  # No SInE strategy applied
% 0.10/0.29  # Trying AutoSched0 for 299 seconds
% 0.14/0.32  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05BN
% 0.14/0.32  # and selection function SelectUnlessUniqMaxSmallestOrientable.
% 0.14/0.32  #
% 0.14/0.32  # Preprocessing time       : 0.028 s
% 0.14/0.32  # Presaturation interreduction done
% 0.14/0.32  
% 0.14/0.32  # Proof found!
% 0.14/0.32  # SZS status Theorem
% 0.14/0.32  # SZS output start CNFRefutation
% 0.14/0.32  fof(t18_yellow_1, conjecture, ![X1]:k3_yellow_0(k3_yellow_1(X1))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_yellow_1)).
% 0.14/0.32  fof(t4_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k2_yellow_1(k9_setfam_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_yellow_1)).
% 0.14/0.32  fof(redefinition_k9_setfam_1, axiom, ![X1]:k9_setfam_1(X1)=k1_zfmisc_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 0.14/0.32  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.14/0.32  fof(t83_zfmisc_1, axiom, ![X1, X2]:k1_zfmisc_1(k3_xboole_0(X1,X2))=k3_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_zfmisc_1)).
% 0.14/0.32  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.14/0.32  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.14/0.32  fof(t13_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k1_xboole_0,X1)=>k3_yellow_0(k2_yellow_1(X1))=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_yellow_1)).
% 0.14/0.32  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.14/0.32  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.14/0.32  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.14/0.32  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.14/0.32  fof(t46_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 0.14/0.32  fof(c_0_13, negated_conjecture, ~(![X1]:k3_yellow_0(k3_yellow_1(X1))=k1_xboole_0), inference(assume_negation,[status(cth)],[t18_yellow_1])).
% 0.14/0.32  fof(c_0_14, plain, ![X35]:k3_yellow_1(X35)=k2_yellow_1(k9_setfam_1(X35)), inference(variable_rename,[status(thm)],[t4_yellow_1])).
% 0.14/0.32  fof(c_0_15, plain, ![X33]:k9_setfam_1(X33)=k1_zfmisc_1(X33), inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).
% 0.14/0.32  fof(c_0_16, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k3_xboole_0(X7,X8))&(r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k3_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|~r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k3_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|~r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k3_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k3_xboole_0(X12,X13))&(r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k3_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.14/0.32  fof(c_0_17, negated_conjecture, k3_yellow_0(k3_yellow_1(esk3_0))!=k1_xboole_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.14/0.32  cnf(c_0_18, plain, (k3_yellow_1(X1)=k2_yellow_1(k9_setfam_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.32  cnf(c_0_19, plain, (k9_setfam_1(X1)=k1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.32  cnf(c_0_20, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.32  fof(c_0_21, plain, ![X31, X32]:k1_zfmisc_1(k3_xboole_0(X31,X32))=k3_xboole_0(k1_zfmisc_1(X31),k1_zfmisc_1(X32)), inference(variable_rename,[status(thm)],[t83_zfmisc_1])).
% 0.14/0.32  fof(c_0_22, plain, ![X19]:k3_xboole_0(X19,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.14/0.32  fof(c_0_23, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.14/0.32  cnf(c_0_24, negated_conjecture, (k3_yellow_0(k3_yellow_1(esk3_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.32  cnf(c_0_25, plain, (k3_yellow_1(X1)=k2_yellow_1(k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.14/0.32  fof(c_0_26, plain, ![X34]:(v1_xboole_0(X34)|(~r2_hidden(k1_xboole_0,X34)|k3_yellow_0(k2_yellow_1(X34))=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t13_yellow_1])])])).
% 0.14/0.32  cnf(c_0_27, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_20])).
% 0.14/0.32  cnf(c_0_28, plain, (k1_zfmisc_1(k3_xboole_0(X1,X2))=k3_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.32  cnf(c_0_29, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.32  cnf(c_0_30, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.32  fof(c_0_31, plain, ![X20, X21, X22, X23, X24, X25]:(((~r2_hidden(X22,X21)|r1_tarski(X22,X20)|X21!=k1_zfmisc_1(X20))&(~r1_tarski(X23,X20)|r2_hidden(X23,X21)|X21!=k1_zfmisc_1(X20)))&((~r2_hidden(esk2_2(X24,X25),X25)|~r1_tarski(esk2_2(X24,X25),X24)|X25=k1_zfmisc_1(X24))&(r2_hidden(esk2_2(X24,X25),X25)|r1_tarski(esk2_2(X24,X25),X24)|X25=k1_zfmisc_1(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.14/0.32  fof(c_0_32, plain, ![X16]:(~v1_xboole_0(X16)|X16=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.14/0.32  cnf(c_0_33, negated_conjecture, (k3_yellow_0(k2_yellow_1(k1_zfmisc_1(esk3_0)))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.14/0.32  cnf(c_0_34, plain, (v1_xboole_0(X1)|k3_yellow_0(k2_yellow_1(X1))=k1_xboole_0|~r2_hidden(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.14/0.32  cnf(c_0_35, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r2_hidden(X1,k1_zfmisc_1(k3_xboole_0(X3,X2)))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.14/0.32  cnf(c_0_36, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.14/0.32  cnf(c_0_37, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.32  fof(c_0_38, plain, ![X17, X18]:(((r1_tarski(X17,X18)|X17!=X18)&(r1_tarski(X18,X17)|X17!=X18))&(~r1_tarski(X17,X18)|~r1_tarski(X18,X17)|X17=X18)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.14/0.32  cnf(c_0_39, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.14/0.32  cnf(c_0_40, negated_conjecture, (v1_xboole_0(k1_zfmisc_1(esk3_0))|~r2_hidden(k1_xboole_0,k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.14/0.32  cnf(c_0_41, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r2_hidden(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.14/0.32  cnf(c_0_42, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_37])).
% 0.14/0.32  cnf(c_0_43, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.14/0.32  fof(c_0_44, plain, ![X29, X30]:k2_xboole_0(k1_tarski(X29),X30)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.14/0.32  fof(c_0_45, plain, ![X27, X28]:(~r2_hidden(X27,X28)|k2_xboole_0(k1_tarski(X27),X28)=X28), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_zfmisc_1])])).
% 0.14/0.32  cnf(c_0_46, negated_conjecture, (k1_zfmisc_1(esk3_0)=k1_xboole_0|~r2_hidden(k1_xboole_0,k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.14/0.32  cnf(c_0_47, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.14/0.32  cnf(c_0_48, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_43])).
% 0.14/0.32  cnf(c_0_49, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.14/0.32  cnf(c_0_50, plain, (k2_xboole_0(k1_tarski(X1),X2)=X2|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.14/0.32  cnf(c_0_51, negated_conjecture, (k1_zfmisc_1(esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])])).
% 0.14/0.32  cnf(c_0_52, plain, (~r2_hidden(X1,k1_xboole_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50])])).
% 0.14/0.32  cnf(c_0_53, negated_conjecture, (~r1_tarski(X1,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_51]), c_0_52])).
% 0.14/0.32  cnf(c_0_54, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_53, c_0_48]), ['proof']).
% 0.14/0.32  # SZS output end CNFRefutation
% 0.14/0.32  # Proof object total steps             : 55
% 0.14/0.32  # Proof object clause steps            : 28
% 0.14/0.32  # Proof object formula steps           : 27
% 0.14/0.32  # Proof object conjectures             : 10
% 0.14/0.32  # Proof object clause conjectures      : 7
% 0.14/0.32  # Proof object formula conjectures     : 3
% 0.14/0.32  # Proof object initial clauses used    : 13
% 0.14/0.32  # Proof object initial formulas used   : 13
% 0.14/0.32  # Proof object generating inferences   : 10
% 0.14/0.32  # Proof object simplifying inferences  : 9
% 0.14/0.32  # Training examples: 0 positive, 0 negative
% 0.14/0.32  # Parsed axioms                        : 13
% 0.14/0.32  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.32  # Initial clauses                      : 23
% 0.14/0.32  # Removed in clause preprocessing      : 2
% 0.14/0.32  # Initial clauses in saturation        : 21
% 0.14/0.32  # Processed clauses                    : 74
% 0.14/0.32  # ...of these trivial                  : 1
% 0.14/0.32  # ...subsumed                          : 8
% 0.14/0.32  # ...remaining for further processing  : 65
% 0.14/0.32  # Other redundant clauses eliminated   : 8
% 0.14/0.32  # Clauses deleted for lack of memory   : 0
% 0.14/0.32  # Backward-subsumed                    : 0
% 0.14/0.32  # Backward-rewritten                   : 6
% 0.14/0.32  # Generated clauses                    : 132
% 0.14/0.32  # ...of the previous two non-trivial   : 112
% 0.14/0.32  # Contextual simplify-reflections      : 0
% 0.14/0.32  # Paramodulations                      : 120
% 0.14/0.32  # Factorizations                       : 4
% 0.14/0.32  # Equation resolutions                 : 8
% 0.14/0.32  # Propositional unsat checks           : 0
% 0.14/0.32  #    Propositional check models        : 0
% 0.14/0.32  #    Propositional check unsatisfiable : 0
% 0.14/0.32  #    Propositional clauses             : 0
% 0.14/0.32  #    Propositional clauses after purity: 0
% 0.14/0.32  #    Propositional unsat core size     : 0
% 0.14/0.32  #    Propositional preprocessing time  : 0.000
% 0.14/0.32  #    Propositional encoding time       : 0.000
% 0.14/0.32  #    Propositional solver time         : 0.000
% 0.14/0.32  #    Success case prop preproc time    : 0.000
% 0.14/0.32  #    Success case prop encoding time   : 0.000
% 0.14/0.32  #    Success case prop solver time     : 0.000
% 0.14/0.32  # Current number of processed clauses  : 32
% 0.14/0.32  #    Positive orientable unit clauses  : 7
% 0.14/0.32  #    Positive unorientable unit clauses: 1
% 0.14/0.32  #    Negative unit clauses             : 4
% 0.14/0.32  #    Non-unit-clauses                  : 20
% 0.14/0.32  # Current number of unprocessed clauses: 78
% 0.14/0.32  # ...number of literals in the above   : 187
% 0.14/0.32  # Current number of archived formulas  : 0
% 0.14/0.32  # Current number of archived clauses   : 28
% 0.14/0.32  # Clause-clause subsumption calls (NU) : 110
% 0.14/0.32  # Rec. Clause-clause subsumption calls : 101
% 0.14/0.32  # Non-unit clause-clause subsumptions  : 5
% 0.14/0.32  # Unit Clause-clause subsumption calls : 12
% 0.14/0.32  # Rewrite failures with RHS unbound    : 0
% 0.14/0.32  # BW rewrite match attempts            : 6
% 0.14/0.32  # BW rewrite match successes           : 6
% 0.14/0.32  # Condensation attempts                : 0
% 0.14/0.32  # Condensation successes               : 0
% 0.14/0.32  # Termbank termtop insertions          : 2661
% 0.14/0.32  
% 0.14/0.32  # -------------------------------------------------
% 0.14/0.32  # User time                : 0.030 s
% 0.14/0.32  # System time              : 0.004 s
% 0.14/0.32  # Total time               : 0.034 s
% 0.14/0.32  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
