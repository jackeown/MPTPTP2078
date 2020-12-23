%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:50 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   58 (  87 expanded)
%              Number of clauses        :   32 (  38 expanded)
%              Number of leaves         :   13 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :  118 ( 190 expanded)
%              Number of equality atoms :   57 (  79 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t44_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
        & X2 != X3
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(d1_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( v1_zfmisc_1(X1)
      <=> ? [X2] :
            ( m1_subset_1(X2,X1)
            & X1 = k6_domain_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(t2_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_zfmisc_1(X1) )
     => ! [X2] :
          ( ~ v1_xboole_0(k3_xboole_0(X1,X2))
         => r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tex_2)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_13,plain,(
    ! [X11,X12] : k2_xboole_0(X11,k3_xboole_0(X11,X12)) = X11 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

fof(c_0_14,plain,(
    ! [X20,X21] : k1_setfam_1(k2_tarski(X20,X21)) = k3_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_15,plain,(
    ! [X18,X19] : k2_xboole_0(k1_tarski(X18),X19) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

fof(c_0_16,plain,(
    ! [X8] : k2_xboole_0(X8,k1_xboole_0) = X8 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_17,plain,(
    ! [X15,X16,X17] :
      ( k1_tarski(X15) != k2_xboole_0(X16,X17)
      | X16 = X17
      | X16 = k1_xboole_0
      | X17 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_zfmisc_1])])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X22,X23] :
      ( v1_xboole_0(X22)
      | ~ m1_subset_1(X23,X22)
      | k6_domain_1(X22,X23) = k1_tarski(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_23,plain,(
    ! [X24,X26] :
      ( ( m1_subset_1(esk1_1(X24),X24)
        | ~ v1_zfmisc_1(X24)
        | v1_xboole_0(X24) )
      & ( X24 = k6_domain_1(X24,esk1_1(X24))
        | ~ v1_zfmisc_1(X24)
        | v1_xboole_0(X24) )
      & ( ~ m1_subset_1(X26,X24)
        | X24 != k6_domain_1(X24,X26)
        | v1_zfmisc_1(X24)
        | v1_xboole_0(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tex_2])])])])])])).

fof(c_0_24,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k5_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_25,plain,
    ( X2 = X3
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | k1_tarski(X1) != k2_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,plain,
    ( k1_tarski(X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( m1_subset_1(esk1_1(X1),X1)
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_30,plain,(
    ! [X4,X5] :
      ( ( k4_xboole_0(X4,X5) != k1_xboole_0
        | r1_tarski(X4,X5) )
      & ( ~ r1_tarski(X4,X5)
        | k4_xboole_0(X4,X5) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_32,plain,(
    ! [X9,X10] : k3_xboole_0(X9,k2_xboole_0(X9,X10)) = X9 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

fof(c_0_33,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v1_xboole_0(X1)
          & v1_zfmisc_1(X1) )
       => ! [X2] :
            ( ~ v1_xboole_0(k3_xboole_0(X1,X2))
           => r1_tarski(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t2_tex_2])).

cnf(c_0_34,plain,
    ( k1_setfam_1(k2_tarski(k1_tarski(X1),X2)) = k1_tarski(X1)
    | k1_setfam_1(k2_tarski(k1_tarski(X1),X2)) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26])]),c_0_27])).

cnf(c_0_35,plain,
    ( k1_tarski(esk1_1(X1)) = k6_domain_1(X1,esk1_1(X1))
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_31,c_0_19])).

fof(c_0_38,plain,(
    ! [X13,X14] : r1_tarski(X13,k2_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_40,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    & v1_zfmisc_1(esk2_0)
    & ~ v1_xboole_0(k3_xboole_0(esk2_0,esk3_0))
    & ~ r1_tarski(esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_33])])])])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( k1_setfam_1(k2_tarski(k6_domain_1(X1,esk1_1(X1)),X2)) = k6_domain_1(X1,esk1_1(X1))
    | k1_setfam_1(k2_tarski(k6_domain_1(X1,esk1_1(X1)),X2)) = k1_xboole_0
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,plain,
    ( X1 = k6_domain_1(X1,esk1_1(X1))
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_44,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( k1_setfam_1(k2_tarski(X1,k2_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_39,c_0_19])).

cnf(c_0_47,negated_conjecture,
    ( ~ v1_xboole_0(k3_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_41,c_0_37])).

cnf(c_0_49,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_xboole_0
    | k1_setfam_1(k2_tarski(X1,X2)) = X1
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( ~ v1_xboole_0(k1_setfam_1(k2_tarski(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_47,c_0_19])).

cnf(c_0_52,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_xboole_0
    | r1_tarski(X1,X2)
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])])).

cnf(c_0_53,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_54,negated_conjecture,
    ( v1_zfmisc_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_55,negated_conjecture,
    ( ~ r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_56,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_54])]),c_0_55]),c_0_56]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:12:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_B00_00_F1_SE_CS_SP_PS_S083N
% 0.14/0.38  # and selection function SelectCQArNT.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.027 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 0.14/0.38  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.14/0.38  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.14/0.38  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.14/0.38  fof(t44_zfmisc_1, axiom, ![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&X2!=X3)&X2!=k1_xboole_0)&X3!=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 0.14/0.38  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.14/0.38  fof(d1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>(v1_zfmisc_1(X1)<=>?[X2]:(m1_subset_1(X2,X1)&X1=k6_domain_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 0.14/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.14/0.38  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.14/0.38  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 0.14/0.38  fof(t2_tex_2, conjecture, ![X1]:((~(v1_xboole_0(X1))&v1_zfmisc_1(X1))=>![X2]:(~(v1_xboole_0(k3_xboole_0(X1,X2)))=>r1_tarski(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tex_2)).
% 0.14/0.38  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.14/0.38  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.14/0.38  fof(c_0_13, plain, ![X11, X12]:k2_xboole_0(X11,k3_xboole_0(X11,X12))=X11, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 0.14/0.38  fof(c_0_14, plain, ![X20, X21]:k1_setfam_1(k2_tarski(X20,X21))=k3_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.14/0.38  fof(c_0_15, plain, ![X18, X19]:k2_xboole_0(k1_tarski(X18),X19)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.14/0.38  fof(c_0_16, plain, ![X8]:k2_xboole_0(X8,k1_xboole_0)=X8, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.14/0.38  fof(c_0_17, plain, ![X15, X16, X17]:(k1_tarski(X15)!=k2_xboole_0(X16,X17)|X16=X17|X16=k1_xboole_0|X17=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_zfmisc_1])])).
% 0.14/0.38  cnf(c_0_18, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_19, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  cnf(c_0_20, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_21, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.38  fof(c_0_22, plain, ![X22, X23]:(v1_xboole_0(X22)|~m1_subset_1(X23,X22)|k6_domain_1(X22,X23)=k1_tarski(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.14/0.38  fof(c_0_23, plain, ![X24, X26]:(((m1_subset_1(esk1_1(X24),X24)|~v1_zfmisc_1(X24)|v1_xboole_0(X24))&(X24=k6_domain_1(X24,esk1_1(X24))|~v1_zfmisc_1(X24)|v1_xboole_0(X24)))&(~m1_subset_1(X26,X24)|X24!=k6_domain_1(X24,X26)|v1_zfmisc_1(X24)|v1_xboole_0(X24))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tex_2])])])])])])).
% 0.14/0.38  fof(c_0_24, plain, ![X6, X7]:k4_xboole_0(X6,X7)=k5_xboole_0(X6,k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.14/0.38  cnf(c_0_25, plain, (X2=X3|X2=k1_xboole_0|X3=k1_xboole_0|k1_tarski(X1)!=k2_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.38  cnf(c_0_26, plain, (k2_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=X1), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.14/0.38  cnf(c_0_27, plain, (k1_tarski(X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.14/0.38  cnf(c_0_28, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.38  cnf(c_0_29, plain, (m1_subset_1(esk1_1(X1),X1)|v1_xboole_0(X1)|~v1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.38  fof(c_0_30, plain, ![X4, X5]:((k4_xboole_0(X4,X5)!=k1_xboole_0|r1_tarski(X4,X5))&(~r1_tarski(X4,X5)|k4_xboole_0(X4,X5)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.14/0.38  cnf(c_0_31, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.38  fof(c_0_32, plain, ![X9, X10]:k3_xboole_0(X9,k2_xboole_0(X9,X10))=X9, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 0.14/0.38  fof(c_0_33, negated_conjecture, ~(![X1]:((~(v1_xboole_0(X1))&v1_zfmisc_1(X1))=>![X2]:(~(v1_xboole_0(k3_xboole_0(X1,X2)))=>r1_tarski(X1,X2)))), inference(assume_negation,[status(cth)],[t2_tex_2])).
% 0.14/0.38  cnf(c_0_34, plain, (k1_setfam_1(k2_tarski(k1_tarski(X1),X2))=k1_tarski(X1)|k1_setfam_1(k2_tarski(k1_tarski(X1),X2))=k1_xboole_0), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26])]), c_0_27])).
% 0.14/0.38  cnf(c_0_35, plain, (k1_tarski(esk1_1(X1))=k6_domain_1(X1,esk1_1(X1))|v1_xboole_0(X1)|~v1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.14/0.38  cnf(c_0_36, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.38  cnf(c_0_37, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_31, c_0_19])).
% 0.14/0.38  fof(c_0_38, plain, ![X13, X14]:r1_tarski(X13,k2_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.14/0.38  cnf(c_0_39, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.14/0.38  fof(c_0_40, negated_conjecture, ((~v1_xboole_0(esk2_0)&v1_zfmisc_1(esk2_0))&(~v1_xboole_0(k3_xboole_0(esk2_0,esk3_0))&~r1_tarski(esk2_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_33])])])])).
% 0.14/0.38  cnf(c_0_41, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.38  cnf(c_0_42, plain, (k1_setfam_1(k2_tarski(k6_domain_1(X1,esk1_1(X1)),X2))=k6_domain_1(X1,esk1_1(X1))|k1_setfam_1(k2_tarski(k6_domain_1(X1,esk1_1(X1)),X2))=k1_xboole_0|v1_xboole_0(X1)|~v1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.14/0.38  cnf(c_0_43, plain, (X1=k6_domain_1(X1,esk1_1(X1))|v1_xboole_0(X1)|~v1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.38  cnf(c_0_44, plain, (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.14/0.38  cnf(c_0_45, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.14/0.38  cnf(c_0_46, plain, (k1_setfam_1(k2_tarski(X1,k2_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[c_0_39, c_0_19])).
% 0.14/0.38  cnf(c_0_47, negated_conjecture, (~v1_xboole_0(k3_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.14/0.38  cnf(c_0_48, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_41, c_0_37])).
% 0.14/0.38  cnf(c_0_49, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_xboole_0|k1_setfam_1(k2_tarski(X1,X2))=X1|v1_xboole_0(X1)|~v1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.14/0.38  cnf(c_0_50, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])).
% 0.14/0.38  cnf(c_0_51, negated_conjecture, (~v1_xboole_0(k1_setfam_1(k2_tarski(esk2_0,esk3_0)))), inference(rw,[status(thm)],[c_0_47, c_0_19])).
% 0.14/0.38  cnf(c_0_52, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_xboole_0|r1_tarski(X1,X2)|v1_xboole_0(X1)|~v1_zfmisc_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])])).
% 0.14/0.38  cnf(c_0_53, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.14/0.38  cnf(c_0_54, negated_conjecture, (v1_zfmisc_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.14/0.38  cnf(c_0_55, negated_conjecture, (~r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.14/0.38  cnf(c_0_56, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.14/0.38  cnf(c_0_57, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_54])]), c_0_55]), c_0_56]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 58
% 0.14/0.38  # Proof object clause steps            : 32
% 0.14/0.38  # Proof object formula steps           : 26
% 0.14/0.38  # Proof object conjectures             : 9
% 0.14/0.38  # Proof object clause conjectures      : 6
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 18
% 0.14/0.38  # Proof object initial formulas used   : 13
% 0.14/0.38  # Proof object generating inferences   : 8
% 0.14/0.38  # Proof object simplifying inferences  : 16
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 13
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 19
% 0.14/0.38  # Removed in clause preprocessing      : 2
% 0.14/0.38  # Initial clauses in saturation        : 17
% 0.14/0.38  # Processed clauses                    : 63
% 0.14/0.38  # ...of these trivial                  : 3
% 0.14/0.38  # ...subsumed                          : 6
% 0.14/0.38  # ...remaining for further processing  : 54
% 0.14/0.38  # Other redundant clauses eliminated   : 9
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 1
% 0.14/0.38  # Generated clauses                    : 72
% 0.14/0.38  # ...of the previous two non-trivial   : 36
% 0.14/0.38  # Contextual simplify-reflections      : 0
% 0.14/0.38  # Paramodulations                      : 59
% 0.14/0.38  # Factorizations                       : 4
% 0.14/0.38  # Equation resolutions                 : 9
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 36
% 0.14/0.38  #    Positive orientable unit clauses  : 10
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 5
% 0.14/0.38  #    Non-unit-clauses                  : 21
% 0.14/0.38  # Current number of unprocessed clauses: 7
% 0.14/0.38  # ...number of literals in the above   : 31
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 20
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 76
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 39
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 3
% 0.14/0.38  # Unit Clause-clause subsumption calls : 6
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 11
% 0.14/0.38  # BW rewrite match successes           : 1
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 1886
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.028 s
% 0.14/0.38  # System time              : 0.005 s
% 0.14/0.38  # Total time               : 0.034 s
% 0.14/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
