%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:49:38 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 162 expanded)
%              Number of clauses        :   30 (  73 expanded)
%              Number of leaves         :   12 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :  107 ( 312 expanded)
%              Number of equality atoms :   47 ( 153 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t95_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k7_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(t67_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_xboole_0(k2_relat_1(X1),k1_relat_1(X2))
           => k5_relat_1(X1,X2) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_relat_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(c_0_12,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X23)
      | k1_relat_1(k7_relat_1(X23,X22)) = k3_xboole_0(k1_relat_1(X23),X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

fof(c_0_13,plain,(
    ! [X16,X17] : k1_setfam_1(k2_tarski(X16,X17)) = k3_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k7_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t95_relat_1])).

fof(c_0_15,plain,(
    ! [X6,X7,X9,X10,X11] :
      ( ( r1_xboole_0(X6,X7)
        | r2_hidden(esk1_2(X6,X7),k3_xboole_0(X6,X7)) )
      & ( ~ r2_hidden(X11,k3_xboole_0(X9,X10))
        | ~ r1_xboole_0(X9,X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_16,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X18] : v1_relat_1(k6_relat_1(X18)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_19,plain,(
    ! [X21] :
      ( k1_relat_1(k6_relat_1(X21)) = X21
      & k2_relat_1(k6_relat_1(X21)) = X21 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_20,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & ( k7_relat_1(esk3_0,esk2_0) != k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(esk3_0),esk2_0) )
    & ( k7_relat_1(esk3_0,esk2_0) = k1_xboole_0
      | r1_xboole_0(k1_relat_1(esk3_0),esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

cnf(c_0_21,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X12,X13] :
      ( ( k2_zfmisc_1(X12,X13) != k1_xboole_0
        | X12 = k1_xboole_0
        | X13 = k1_xboole_0 )
      & ( X12 != k1_xboole_0
        | k2_zfmisc_1(X12,X13) = k1_xboole_0 )
      & ( X13 != k1_xboole_0
        | k2_zfmisc_1(X12,X13) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_27,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_21,c_0_17])).

cnf(c_0_28,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( k1_setfam_1(k2_tarski(k1_relat_1(esk3_0),X1)) = k1_relat_1(k7_relat_1(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_25])).

fof(c_0_30,plain,(
    ! [X14,X15] : ~ r2_hidden(X14,k2_zfmisc_1(X14,X15)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_31,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( r2_hidden(esk1_2(X1,X2),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)))
    | r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(esk3_0)),X1)) = k1_relat_1(k7_relat_1(esk3_0,X1)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_28])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_31])).

fof(c_0_36,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X19)
      | ~ v1_relat_1(X20)
      | ~ r1_xboole_0(k2_relat_1(X19),k1_relat_1(X20))
      | k5_relat_1(X19,X20) = k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_relat_1])])])).

fof(c_0_37,plain,(
    ! [X4,X5] :
      ( ~ r1_xboole_0(X4,X5)
      | r1_xboole_0(X5,X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk1_2(k1_relat_1(esk3_0),X1),k1_relat_1(k7_relat_1(esk3_0,X1)))
    | r1_xboole_0(k1_relat_1(esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( k7_relat_1(esk3_0,esk2_0) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_40,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_42,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | k7_relat_1(X25,X24) = k5_relat_1(k6_relat_1(X24),X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

cnf(c_0_43,plain,
    ( k5_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_xboole_0(k2_relat_1(X1),k1_relat_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_45,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_47,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( k7_relat_1(esk3_0,esk2_0) != k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_49,plain,
    ( k5_relat_1(k6_relat_1(X1),X2) = k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ r1_xboole_0(X1,k1_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_23])])).

cnf(c_0_50,negated_conjecture,
    ( r1_xboole_0(esk2_0,k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( k5_relat_1(k6_relat_1(X1),esk3_0) = k7_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_25])).

cnf(c_0_52,negated_conjecture,
    ( k7_relat_1(esk3_0,esk2_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_46])])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_25])]),c_0_52]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:27:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00AA
% 0.20/0.37  # and selection function SelectLargestOrientable.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.027 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 0.20/0.37  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.37  fof(t95_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k7_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 0.20/0.37  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.20/0.37  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.20/0.37  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.20/0.37  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.37  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.20/0.37  fof(t67_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_xboole_0(k2_relat_1(X1),k1_relat_1(X2))=>k5_relat_1(X1,X2)=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_relat_1)).
% 0.20/0.37  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.20/0.37  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.20/0.37  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 0.20/0.37  fof(c_0_12, plain, ![X22, X23]:(~v1_relat_1(X23)|k1_relat_1(k7_relat_1(X23,X22))=k3_xboole_0(k1_relat_1(X23),X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.20/0.37  fof(c_0_13, plain, ![X16, X17]:k1_setfam_1(k2_tarski(X16,X17))=k3_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.37  fof(c_0_14, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k7_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t95_relat_1])).
% 0.20/0.37  fof(c_0_15, plain, ![X6, X7, X9, X10, X11]:((r1_xboole_0(X6,X7)|r2_hidden(esk1_2(X6,X7),k3_xboole_0(X6,X7)))&(~r2_hidden(X11,k3_xboole_0(X9,X10))|~r1_xboole_0(X9,X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.20/0.37  cnf(c_0_16, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.37  cnf(c_0_17, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.37  fof(c_0_18, plain, ![X18]:v1_relat_1(k6_relat_1(X18)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.20/0.37  fof(c_0_19, plain, ![X21]:(k1_relat_1(k6_relat_1(X21))=X21&k2_relat_1(k6_relat_1(X21))=X21), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.20/0.37  fof(c_0_20, negated_conjecture, (v1_relat_1(esk3_0)&((k7_relat_1(esk3_0,esk2_0)!=k1_xboole_0|~r1_xboole_0(k1_relat_1(esk3_0),esk2_0))&(k7_relat_1(esk3_0,esk2_0)=k1_xboole_0|r1_xboole_0(k1_relat_1(esk3_0),esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.20/0.37  cnf(c_0_21, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.37  cnf(c_0_22, plain, (k1_relat_1(k7_relat_1(X1,X2))=k1_setfam_1(k2_tarski(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.37  cnf(c_0_23, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.37  cnf(c_0_24, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.37  cnf(c_0_25, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.37  fof(c_0_26, plain, ![X12, X13]:((k2_zfmisc_1(X12,X13)!=k1_xboole_0|(X12=k1_xboole_0|X13=k1_xboole_0))&((X12!=k1_xboole_0|k2_zfmisc_1(X12,X13)=k1_xboole_0)&(X13!=k1_xboole_0|k2_zfmisc_1(X12,X13)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.20/0.37  cnf(c_0_27, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_21, c_0_17])).
% 0.20/0.37  cnf(c_0_28, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])).
% 0.20/0.37  cnf(c_0_29, negated_conjecture, (k1_setfam_1(k2_tarski(k1_relat_1(esk3_0),X1))=k1_relat_1(k7_relat_1(esk3_0,X1))), inference(spm,[status(thm)],[c_0_22, c_0_25])).
% 0.20/0.37  fof(c_0_30, plain, ![X14, X15]:~r2_hidden(X14,k2_zfmisc_1(X14,X15)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.20/0.37  cnf(c_0_31, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.37  cnf(c_0_32, plain, (r2_hidden(esk1_2(X1,X2),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)))|r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.37  cnf(c_0_33, negated_conjecture, (k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(esk3_0)),X1))=k1_relat_1(k7_relat_1(esk3_0,X1))), inference(rw,[status(thm)],[c_0_29, c_0_28])).
% 0.20/0.37  cnf(c_0_34, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.37  cnf(c_0_35, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_31])).
% 0.20/0.37  fof(c_0_36, plain, ![X19, X20]:(~v1_relat_1(X19)|(~v1_relat_1(X20)|(~r1_xboole_0(k2_relat_1(X19),k1_relat_1(X20))|k5_relat_1(X19,X20)=k1_xboole_0))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_relat_1])])])).
% 0.20/0.37  fof(c_0_37, plain, ![X4, X5]:(~r1_xboole_0(X4,X5)|r1_xboole_0(X5,X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.20/0.37  cnf(c_0_38, negated_conjecture, (r2_hidden(esk1_2(k1_relat_1(esk3_0),X1),k1_relat_1(k7_relat_1(esk3_0,X1)))|r1_xboole_0(k1_relat_1(esk3_0),X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.37  cnf(c_0_39, negated_conjecture, (k7_relat_1(esk3_0,esk2_0)=k1_xboole_0|r1_xboole_0(k1_relat_1(esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.37  cnf(c_0_40, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.20/0.37  cnf(c_0_41, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.37  fof(c_0_42, plain, ![X24, X25]:(~v1_relat_1(X25)|k7_relat_1(X25,X24)=k5_relat_1(k6_relat_1(X24),X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.20/0.37  cnf(c_0_43, plain, (k5_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_xboole_0(k2_relat_1(X1),k1_relat_1(X2))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.37  cnf(c_0_44, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.37  cnf(c_0_45, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.37  cnf(c_0_46, negated_conjecture, (r1_xboole_0(k1_relat_1(esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_41])).
% 0.20/0.37  cnf(c_0_47, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.37  cnf(c_0_48, negated_conjecture, (k7_relat_1(esk3_0,esk2_0)!=k1_xboole_0|~r1_xboole_0(k1_relat_1(esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.37  cnf(c_0_49, plain, (k5_relat_1(k6_relat_1(X1),X2)=k1_xboole_0|~v1_relat_1(X2)|~r1_xboole_0(X1,k1_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_23])])).
% 0.20/0.37  cnf(c_0_50, negated_conjecture, (r1_xboole_0(esk2_0,k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.37  cnf(c_0_51, negated_conjecture, (k5_relat_1(k6_relat_1(X1),esk3_0)=k7_relat_1(esk3_0,X1)), inference(spm,[status(thm)],[c_0_47, c_0_25])).
% 0.20/0.37  cnf(c_0_52, negated_conjecture, (k7_relat_1(esk3_0,esk2_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_46])])).
% 0.20/0.37  cnf(c_0_53, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_25])]), c_0_52]), ['proof']).
% 0.20/0.37  # SZS output end CNFRefutation
% 0.20/0.37  # Proof object total steps             : 54
% 0.20/0.37  # Proof object clause steps            : 30
% 0.20/0.37  # Proof object formula steps           : 24
% 0.20/0.37  # Proof object conjectures             : 14
% 0.20/0.37  # Proof object clause conjectures      : 11
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 15
% 0.20/0.37  # Proof object initial formulas used   : 12
% 0.20/0.37  # Proof object generating inferences   : 9
% 0.20/0.37  # Proof object simplifying inferences  : 16
% 0.20/0.37  # Training examples: 0 positive, 0 negative
% 0.20/0.37  # Parsed axioms                        : 12
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 19
% 0.20/0.37  # Removed in clause preprocessing      : 1
% 0.20/0.37  # Initial clauses in saturation        : 18
% 0.20/0.37  # Processed clauses                    : 70
% 0.20/0.37  # ...of these trivial                  : 0
% 0.20/0.37  # ...subsumed                          : 7
% 0.20/0.37  # ...remaining for further processing  : 63
% 0.20/0.37  # Other redundant clauses eliminated   : 2
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 0
% 0.20/0.37  # Backward-rewritten                   : 7
% 0.20/0.37  # Generated clauses                    : 42
% 0.20/0.37  # ...of the previous two non-trivial   : 40
% 0.20/0.37  # Contextual simplify-reflections      : 0
% 0.20/0.37  # Paramodulations                      : 40
% 0.20/0.37  # Factorizations                       : 0
% 0.20/0.37  # Equation resolutions                 : 2
% 0.20/0.37  # Propositional unsat checks           : 0
% 0.20/0.37  #    Propositional check models        : 0
% 0.20/0.37  #    Propositional check unsatisfiable : 0
% 0.20/0.37  #    Propositional clauses             : 0
% 0.20/0.37  #    Propositional clauses after purity: 0
% 0.20/0.37  #    Propositional unsat core size     : 0
% 0.20/0.37  #    Propositional preprocessing time  : 0.000
% 0.20/0.37  #    Propositional encoding time       : 0.000
% 0.20/0.37  #    Propositional solver time         : 0.000
% 0.20/0.37  #    Success case prop preproc time    : 0.000
% 0.20/0.37  #    Success case prop encoding time   : 0.000
% 0.20/0.37  #    Success case prop solver time     : 0.000
% 0.20/0.37  # Current number of processed clauses  : 36
% 0.20/0.37  #    Positive orientable unit clauses  : 14
% 0.20/0.37  #    Positive unorientable unit clauses: 0
% 0.20/0.37  #    Negative unit clauses             : 3
% 0.20/0.37  #    Non-unit-clauses                  : 19
% 0.20/0.37  # Current number of unprocessed clauses: 4
% 0.20/0.37  # ...number of literals in the above   : 14
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 26
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 113
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 81
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 6
% 0.20/0.37  # Unit Clause-clause subsumption calls : 2
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 8
% 0.20/0.37  # BW rewrite match successes           : 6
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 1930
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.031 s
% 0.20/0.37  # System time              : 0.002 s
% 0.20/0.37  # Total time               : 0.033 s
% 0.20/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
