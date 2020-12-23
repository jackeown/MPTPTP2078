%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:44 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   55 (  71 expanded)
%              Number of clauses        :   28 (  31 expanded)
%              Number of leaves         :   13 (  18 expanded)
%              Depth                    :    9
%              Number of atoms          :  103 ( 137 expanded)
%              Number of equality atoms :   29 (  44 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t216_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => k7_relat_1(k6_subset_1(X3,k7_relat_1(X3,X2)),X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t216_relat_1)).

fof(t38_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k4_xboole_0(X2,X1))
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t212_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1))) = k6_subset_1(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t187_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_xboole_0(X2,k1_relat_1(X1))
         => k7_relat_1(X1,X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

fof(fc2_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).

fof(t81_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
     => r1_xboole_0(X2,k4_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r1_tarski(X1,X2)
         => k7_relat_1(k6_subset_1(X3,k7_relat_1(X3,X2)),X1) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t216_relat_1])).

fof(c_0_14,plain,(
    ! [X11,X12] :
      ( ~ r1_tarski(X11,k4_xboole_0(X12,X11))
      | X11 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).

fof(c_0_15,plain,(
    ! [X19,X20] :
      ( ( ~ r1_xboole_0(X19,X20)
        | k4_xboole_0(X19,X20) = X19 )
      & ( k4_xboole_0(X19,X20) != X19
        | r1_xboole_0(X19,X20) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_16,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X7,X8)
      | r1_tarski(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_17,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & r1_tarski(esk1_0,esk2_0)
    & k7_relat_1(k6_subset_1(esk3_0,k7_relat_1(esk3_0,esk2_0)),esk1_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_18,plain,(
    ! [X27,X28] :
      ( ~ v1_relat_1(X28)
      | k1_relat_1(k6_subset_1(X28,k7_relat_1(X28,X27))) = k6_subset_1(k1_relat_1(X28),X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t212_relat_1])])).

fof(c_0_19,plain,(
    ! [X21,X22] : k6_subset_1(X21,X22) = k4_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_20,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X2))) = k6_subset_1(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_28,plain,(
    ! [X9,X10] : r1_tarski(k4_xboole_0(X9,X10),X9) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_29,plain,(
    ! [X4,X5] :
      ( ~ r1_xboole_0(X4,X5)
      | r1_xboole_0(X5,X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_30,plain,(
    ! [X14,X15] : r1_xboole_0(k4_xboole_0(X14,X15),X15) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_31,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X25)
      | ~ r1_xboole_0(X26,k1_relat_1(X25))
      | k7_relat_1(X25,X26) = k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t187_relat_1])])])).

cnf(c_0_32,plain,
    ( k1_relat_1(k4_xboole_0(X1,k7_relat_1(X1,X2))) = k4_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_34,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,esk1_0)
    | ~ r1_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_35,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( k7_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( k1_relat_1(k4_xboole_0(esk3_0,k7_relat_1(esk3_0,X1))) = k4_xboole_0(k1_relat_1(esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_40,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X23)
      | v1_relat_1(k4_xboole_0(X23,X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_relat_1])])).

fof(c_0_41,plain,(
    ! [X16,X17,X18] :
      ( ~ r1_xboole_0(X16,k4_xboole_0(X17,X18))
      | r1_xboole_0(X17,k4_xboole_0(X16,X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t81_xboole_1])])).

cnf(c_0_42,negated_conjecture,
    ( k4_xboole_0(esk1_0,X1) = k1_xboole_0
    | ~ r1_xboole_0(esk2_0,k4_xboole_0(esk1_0,X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_44,plain,(
    ! [X13] : r1_xboole_0(X13,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_45,negated_conjecture,
    ( k7_relat_1(k6_subset_1(esk3_0,k7_relat_1(esk3_0,esk2_0)),esk1_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_46,negated_conjecture,
    ( k7_relat_1(k4_xboole_0(esk3_0,k7_relat_1(esk3_0,X1)),X2) = k1_xboole_0
    | ~ v1_relat_1(k4_xboole_0(esk3_0,k7_relat_1(esk3_0,X1)))
    | ~ r1_xboole_0(X2,k4_xboole_0(k1_relat_1(esk3_0),X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,plain,
    ( v1_relat_1(k4_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( r1_xboole_0(X2,k4_xboole_0(X1,X3))
    | ~ r1_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( k7_relat_1(k4_xboole_0(esk3_0,k7_relat_1(esk3_0,esk2_0)),esk1_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_45,c_0_25])).

cnf(c_0_52,negated_conjecture,
    ( k7_relat_1(k4_xboole_0(esk3_0,k7_relat_1(esk3_0,X1)),X2) = k1_xboole_0
    | ~ r1_xboole_0(X2,k4_xboole_0(k1_relat_1(esk3_0),X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_33])])).

cnf(c_0_53,negated_conjecture,
    ( r1_xboole_0(esk1_0,k4_xboole_0(X1,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:52:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.42  # AutoSched0-Mode selected heuristic G_E___208_C12_11_nc_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.42  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.42  #
% 0.20/0.42  # Preprocessing time       : 0.027 s
% 0.20/0.42  # Presaturation interreduction done
% 0.20/0.42  
% 0.20/0.42  # Proof found!
% 0.20/0.42  # SZS status Theorem
% 0.20/0.42  # SZS output start CNFRefutation
% 0.20/0.42  fof(t216_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k7_relat_1(k6_subset_1(X3,k7_relat_1(X3,X2)),X1)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t216_relat_1)).
% 0.20/0.42  fof(t38_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,k4_xboole_0(X2,X1))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 0.20/0.42  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.20/0.42  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.20/0.42  fof(t212_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)))=k6_subset_1(k1_relat_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t212_relat_1)).
% 0.20/0.42  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.20/0.42  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.20/0.42  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.20/0.42  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.20/0.42  fof(t187_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_xboole_0(X2,k1_relat_1(X1))=>k7_relat_1(X1,X2)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 0.20/0.42  fof(fc2_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k4_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_relat_1)).
% 0.20/0.42  fof(t81_xboole_1, axiom, ![X1, X2, X3]:(r1_xboole_0(X1,k4_xboole_0(X2,X3))=>r1_xboole_0(X2,k4_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_xboole_1)).
% 0.20/0.42  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.20/0.42  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k7_relat_1(k6_subset_1(X3,k7_relat_1(X3,X2)),X1)=k1_xboole_0))), inference(assume_negation,[status(cth)],[t216_relat_1])).
% 0.20/0.42  fof(c_0_14, plain, ![X11, X12]:(~r1_tarski(X11,k4_xboole_0(X12,X11))|X11=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_xboole_1])])).
% 0.20/0.42  fof(c_0_15, plain, ![X19, X20]:((~r1_xboole_0(X19,X20)|k4_xboole_0(X19,X20)=X19)&(k4_xboole_0(X19,X20)!=X19|r1_xboole_0(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.20/0.42  fof(c_0_16, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X7,X8)|r1_tarski(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.20/0.42  fof(c_0_17, negated_conjecture, (v1_relat_1(esk3_0)&(r1_tarski(esk1_0,esk2_0)&k7_relat_1(k6_subset_1(esk3_0,k7_relat_1(esk3_0,esk2_0)),esk1_0)!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.20/0.42  fof(c_0_18, plain, ![X27, X28]:(~v1_relat_1(X28)|k1_relat_1(k6_subset_1(X28,k7_relat_1(X28,X27)))=k6_subset_1(k1_relat_1(X28),X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t212_relat_1])])).
% 0.20/0.42  fof(c_0_19, plain, ![X21, X22]:k6_subset_1(X21,X22)=k4_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.20/0.42  cnf(c_0_20, plain, (X1=k1_xboole_0|~r1_tarski(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.42  cnf(c_0_21, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.42  cnf(c_0_22, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.42  cnf(c_0_23, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.42  cnf(c_0_24, plain, (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X2)))=k6_subset_1(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.42  cnf(c_0_25, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.42  cnf(c_0_26, plain, (X1=k1_xboole_0|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.42  cnf(c_0_27, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,esk1_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.42  fof(c_0_28, plain, ![X9, X10]:r1_tarski(k4_xboole_0(X9,X10),X9), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.20/0.42  fof(c_0_29, plain, ![X4, X5]:(~r1_xboole_0(X4,X5)|r1_xboole_0(X5,X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.20/0.42  fof(c_0_30, plain, ![X14, X15]:r1_xboole_0(k4_xboole_0(X14,X15),X15), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.20/0.42  fof(c_0_31, plain, ![X25, X26]:(~v1_relat_1(X25)|(~r1_xboole_0(X26,k1_relat_1(X25))|k7_relat_1(X25,X26)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t187_relat_1])])])).
% 0.20/0.42  cnf(c_0_32, plain, (k1_relat_1(k4_xboole_0(X1,k7_relat_1(X1,X2)))=k4_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_25])).
% 0.20/0.42  cnf(c_0_33, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.42  cnf(c_0_34, negated_conjecture, (X1=k1_xboole_0|~r1_tarski(X1,esk1_0)|~r1_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.42  cnf(c_0_35, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.42  cnf(c_0_36, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.42  cnf(c_0_37, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.42  cnf(c_0_38, plain, (k7_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.42  cnf(c_0_39, negated_conjecture, (k1_relat_1(k4_xboole_0(esk3_0,k7_relat_1(esk3_0,X1)))=k4_xboole_0(k1_relat_1(esk3_0),X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.42  fof(c_0_40, plain, ![X23, X24]:(~v1_relat_1(X23)|v1_relat_1(k4_xboole_0(X23,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_relat_1])])).
% 0.20/0.42  fof(c_0_41, plain, ![X16, X17, X18]:(~r1_xboole_0(X16,k4_xboole_0(X17,X18))|r1_xboole_0(X17,k4_xboole_0(X16,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t81_xboole_1])])).
% 0.20/0.42  cnf(c_0_42, negated_conjecture, (k4_xboole_0(esk1_0,X1)=k1_xboole_0|~r1_xboole_0(esk2_0,k4_xboole_0(esk1_0,X1))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.42  cnf(c_0_43, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.42  fof(c_0_44, plain, ![X13]:r1_xboole_0(X13,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.20/0.42  cnf(c_0_45, negated_conjecture, (k7_relat_1(k6_subset_1(esk3_0,k7_relat_1(esk3_0,esk2_0)),esk1_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.42  cnf(c_0_46, negated_conjecture, (k7_relat_1(k4_xboole_0(esk3_0,k7_relat_1(esk3_0,X1)),X2)=k1_xboole_0|~v1_relat_1(k4_xboole_0(esk3_0,k7_relat_1(esk3_0,X1)))|~r1_xboole_0(X2,k4_xboole_0(k1_relat_1(esk3_0),X1))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.42  cnf(c_0_47, plain, (v1_relat_1(k4_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.42  cnf(c_0_48, plain, (r1_xboole_0(X2,k4_xboole_0(X1,X3))|~r1_xboole_0(X1,k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.42  cnf(c_0_49, negated_conjecture, (k4_xboole_0(esk1_0,esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.42  cnf(c_0_50, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.42  cnf(c_0_51, negated_conjecture, (k7_relat_1(k4_xboole_0(esk3_0,k7_relat_1(esk3_0,esk2_0)),esk1_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_45, c_0_25])).
% 0.20/0.42  cnf(c_0_52, negated_conjecture, (k7_relat_1(k4_xboole_0(esk3_0,k7_relat_1(esk3_0,X1)),X2)=k1_xboole_0|~r1_xboole_0(X2,k4_xboole_0(k1_relat_1(esk3_0),X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_33])])).
% 0.20/0.42  cnf(c_0_53, negated_conjecture, (r1_xboole_0(esk1_0,k4_xboole_0(X1,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])])).
% 0.20/0.42  cnf(c_0_54, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])]), ['proof']).
% 0.20/0.42  # SZS output end CNFRefutation
% 0.20/0.42  # Proof object total steps             : 55
% 0.20/0.42  # Proof object clause steps            : 28
% 0.20/0.42  # Proof object formula steps           : 27
% 0.20/0.42  # Proof object conjectures             : 16
% 0.20/0.42  # Proof object clause conjectures      : 13
% 0.20/0.42  # Proof object formula conjectures     : 3
% 0.20/0.42  # Proof object initial clauses used    : 15
% 0.20/0.42  # Proof object initial formulas used   : 13
% 0.20/0.42  # Proof object generating inferences   : 11
% 0.20/0.42  # Proof object simplifying inferences  : 9
% 0.20/0.42  # Training examples: 0 positive, 0 negative
% 0.20/0.42  # Parsed axioms                        : 13
% 0.20/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.42  # Initial clauses                      : 16
% 0.20/0.42  # Removed in clause preprocessing      : 1
% 0.20/0.42  # Initial clauses in saturation        : 15
% 0.20/0.42  # Processed clauses                    : 919
% 0.20/0.42  # ...of these trivial                  : 24
% 0.20/0.42  # ...subsumed                          : 601
% 0.20/0.42  # ...remaining for further processing  : 294
% 0.20/0.42  # Other redundant clauses eliminated   : 2
% 0.20/0.42  # Clauses deleted for lack of memory   : 0
% 0.20/0.42  # Backward-subsumed                    : 25
% 0.20/0.42  # Backward-rewritten                   : 18
% 0.20/0.42  # Generated clauses                    : 4252
% 0.20/0.42  # ...of the previous two non-trivial   : 1992
% 0.20/0.42  # Contextual simplify-reflections      : 2
% 0.20/0.42  # Paramodulations                      : 4250
% 0.20/0.42  # Factorizations                       : 0
% 0.20/0.42  # Equation resolutions                 : 2
% 0.20/0.42  # Propositional unsat checks           : 0
% 0.20/0.42  #    Propositional check models        : 0
% 0.20/0.42  #    Propositional check unsatisfiable : 0
% 0.20/0.42  #    Propositional clauses             : 0
% 0.20/0.42  #    Propositional clauses after purity: 0
% 0.20/0.42  #    Propositional unsat core size     : 0
% 0.20/0.42  #    Propositional preprocessing time  : 0.000
% 0.20/0.42  #    Propositional encoding time       : 0.000
% 0.20/0.42  #    Propositional solver time         : 0.000
% 0.20/0.42  #    Success case prop preproc time    : 0.000
% 0.20/0.42  #    Success case prop encoding time   : 0.000
% 0.20/0.42  #    Success case prop solver time     : 0.000
% 0.20/0.42  # Current number of processed clauses  : 236
% 0.20/0.42  #    Positive orientable unit clauses  : 79
% 0.20/0.42  #    Positive unorientable unit clauses: 0
% 0.20/0.42  #    Negative unit clauses             : 32
% 0.20/0.42  #    Non-unit-clauses                  : 125
% 0.20/0.42  # Current number of unprocessed clauses: 1032
% 0.20/0.42  # ...number of literals in the above   : 2132
% 0.20/0.42  # Current number of archived formulas  : 0
% 0.20/0.42  # Current number of archived clauses   : 59
% 0.20/0.42  # Clause-clause subsumption calls (NU) : 2690
% 0.20/0.42  # Rec. Clause-clause subsumption calls : 2620
% 0.20/0.42  # Non-unit clause-clause subsumptions  : 368
% 0.20/0.42  # Unit Clause-clause subsumption calls : 818
% 0.20/0.42  # Rewrite failures with RHS unbound    : 0
% 0.20/0.42  # BW rewrite match attempts            : 134
% 0.20/0.42  # BW rewrite match successes           : 18
% 0.20/0.42  # Condensation attempts                : 0
% 0.20/0.42  # Condensation successes               : 0
% 0.20/0.42  # Termbank termtop insertions          : 42836
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.078 s
% 0.20/0.42  # System time              : 0.004 s
% 0.20/0.42  # Total time               : 0.082 s
% 0.20/0.42  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
