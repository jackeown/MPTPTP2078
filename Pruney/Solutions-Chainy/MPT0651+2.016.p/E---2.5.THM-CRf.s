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
% DateTime   : Thu Dec  3 10:53:50 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   53 (  97 expanded)
%              Number of clauses        :   26 (  35 expanded)
%              Number of leaves         :   13 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :  153 ( 323 expanded)
%              Number of equality atoms :   45 ( 108 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t45_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(t80_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc4_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v2_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(t37_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
        & k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(dt_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(t58_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k1_relat_1(k5_relat_1(X1,k2_funct_1(X1))) = k1_relat_1(X1)
          & k2_relat_1(k5_relat_1(X1,k2_funct_1(X1))) = k1_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(t46_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
           => k1_relat_1(k5_relat_1(X1,X2)) = k1_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t160_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k2_relat_1(k5_relat_1(X1,X2)) = k9_relat_1(X2,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(d9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(X1) = k4_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(c_0_13,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(X8)
      | ~ v1_relat_1(X9)
      | r1_tarski(k2_relat_1(k5_relat_1(X8,X9)),k2_relat_1(X9)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_relat_1])])])).

fof(c_0_14,plain,(
    ! [X13] :
      ( ~ v1_relat_1(X13)
      | k5_relat_1(X13,k6_relat_1(k2_relat_1(X13))) = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).

fof(c_0_15,plain,(
    ! [X12] :
      ( k1_relat_1(k6_relat_1(X12)) = X12
      & k2_relat_1(k6_relat_1(X12)) = X12 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_16,plain,(
    ! [X16] :
      ( v1_relat_1(k6_relat_1(X16))
      & v2_funct_1(k6_relat_1(X16)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

fof(c_0_17,plain,(
    ! [X4] :
      ( ~ v1_relat_1(X4)
      | k9_relat_1(X4,k1_relat_1(X4)) = k2_relat_1(X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

fof(c_0_18,plain,(
    ! [X7] :
      ( ( k2_relat_1(X7) = k1_relat_1(k4_relat_1(X7))
        | ~ v1_relat_1(X7) )
      & ( k1_relat_1(X7) = k2_relat_1(k4_relat_1(X7))
        | ~ v1_relat_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).

fof(c_0_19,plain,(
    ! [X3] :
      ( ~ v1_relat_1(X3)
      | v1_relat_1(k4_relat_1(X3)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
         => ( k1_relat_1(k5_relat_1(X1,k2_funct_1(X1))) = k1_relat_1(X1)
            & k2_relat_1(k5_relat_1(X1,k2_funct_1(X1))) = k1_relat_1(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t58_funct_1])).

fof(c_0_21,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | ~ v1_relat_1(X11)
      | ~ r1_tarski(k2_relat_1(X10),k1_relat_1(X11))
      | k1_relat_1(k5_relat_1(X10,X11)) = k1_relat_1(X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_relat_1])])])).

fof(c_0_22,plain,(
    ! [X17] :
      ( ( k2_relat_1(X17) = k1_relat_1(k2_funct_1(X17))
        | ~ v2_funct_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( k1_relat_1(X17) = k2_relat_1(k2_funct_1(X17))
        | ~ v2_funct_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_23,plain,(
    ! [X15] :
      ( ( v1_relat_1(k2_funct_1(X15))
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( v1_funct_1(k2_funct_1(X15))
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_24,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,plain,
    ( k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_28,plain,(
    ! [X5,X6] :
      ( ~ v1_relat_1(X5)
      | ~ v1_relat_1(X6)
      | k2_relat_1(k5_relat_1(X5,X6)) = k9_relat_1(X6,k2_relat_1(X5)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t160_relat_1])])])).

cnf(c_0_29,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,plain,
    ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,plain,
    ( v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_32,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & v2_funct_1(esk1_0)
    & ( k1_relat_1(k5_relat_1(esk1_0,k2_funct_1(esk1_0))) != k1_relat_1(esk1_0)
      | k2_relat_1(k5_relat_1(esk1_0,k2_funct_1(esk1_0))) != k1_relat_1(esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

cnf(c_0_33,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27])])).

cnf(c_0_37,plain,
    ( k2_relat_1(k5_relat_1(X1,X2)) = k9_relat_1(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( k9_relat_1(k4_relat_1(X1),k2_relat_1(X1)) = k2_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

fof(c_0_39,plain,(
    ! [X14] :
      ( ~ v1_relat_1(X14)
      | ~ v1_funct_1(X14)
      | ~ v2_funct_1(X14)
      | k2_funct_1(X14) = k4_relat_1(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).

cnf(c_0_40,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk1_0,k2_funct_1(esk1_0))) != k1_relat_1(esk1_0)
    | k2_relat_1(k5_relat_1(esk1_0,k2_funct_1(esk1_0))) != k1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( k1_relat_1(k5_relat_1(X1,k2_funct_1(X2))) = k1_relat_1(X1)
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( v2_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_26]),c_0_27])])).

cnf(c_0_45,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_46,plain,
    ( k2_relat_1(k5_relat_1(X1,k4_relat_1(X1))) = k2_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_31])).

cnf(c_0_47,plain,
    ( k2_funct_1(X1) = k4_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_49,negated_conjecture,
    ( k2_relat_1(k5_relat_1(esk1_0,k2_funct_1(esk1_0))) != k1_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45])])).

cnf(c_0_50,plain,
    ( k2_relat_1(k5_relat_1(X1,k2_funct_1(X1))) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk1_0)) = k1_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_42]),c_0_43]),c_0_45])])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_42]),c_0_43]),c_0_45])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:37:51 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.34  # Version: 2.5pre002
% 0.19/0.34  # No SInE strategy applied
% 0.19/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.027 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t45_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 0.19/0.37  fof(t80_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 0.19/0.37  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.19/0.37  fof(fc4_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v2_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 0.19/0.37  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 0.19/0.37  fof(t37_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))&k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 0.19/0.37  fof(dt_k4_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>v1_relat_1(k4_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 0.19/0.37  fof(t58_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k1_relat_1(k5_relat_1(X1,k2_funct_1(X1)))=k1_relat_1(X1)&k2_relat_1(k5_relat_1(X1,k2_funct_1(X1)))=k1_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_funct_1)).
% 0.19/0.37  fof(t46_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X1),k1_relat_1(X2))=>k1_relat_1(k5_relat_1(X1,X2))=k1_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 0.19/0.37  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 0.19/0.37  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.19/0.37  fof(t160_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k2_relat_1(k5_relat_1(X1,X2))=k9_relat_1(X2,k2_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 0.19/0.37  fof(d9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>k2_funct_1(X1)=k4_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 0.19/0.37  fof(c_0_13, plain, ![X8, X9]:(~v1_relat_1(X8)|(~v1_relat_1(X9)|r1_tarski(k2_relat_1(k5_relat_1(X8,X9)),k2_relat_1(X9)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_relat_1])])])).
% 0.19/0.37  fof(c_0_14, plain, ![X13]:(~v1_relat_1(X13)|k5_relat_1(X13,k6_relat_1(k2_relat_1(X13)))=X13), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).
% 0.19/0.37  fof(c_0_15, plain, ![X12]:(k1_relat_1(k6_relat_1(X12))=X12&k2_relat_1(k6_relat_1(X12))=X12), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.19/0.37  fof(c_0_16, plain, ![X16]:(v1_relat_1(k6_relat_1(X16))&v2_funct_1(k6_relat_1(X16))), inference(variable_rename,[status(thm)],[fc4_funct_1])).
% 0.19/0.37  fof(c_0_17, plain, ![X4]:(~v1_relat_1(X4)|k9_relat_1(X4,k1_relat_1(X4))=k2_relat_1(X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.19/0.37  fof(c_0_18, plain, ![X7]:((k2_relat_1(X7)=k1_relat_1(k4_relat_1(X7))|~v1_relat_1(X7))&(k1_relat_1(X7)=k2_relat_1(k4_relat_1(X7))|~v1_relat_1(X7))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).
% 0.19/0.37  fof(c_0_19, plain, ![X3]:(~v1_relat_1(X3)|v1_relat_1(k4_relat_1(X3))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).
% 0.19/0.37  fof(c_0_20, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k1_relat_1(k5_relat_1(X1,k2_funct_1(X1)))=k1_relat_1(X1)&k2_relat_1(k5_relat_1(X1,k2_funct_1(X1)))=k1_relat_1(X1))))), inference(assume_negation,[status(cth)],[t58_funct_1])).
% 0.19/0.37  fof(c_0_21, plain, ![X10, X11]:(~v1_relat_1(X10)|(~v1_relat_1(X11)|(~r1_tarski(k2_relat_1(X10),k1_relat_1(X11))|k1_relat_1(k5_relat_1(X10,X11))=k1_relat_1(X10)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_relat_1])])])).
% 0.19/0.37  fof(c_0_22, plain, ![X17]:((k2_relat_1(X17)=k1_relat_1(k2_funct_1(X17))|~v2_funct_1(X17)|(~v1_relat_1(X17)|~v1_funct_1(X17)))&(k1_relat_1(X17)=k2_relat_1(k2_funct_1(X17))|~v2_funct_1(X17)|(~v1_relat_1(X17)|~v1_funct_1(X17)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.19/0.37  fof(c_0_23, plain, ![X15]:((v1_relat_1(k2_funct_1(X15))|(~v1_relat_1(X15)|~v1_funct_1(X15)))&(v1_funct_1(k2_funct_1(X15))|(~v1_relat_1(X15)|~v1_funct_1(X15)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.19/0.37  cnf(c_0_24, plain, (r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_25, plain, (k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_26, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.37  cnf(c_0_27, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.37  fof(c_0_28, plain, ![X5, X6]:(~v1_relat_1(X5)|(~v1_relat_1(X6)|k2_relat_1(k5_relat_1(X5,X6))=k9_relat_1(X6,k2_relat_1(X5)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t160_relat_1])])])).
% 0.19/0.37  cnf(c_0_29, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.37  cnf(c_0_30, plain, (k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.37  cnf(c_0_31, plain, (v1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.37  fof(c_0_32, negated_conjecture, ((v1_relat_1(esk1_0)&v1_funct_1(esk1_0))&(v2_funct_1(esk1_0)&(k1_relat_1(k5_relat_1(esk1_0,k2_funct_1(esk1_0)))!=k1_relat_1(esk1_0)|k2_relat_1(k5_relat_1(esk1_0,k2_funct_1(esk1_0)))!=k1_relat_1(esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.19/0.37  cnf(c_0_33, plain, (k1_relat_1(k5_relat_1(X1,X2))=k1_relat_1(X1)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(k2_relat_1(X1),k1_relat_1(X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.37  cnf(c_0_34, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.37  cnf(c_0_35, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.37  cnf(c_0_36, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27])])).
% 0.19/0.37  cnf(c_0_37, plain, (k2_relat_1(k5_relat_1(X1,X2))=k9_relat_1(X2,k2_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.37  cnf(c_0_38, plain, (k9_relat_1(k4_relat_1(X1),k2_relat_1(X1))=k2_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 0.19/0.37  fof(c_0_39, plain, ![X14]:(~v1_relat_1(X14)|~v1_funct_1(X14)|(~v2_funct_1(X14)|k2_funct_1(X14)=k4_relat_1(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).
% 0.19/0.37  cnf(c_0_40, negated_conjecture, (k1_relat_1(k5_relat_1(esk1_0,k2_funct_1(esk1_0)))!=k1_relat_1(esk1_0)|k2_relat_1(k5_relat_1(esk1_0,k2_funct_1(esk1_0)))!=k1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.37  cnf(c_0_41, plain, (k1_relat_1(k5_relat_1(X1,k2_funct_1(X2)))=k1_relat_1(X1)|~v2_funct_1(X2)|~v1_funct_1(X2)|~r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 0.19/0.37  cnf(c_0_42, negated_conjecture, (v2_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.37  cnf(c_0_43, negated_conjecture, (v1_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.37  cnf(c_0_44, plain, (r1_tarski(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_26]), c_0_27])])).
% 0.19/0.37  cnf(c_0_45, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.37  cnf(c_0_46, plain, (k2_relat_1(k5_relat_1(X1,k4_relat_1(X1)))=k2_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_31])).
% 0.19/0.38  cnf(c_0_47, plain, (k2_funct_1(X1)=k4_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.38  cnf(c_0_48, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.38  cnf(c_0_49, negated_conjecture, (k2_relat_1(k5_relat_1(esk1_0,k2_funct_1(esk1_0)))!=k1_relat_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45])])).
% 0.19/0.38  cnf(c_0_50, plain, (k2_relat_1(k5_relat_1(X1,k2_funct_1(X1)))=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.38  cnf(c_0_51, negated_conjecture, (k2_relat_1(k2_funct_1(esk1_0))=k1_relat_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_42]), c_0_43]), c_0_45])])).
% 0.19/0.38  cnf(c_0_52, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_42]), c_0_43]), c_0_45])]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 53
% 0.19/0.38  # Proof object clause steps            : 26
% 0.19/0.38  # Proof object formula steps           : 27
% 0.19/0.38  # Proof object conjectures             : 10
% 0.19/0.38  # Proof object clause conjectures      : 7
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 17
% 0.19/0.38  # Proof object initial formulas used   : 13
% 0.19/0.38  # Proof object generating inferences   : 9
% 0.19/0.38  # Proof object simplifying inferences  : 21
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 13
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 21
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 21
% 0.19/0.38  # Processed clauses                    : 128
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 26
% 0.19/0.38  # ...remaining for further processing  : 102
% 0.19/0.38  # Other redundant clauses eliminated   : 0
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 2
% 0.19/0.38  # Generated clauses                    : 326
% 0.19/0.38  # ...of the previous two non-trivial   : 264
% 0.19/0.38  # Contextual simplify-reflections      : 8
% 0.19/0.38  # Paramodulations                      : 326
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 0
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 79
% 0.19/0.38  #    Positive orientable unit clauses  : 16
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 1
% 0.19/0.38  #    Non-unit-clauses                  : 62
% 0.19/0.38  # Current number of unprocessed clauses: 163
% 0.19/0.38  # ...number of literals in the above   : 796
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 23
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 737
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 449
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 34
% 0.19/0.38  # Unit Clause-clause subsumption calls : 12
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 5
% 0.19/0.38  # BW rewrite match successes           : 2
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 8755
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.040 s
% 0.19/0.38  # System time              : 0.001 s
% 0.19/0.38  # Total time               : 0.041 s
% 0.19/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
