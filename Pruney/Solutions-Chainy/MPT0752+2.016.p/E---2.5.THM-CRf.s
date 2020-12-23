%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:37 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 287 expanded)
%              Number of clauses        :   33 ( 126 expanded)
%              Number of leaves         :   13 (  80 expanded)
%              Depth                    :   12
%              Number of atoms          :  154 ( 813 expanded)
%              Number of equality atoms :   53 ( 324 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal clause size      :   19 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( X2 = k6_relat_1(X1)
      <=> ( k1_relat_1(X2) = X1
          & ! [X3] :
              ( r2_hidden(X3,X1)
             => k1_funct_1(X2,X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(t149_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_relat_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(t62_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
        & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(t120_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k2_relat_1(X2))
       => k2_relat_1(k8_relat_1(X1,X2)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_relat_1)).

fof(t123_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k5_relat_1(X2,k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(rc3_ordinal1,axiom,(
    ! [X1] :
    ? [X2] :
      ( v1_relat_1(X2)
      & v5_relat_1(X2,X1)
      & v1_funct_1(X2)
      & v5_ordinal1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_ordinal1)).

fof(t45_ordinal1,conjecture,(
    ! [X1] :
      ( v1_relat_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X1)
      & v1_funct_1(k1_xboole_0)
      & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).

fof(t206_relat_1,axiom,(
    ! [X1,X2] :
      ( v4_relat_1(k1_xboole_0,X1)
      & v5_relat_1(k1_xboole_0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t206_relat_1)).

fof(c_0_13,plain,(
    ! [X24,X25,X26] :
      ( ( k1_relat_1(X25) = X24
        | X25 != k6_relat_1(X24)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( ~ r2_hidden(X26,X24)
        | k1_funct_1(X25,X26) = X26
        | X25 != k6_relat_1(X24)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( r2_hidden(esk1_2(X24,X25),X24)
        | k1_relat_1(X25) != X24
        | X25 = k6_relat_1(X24)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( k1_funct_1(X25,esk1_2(X24,X25)) != esk1_2(X24,X25)
        | k1_relat_1(X25) != X24
        | X25 = k6_relat_1(X24)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_funct_1])])])])])).

fof(c_0_14,plain,(
    ! [X23] :
      ( v1_relat_1(k6_relat_1(X23))
      & v1_funct_1(k6_relat_1(X23)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_15,plain,(
    ! [X6] : v1_relat_1(k6_relat_1(X6)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_16,plain,(
    ! [X20] :
      ( ( k1_relat_1(X20) != k1_xboole_0
        | X20 = k1_xboole_0
        | ~ v1_relat_1(X20) )
      & ( k2_relat_1(X20) != k1_xboole_0
        | X20 = k1_xboole_0
        | ~ v1_relat_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

cnf(c_0_17,plain,
    ( k1_relat_1(X1) = X2
    | X1 != k6_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_17]),c_0_18]),c_0_19])])).

fof(c_0_22,plain,(
    ! [X16] :
      ( ~ v1_relat_1(X16)
      | k9_relat_1(X16,k1_xboole_0) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t149_relat_1])])).

cnf(c_0_23,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_19])])])).

fof(c_0_24,plain,(
    ! [X15] :
      ( ~ v1_relat_1(X15)
      | k9_relat_1(X15,k1_relat_1(X15)) = k2_relat_1(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

cnf(c_0_25,plain,
    ( k9_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_23])).

fof(c_0_27,plain,(
    ! [X19] :
      ( ( k5_relat_1(k1_xboole_0,X19) = k1_xboole_0
        | ~ v1_relat_1(X19) )
      & ( k5_relat_1(X19,k1_xboole_0) = k1_xboole_0
        | ~ v1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_relat_1])])])).

fof(c_0_28,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X11)
      | ~ r1_tarski(X10,k2_relat_1(X11))
      | k2_relat_1(k8_relat_1(X10,X11)) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t120_relat_1])])).

cnf(c_0_29,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_23])).

cnf(c_0_31,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_32,plain,(
    ! [X12,X13] :
      ( ~ v1_relat_1(X13)
      | k8_relat_1(X12,X13) = k5_relat_1(X13,k6_relat_1(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).

cnf(c_0_33,plain,
    ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( k2_relat_1(k8_relat_1(X2,X1)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_26]),c_0_30]),c_0_31])).

cnf(c_0_36,plain,
    ( k8_relat_1(X2,X1) = k5_relat_1(X1,k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,plain,
    ( k5_relat_1(k1_xboole_0,k6_relat_1(X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_19])).

fof(c_0_38,plain,(
    ! [X4,X5] :
      ( ( ~ v5_relat_1(X5,X4)
        | r1_tarski(k2_relat_1(X5),X4)
        | ~ v1_relat_1(X5) )
      & ( ~ r1_tarski(k2_relat_1(X5),X4)
        | v5_relat_1(X5,X4)
        | ~ v1_relat_1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_39,plain,(
    ! [X28] :
      ( v1_relat_1(esk2_1(X28))
      & v5_relat_1(esk2_1(X28),X28)
      & v1_funct_1(esk2_1(X28))
      & v5_ordinal1(esk2_1(X28)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc3_ordinal1])])).

fof(c_0_40,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(k1_xboole_0)
        & v5_relat_1(k1_xboole_0,X1)
        & v1_funct_1(k1_xboole_0)
        & v5_ordinal1(k1_xboole_0) ) ),
    inference(assume_negation,[status(cth)],[t45_ordinal1])).

cnf(c_0_41,plain,
    ( k2_relat_1(k8_relat_1(X1,k1_xboole_0)) = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_26])])).

cnf(c_0_42,plain,
    ( k8_relat_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_26]),c_0_37])).

cnf(c_0_43,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,plain,
    ( v5_relat_1(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,plain,
    ( v1_relat_1(esk2_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_46,negated_conjecture,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,esk3_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_40])])])).

fof(c_0_47,plain,(
    ! [X17,X18] :
      ( v4_relat_1(k1_xboole_0,X17)
      & v5_relat_1(k1_xboole_0,X18) ) ),
    inference(variable_rename,[status(thm)],[t206_relat_1])).

cnf(c_0_48,plain,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_35])).

cnf(c_0_49,plain,
    ( r1_tarski(k2_relat_1(esk2_1(X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

cnf(c_0_50,negated_conjecture,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,esk3_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_51,plain,
    ( v5_relat_1(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_52,plain,
    ( X1 = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_53,plain,
    ( k2_relat_1(esk2_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( ~ v5_ordinal1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51])])).

cnf(c_0_55,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_23])).

cnf(c_0_56,plain,
    ( v5_ordinal1(esk2_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_57,plain,
    ( esk2_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_45])])).

cnf(c_0_58,negated_conjecture,
    ( ~ v5_ordinal1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_26])]),c_0_55])])).

cnf(c_0_59,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n023.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:06:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S4b
% 0.13/0.37  # and selection function SelectCQIPrecW.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.027 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t34_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(X2=k6_relat_1(X1)<=>(k1_relat_1(X2)=X1&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 0.13/0.37  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.13/0.37  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.13/0.37  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 0.13/0.37  fof(t149_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_relat_1)).
% 0.13/0.37  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 0.13/0.37  fof(t62_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k5_relat_1(k1_xboole_0,X1)=k1_xboole_0&k5_relat_1(X1,k1_xboole_0)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 0.13/0.37  fof(t120_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k2_relat_1(X2))=>k2_relat_1(k8_relat_1(X1,X2))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_relat_1)).
% 0.13/0.37  fof(t123_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k5_relat_1(X2,k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 0.13/0.37  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.13/0.37  fof(rc3_ordinal1, axiom, ![X1]:?[X2]:(((v1_relat_1(X2)&v5_relat_1(X2,X1))&v1_funct_1(X2))&v5_ordinal1(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_ordinal1)).
% 0.13/0.37  fof(t45_ordinal1, conjecture, ![X1]:(((v1_relat_1(k1_xboole_0)&v5_relat_1(k1_xboole_0,X1))&v1_funct_1(k1_xboole_0))&v5_ordinal1(k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_ordinal1)).
% 0.13/0.37  fof(t206_relat_1, axiom, ![X1, X2]:(v4_relat_1(k1_xboole_0,X1)&v5_relat_1(k1_xboole_0,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t206_relat_1)).
% 0.13/0.37  fof(c_0_13, plain, ![X24, X25, X26]:(((k1_relat_1(X25)=X24|X25!=k6_relat_1(X24)|(~v1_relat_1(X25)|~v1_funct_1(X25)))&(~r2_hidden(X26,X24)|k1_funct_1(X25,X26)=X26|X25!=k6_relat_1(X24)|(~v1_relat_1(X25)|~v1_funct_1(X25))))&((r2_hidden(esk1_2(X24,X25),X24)|k1_relat_1(X25)!=X24|X25=k6_relat_1(X24)|(~v1_relat_1(X25)|~v1_funct_1(X25)))&(k1_funct_1(X25,esk1_2(X24,X25))!=esk1_2(X24,X25)|k1_relat_1(X25)!=X24|X25=k6_relat_1(X24)|(~v1_relat_1(X25)|~v1_funct_1(X25))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_funct_1])])])])])).
% 0.13/0.37  fof(c_0_14, plain, ![X23]:(v1_relat_1(k6_relat_1(X23))&v1_funct_1(k6_relat_1(X23))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.13/0.37  fof(c_0_15, plain, ![X6]:v1_relat_1(k6_relat_1(X6)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.13/0.37  fof(c_0_16, plain, ![X20]:((k1_relat_1(X20)!=k1_xboole_0|X20=k1_xboole_0|~v1_relat_1(X20))&(k2_relat_1(X20)!=k1_xboole_0|X20=k1_xboole_0|~v1_relat_1(X20))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.13/0.37  cnf(c_0_17, plain, (k1_relat_1(X1)=X2|X1!=k6_relat_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_18, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_19, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  cnf(c_0_20, plain, (X1=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_21, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_17]), c_0_18]), c_0_19])])).
% 0.13/0.37  fof(c_0_22, plain, ![X16]:(~v1_relat_1(X16)|k9_relat_1(X16,k1_xboole_0)=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t149_relat_1])])).
% 0.13/0.37  cnf(c_0_23, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_19])])])).
% 0.13/0.37  fof(c_0_24, plain, ![X15]:(~v1_relat_1(X15)|k9_relat_1(X15,k1_relat_1(X15))=k2_relat_1(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.13/0.37  cnf(c_0_25, plain, (k9_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.37  cnf(c_0_26, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_19, c_0_23])).
% 0.13/0.37  fof(c_0_27, plain, ![X19]:((k5_relat_1(k1_xboole_0,X19)=k1_xboole_0|~v1_relat_1(X19))&(k5_relat_1(X19,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X19))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_relat_1])])])).
% 0.13/0.37  fof(c_0_28, plain, ![X10, X11]:(~v1_relat_1(X11)|(~r1_tarski(X10,k2_relat_1(X11))|k2_relat_1(k8_relat_1(X10,X11))=X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t120_relat_1])])).
% 0.13/0.37  cnf(c_0_29, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.37  cnf(c_0_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_21, c_0_23])).
% 0.13/0.37  cnf(c_0_31, plain, (k9_relat_1(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.13/0.37  fof(c_0_32, plain, ![X12, X13]:(~v1_relat_1(X13)|k8_relat_1(X12,X13)=k5_relat_1(X13,k6_relat_1(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).
% 0.13/0.37  cnf(c_0_33, plain, (k5_relat_1(k1_xboole_0,X1)=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.37  cnf(c_0_34, plain, (k2_relat_1(k8_relat_1(X2,X1))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.37  cnf(c_0_35, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_26]), c_0_30]), c_0_31])).
% 0.13/0.37  cnf(c_0_36, plain, (k8_relat_1(X2,X1)=k5_relat_1(X1,k6_relat_1(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.37  cnf(c_0_37, plain, (k5_relat_1(k1_xboole_0,k6_relat_1(X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_19])).
% 0.13/0.37  fof(c_0_38, plain, ![X4, X5]:((~v5_relat_1(X5,X4)|r1_tarski(k2_relat_1(X5),X4)|~v1_relat_1(X5))&(~r1_tarski(k2_relat_1(X5),X4)|v5_relat_1(X5,X4)|~v1_relat_1(X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.13/0.37  fof(c_0_39, plain, ![X28]:(((v1_relat_1(esk2_1(X28))&v5_relat_1(esk2_1(X28),X28))&v1_funct_1(esk2_1(X28)))&v5_ordinal1(esk2_1(X28))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc3_ordinal1])])).
% 0.13/0.37  fof(c_0_40, negated_conjecture, ~(![X1]:(((v1_relat_1(k1_xboole_0)&v5_relat_1(k1_xboole_0,X1))&v1_funct_1(k1_xboole_0))&v5_ordinal1(k1_xboole_0))), inference(assume_negation,[status(cth)],[t45_ordinal1])).
% 0.13/0.37  cnf(c_0_41, plain, (k2_relat_1(k8_relat_1(X1,k1_xboole_0))=X1|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_26])])).
% 0.13/0.37  cnf(c_0_42, plain, (k8_relat_1(X1,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_26]), c_0_37])).
% 0.13/0.37  cnf(c_0_43, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.37  cnf(c_0_44, plain, (v5_relat_1(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.37  cnf(c_0_45, plain, (v1_relat_1(esk2_1(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.37  fof(c_0_46, negated_conjecture, (~v1_relat_1(k1_xboole_0)|~v5_relat_1(k1_xboole_0,esk3_0)|~v1_funct_1(k1_xboole_0)|~v5_ordinal1(k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_40])])])).
% 0.13/0.37  fof(c_0_47, plain, ![X17, X18]:(v4_relat_1(k1_xboole_0,X17)&v5_relat_1(k1_xboole_0,X18)), inference(variable_rename,[status(thm)],[t206_relat_1])).
% 0.13/0.37  cnf(c_0_48, plain, (k1_xboole_0=X1|~r1_tarski(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42]), c_0_35])).
% 0.13/0.37  cnf(c_0_49, plain, (r1_tarski(k2_relat_1(esk2_1(X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])])).
% 0.13/0.37  cnf(c_0_50, negated_conjecture, (~v1_relat_1(k1_xboole_0)|~v5_relat_1(k1_xboole_0,esk3_0)|~v1_funct_1(k1_xboole_0)|~v5_ordinal1(k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.13/0.37  cnf(c_0_51, plain, (v5_relat_1(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.13/0.37  cnf(c_0_52, plain, (X1=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_53, plain, (k2_relat_1(esk2_1(k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.13/0.37  cnf(c_0_54, negated_conjecture, (~v5_ordinal1(k1_xboole_0)|~v1_funct_1(k1_xboole_0)|~v1_relat_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_51])])).
% 0.13/0.37  cnf(c_0_55, plain, (v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_18, c_0_23])).
% 0.13/0.37  cnf(c_0_56, plain, (v5_ordinal1(esk2_1(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.37  cnf(c_0_57, plain, (esk2_1(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_45])])).
% 0.13/0.37  cnf(c_0_58, negated_conjecture, (~v5_ordinal1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_26])]), c_0_55])])).
% 0.13/0.37  cnf(c_0_59, plain, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 60
% 0.13/0.37  # Proof object clause steps            : 33
% 0.13/0.37  # Proof object formula steps           : 27
% 0.13/0.37  # Proof object conjectures             : 6
% 0.13/0.37  # Proof object clause conjectures      : 3
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 16
% 0.13/0.37  # Proof object initial formulas used   : 13
% 0.13/0.37  # Proof object generating inferences   : 13
% 0.13/0.37  # Proof object simplifying inferences  : 25
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 18
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 31
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 31
% 0.13/0.37  # Processed clauses                    : 102
% 0.13/0.37  # ...of these trivial                  : 4
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 98
% 0.13/0.37  # Other redundant clauses eliminated   : 5
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 7
% 0.13/0.37  # Generated clauses                    : 132
% 0.13/0.37  # ...of the previous two non-trivial   : 94
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 127
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 5
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 58
% 0.13/0.37  #    Positive orientable unit clauses  : 38
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 1
% 0.13/0.37  #    Non-unit-clauses                  : 19
% 0.13/0.37  # Current number of unprocessed clauses: 51
% 0.13/0.37  # ...number of literals in the above   : 55
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 36
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 52
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 39
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.37  # Unit Clause-clause subsumption calls : 4
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 8
% 0.13/0.37  # BW rewrite match successes           : 6
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 3082
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.034 s
% 0.13/0.37  # System time              : 0.001 s
% 0.13/0.37  # Total time               : 0.035 s
% 0.13/0.37  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
