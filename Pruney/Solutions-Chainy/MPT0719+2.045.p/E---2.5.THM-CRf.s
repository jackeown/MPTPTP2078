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
% DateTime   : Thu Dec  3 10:55:55 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 180 expanded)
%              Number of clauses        :   30 (  81 expanded)
%              Number of leaves         :   11 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :  154 ( 602 expanded)
%              Number of equality atoms :   55 ( 269 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   19 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(s3_funct_1__e2_25__funct_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( v1_relat_1(X2)
      & v1_funct_1(X2)
      & k1_relat_1(X2) = X1
      & ! [X3] :
          ( r2_hidden(X3,X1)
         => k1_funct_1(X2,X3) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(t62_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
        & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(t205_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k1_relat_1(X2))
      <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(d16_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(t65_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k1_relat_1(X1) = k1_xboole_0
      <=> k2_relat_1(X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(t174_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => v5_funct_1(k1_xboole_0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).

fof(d20_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( v5_funct_1(X2,X1)
          <=> ! [X3] :
                ( r2_hidden(X3,k1_relat_1(X2))
               => r2_hidden(k1_funct_1(X2,X3),k1_funct_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).

fof(c_0_11,plain,(
    ! [X11] :
      ( ( k1_relat_1(X11) != k1_xboole_0
        | X11 = k1_xboole_0
        | ~ v1_relat_1(X11) )
      & ( k2_relat_1(X11) != k1_xboole_0
        | X11 = k1_xboole_0
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

fof(c_0_12,plain,(
    ! [X20,X22] :
      ( v1_relat_1(esk2_1(X20))
      & v1_funct_1(esk2_1(X20))
      & k1_relat_1(esk2_1(X20)) = X20
      & ( ~ r2_hidden(X22,X20)
        | k1_funct_1(esk2_1(X20),X22) = k1_xboole_0 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_25__funct_1])])])])).

cnf(c_0_13,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( k1_relat_1(esk2_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,plain,
    ( v1_relat_1(esk2_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( esk2_1(X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

fof(c_0_17,plain,(
    ! [X10] :
      ( ( k5_relat_1(k1_xboole_0,X10) = k1_xboole_0
        | ~ v1_relat_1(X10) )
      & ( k5_relat_1(X10,k1_xboole_0) = k1_xboole_0
        | ~ v1_relat_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_relat_1])])])).

fof(c_0_18,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X14)
      | k7_relat_1(X14,X13) = k5_relat_1(k6_relat_1(X13),X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_19,plain,(
    ! [X19] :
      ( v1_relat_1(k6_relat_1(X19))
      & v1_funct_1(k6_relat_1(X19)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

cnf(c_0_20,plain,
    ( v1_relat_1(k1_xboole_0)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_21,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(X7)
      | k2_relat_1(k7_relat_1(X7,X6)) = k9_relat_1(X7,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_22,plain,
    ( k5_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X8,X9] :
      ( ( ~ r2_hidden(X8,k1_relat_1(X9))
        | k11_relat_1(X9,X8) != k1_xboole_0
        | ~ v1_relat_1(X9) )
      & ( k11_relat_1(X9,X8) = k1_xboole_0
        | r2_hidden(X8,k1_relat_1(X9))
        | ~ v1_relat_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t205_relat_1])])])).

fof(c_0_27,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X4)
      | k11_relat_1(X4,X5) = k9_relat_1(X4,k1_tarski(X5)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

cnf(c_0_28,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k7_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])]),c_0_25])])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,k1_relat_1(X2))
    | k11_relat_1(X2,X1) != k1_xboole_0
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( k9_relat_1(k1_xboole_0,X1) = k2_relat_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_25])])).

cnf(c_0_33,plain,
    ( k11_relat_1(esk2_1(X1),X2) != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_14]),c_0_15])])).

cnf(c_0_34,plain,
    ( k11_relat_1(k1_xboole_0,X1) = k2_relat_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_25])])).

fof(c_0_35,plain,(
    ! [X12] :
      ( ( k1_relat_1(X12) != k1_xboole_0
        | k2_relat_1(X12) = k1_xboole_0
        | ~ v1_relat_1(X12) )
      & ( k2_relat_1(X12) != k1_xboole_0
        | k1_relat_1(X12) = k1_xboole_0
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).

cnf(c_0_36,plain,
    ( k1_relat_1(k1_xboole_0) = X1
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_14,c_0_16])).

fof(c_0_37,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => v5_funct_1(k1_xboole_0,X1) ) ),
    inference(assume_negation,[status(cth)],[t174_funct_1])).

cnf(c_0_38,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_16]),c_0_34])).

cnf(c_0_39,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_36])).

fof(c_0_41,plain,(
    ! [X15,X16,X17] :
      ( ( ~ v5_funct_1(X16,X15)
        | ~ r2_hidden(X17,k1_relat_1(X16))
        | r2_hidden(k1_funct_1(X16,X17),k1_funct_1(X15,X17))
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( r2_hidden(esk1_2(X15,X16),k1_relat_1(X16))
        | v5_funct_1(X16,X15)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( ~ r2_hidden(k1_funct_1(X16,esk1_2(X15,X16)),k1_funct_1(X15,esk1_2(X15,X16)))
        | v5_funct_1(X16,X15)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_funct_1])])])])])).

cnf(c_0_42,plain,
    ( v1_funct_1(esk2_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_43,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & ~ v5_funct_1(k1_xboole_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_37])])])).

cnf(c_0_44,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_25])])).

cnf(c_0_45,plain,
    ( r2_hidden(esk1_2(X1,X2),k1_relat_1(X2))
    | v5_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,plain,
    ( v1_funct_1(k1_xboole_0)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_16])).

cnf(c_0_47,negated_conjecture,
    ( ~ v5_funct_1(k1_xboole_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_48,plain,
    ( v5_funct_1(X1,X2)
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_40]),c_0_49]),c_0_50]),c_0_25]),c_0_51])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:20:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___103_C18_F1_PI_AE_Q4_CS_SP_S0Y
% 0.13/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 0.13/0.38  fof(s3_funct_1__e2_25__funct_1, axiom, ![X1]:?[X2]:(((v1_relat_1(X2)&v1_funct_1(X2))&k1_relat_1(X2)=X1)&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 0.13/0.38  fof(t62_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k5_relat_1(k1_xboole_0,X1)=k1_xboole_0&k5_relat_1(X1,k1_xboole_0)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 0.13/0.38  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 0.13/0.38  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.13/0.38  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.13/0.38  fof(t205_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 0.13/0.38  fof(d16_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 0.13/0.38  fof(t65_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k1_relat_1(X1)=k1_xboole_0<=>k2_relat_1(X1)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 0.13/0.38  fof(t174_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>v5_funct_1(k1_xboole_0,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_funct_1)).
% 0.13/0.38  fof(d20_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v5_funct_1(X2,X1)<=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X3),k1_funct_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 0.13/0.38  fof(c_0_11, plain, ![X11]:((k1_relat_1(X11)!=k1_xboole_0|X11=k1_xboole_0|~v1_relat_1(X11))&(k2_relat_1(X11)!=k1_xboole_0|X11=k1_xboole_0|~v1_relat_1(X11))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.13/0.38  fof(c_0_12, plain, ![X20, X22]:(((v1_relat_1(esk2_1(X20))&v1_funct_1(esk2_1(X20)))&k1_relat_1(esk2_1(X20))=X20)&(~r2_hidden(X22,X20)|k1_funct_1(esk2_1(X20),X22)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_25__funct_1])])])])).
% 0.13/0.38  cnf(c_0_13, plain, (X1=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_14, plain, (k1_relat_1(esk2_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_15, plain, (v1_relat_1(esk2_1(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_16, plain, (esk2_1(X1)=k1_xboole_0|X1!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])])).
% 0.13/0.38  fof(c_0_17, plain, ![X10]:((k5_relat_1(k1_xboole_0,X10)=k1_xboole_0|~v1_relat_1(X10))&(k5_relat_1(X10,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X10))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_relat_1])])])).
% 0.13/0.38  fof(c_0_18, plain, ![X13, X14]:(~v1_relat_1(X14)|k7_relat_1(X14,X13)=k5_relat_1(k6_relat_1(X13),X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.13/0.38  fof(c_0_19, plain, ![X19]:(v1_relat_1(k6_relat_1(X19))&v1_funct_1(k6_relat_1(X19))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.13/0.38  cnf(c_0_20, plain, (v1_relat_1(k1_xboole_0)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.13/0.38  fof(c_0_21, plain, ![X6, X7]:(~v1_relat_1(X7)|k2_relat_1(k7_relat_1(X7,X6))=k9_relat_1(X7,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.13/0.38  cnf(c_0_22, plain, (k5_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_23, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_24, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_25, plain, (v1_relat_1(k1_xboole_0)), inference(er,[status(thm)],[c_0_20])).
% 0.13/0.38  fof(c_0_26, plain, ![X8, X9]:((~r2_hidden(X8,k1_relat_1(X9))|k11_relat_1(X9,X8)!=k1_xboole_0|~v1_relat_1(X9))&(k11_relat_1(X9,X8)=k1_xboole_0|r2_hidden(X8,k1_relat_1(X9))|~v1_relat_1(X9))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t205_relat_1])])])).
% 0.13/0.38  fof(c_0_27, plain, ![X4, X5]:(~v1_relat_1(X4)|k11_relat_1(X4,X5)=k9_relat_1(X4,k1_tarski(X5))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).
% 0.13/0.38  cnf(c_0_28, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_29, plain, (k7_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])]), c_0_25])])).
% 0.13/0.38  cnf(c_0_30, plain, (~r2_hidden(X1,k1_relat_1(X2))|k11_relat_1(X2,X1)!=k1_xboole_0|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.38  cnf(c_0_31, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.38  cnf(c_0_32, plain, (k9_relat_1(k1_xboole_0,X1)=k2_relat_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_25])])).
% 0.13/0.38  cnf(c_0_33, plain, (k11_relat_1(esk2_1(X1),X2)!=k1_xboole_0|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_14]), c_0_15])])).
% 0.13/0.38  cnf(c_0_34, plain, (k11_relat_1(k1_xboole_0,X1)=k2_relat_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_25])])).
% 0.13/0.38  fof(c_0_35, plain, ![X12]:((k1_relat_1(X12)!=k1_xboole_0|k2_relat_1(X12)=k1_xboole_0|~v1_relat_1(X12))&(k2_relat_1(X12)!=k1_xboole_0|k1_relat_1(X12)=k1_xboole_0|~v1_relat_1(X12))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).
% 0.13/0.38  cnf(c_0_36, plain, (k1_relat_1(k1_xboole_0)=X1|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_14, c_0_16])).
% 0.13/0.38  fof(c_0_37, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>v5_funct_1(k1_xboole_0,X1))), inference(assume_negation,[status(cth)],[t174_funct_1])).
% 0.13/0.38  cnf(c_0_38, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0|X1!=k1_xboole_0|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_16]), c_0_34])).
% 0.13/0.38  cnf(c_0_39, plain, (k2_relat_1(X1)=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.38  cnf(c_0_40, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_36])).
% 0.13/0.38  fof(c_0_41, plain, ![X15, X16, X17]:((~v5_funct_1(X16,X15)|(~r2_hidden(X17,k1_relat_1(X16))|r2_hidden(k1_funct_1(X16,X17),k1_funct_1(X15,X17)))|(~v1_relat_1(X16)|~v1_funct_1(X16))|(~v1_relat_1(X15)|~v1_funct_1(X15)))&((r2_hidden(esk1_2(X15,X16),k1_relat_1(X16))|v5_funct_1(X16,X15)|(~v1_relat_1(X16)|~v1_funct_1(X16))|(~v1_relat_1(X15)|~v1_funct_1(X15)))&(~r2_hidden(k1_funct_1(X16,esk1_2(X15,X16)),k1_funct_1(X15,esk1_2(X15,X16)))|v5_funct_1(X16,X15)|(~v1_relat_1(X16)|~v1_funct_1(X16))|(~v1_relat_1(X15)|~v1_funct_1(X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_funct_1])])])])])).
% 0.13/0.38  cnf(c_0_42, plain, (v1_funct_1(esk2_1(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  fof(c_0_43, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&~v5_funct_1(k1_xboole_0,esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_37])])])).
% 0.13/0.38  cnf(c_0_44, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_25])])).
% 0.13/0.38  cnf(c_0_45, plain, (r2_hidden(esk1_2(X1,X2),k1_relat_1(X2))|v5_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.38  cnf(c_0_46, plain, (v1_funct_1(k1_xboole_0)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_42, c_0_16])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, (~v5_funct_1(k1_xboole_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.38  cnf(c_0_48, plain, (v5_funct_1(X1,X2)|k1_relat_1(X1)!=k1_xboole_0|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.13/0.38  cnf(c_0_49, plain, (v1_funct_1(k1_xboole_0)), inference(er,[status(thm)],[c_0_46])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.38  cnf(c_0_52, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_40]), c_0_49]), c_0_50]), c_0_25]), c_0_51])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 53
% 0.13/0.38  # Proof object clause steps            : 30
% 0.13/0.38  # Proof object formula steps           : 23
% 0.13/0.38  # Proof object conjectures             : 7
% 0.13/0.38  # Proof object clause conjectures      : 4
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 15
% 0.13/0.38  # Proof object initial formulas used   : 11
% 0.13/0.38  # Proof object generating inferences   : 15
% 0.13/0.38  # Proof object simplifying inferences  : 22
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 11
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 23
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 23
% 0.13/0.38  # Processed clauses                    : 50
% 0.13/0.38  # ...of these trivial                  : 1
% 0.13/0.38  # ...subsumed                          : 4
% 0.13/0.38  # ...remaining for further processing  : 45
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 1
% 0.13/0.38  # Backward-rewritten                   : 7
% 0.13/0.38  # Generated clauses                    : 40
% 0.13/0.38  # ...of the previous two non-trivial   : 38
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 37
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 3
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
% 0.13/0.38  # Current number of processed clauses  : 37
% 0.13/0.38  #    Positive orientable unit clauses  : 14
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 2
% 0.13/0.38  #    Non-unit-clauses                  : 21
% 0.13/0.38  # Current number of unprocessed clauses: 11
% 0.13/0.38  # ...number of literals in the above   : 52
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 8
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 155
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 59
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 4
% 0.13/0.38  # Unit Clause-clause subsumption calls : 11
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 5
% 0.13/0.38  # BW rewrite match successes           : 5
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 2000
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.029 s
% 0.13/0.38  # System time              : 0.004 s
% 0.13/0.38  # Total time               : 0.033 s
% 0.13/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
