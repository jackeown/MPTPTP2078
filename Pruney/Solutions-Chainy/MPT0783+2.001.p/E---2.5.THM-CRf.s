%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:54 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   43 (  95 expanded)
%              Number of clauses        :   26 (  35 expanded)
%              Number of leaves         :    8 (  24 expanded)
%              Depth                    :   13
%              Number of atoms          :  165 ( 418 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
      <=> ( v1_relat_2(X1)
          & v8_relat_2(X1)
          & v4_relat_2(X1)
          & v6_relat_2(X1)
          & v1_wellord1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

fof(t31_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v1_wellord1(X2)
       => v1_wellord1(k2_wellord1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_wellord1)).

fof(dt_k2_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k2_wellord1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(t23_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v6_relat_2(X2)
       => v6_relat_2(k2_wellord1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_wellord1)).

fof(t25_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_2(X2)
       => v4_relat_2(k2_wellord1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_wellord1)).

fof(t24_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v8_relat_2(X2)
       => v8_relat_2(k2_wellord1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_wellord1)).

fof(t32_wellord1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v2_wellord1(X2)
       => v2_wellord1(k2_wellord1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_wellord1)).

fof(t22_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v1_relat_2(X2)
       => v1_relat_2(k2_wellord1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_wellord1)).

fof(c_0_8,plain,(
    ! [X3] :
      ( ( v1_relat_2(X3)
        | ~ v2_wellord1(X3)
        | ~ v1_relat_1(X3) )
      & ( v8_relat_2(X3)
        | ~ v2_wellord1(X3)
        | ~ v1_relat_1(X3) )
      & ( v4_relat_2(X3)
        | ~ v2_wellord1(X3)
        | ~ v1_relat_1(X3) )
      & ( v6_relat_2(X3)
        | ~ v2_wellord1(X3)
        | ~ v1_relat_1(X3) )
      & ( v1_wellord1(X3)
        | ~ v2_wellord1(X3)
        | ~ v1_relat_1(X3) )
      & ( ~ v1_relat_2(X3)
        | ~ v8_relat_2(X3)
        | ~ v4_relat_2(X3)
        | ~ v6_relat_2(X3)
        | ~ v1_wellord1(X3)
        | v2_wellord1(X3)
        | ~ v1_relat_1(X3) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).

fof(c_0_9,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X15)
      | ~ v1_wellord1(X15)
      | v1_wellord1(k2_wellord1(X15,X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_wellord1])])).

fof(c_0_10,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X4)
      | v1_relat_1(k2_wellord1(X4,X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_wellord1])])).

cnf(c_0_11,plain,
    ( v2_wellord1(X1)
    | ~ v1_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ v4_relat_2(X1)
    | ~ v6_relat_2(X1)
    | ~ v1_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( v1_wellord1(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_wellord1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( v1_relat_1(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(X9)
      | ~ v6_relat_2(X9)
      | v6_relat_2(k2_wellord1(X9,X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_wellord1])])).

cnf(c_0_15,plain,
    ( v2_wellord1(k2_wellord1(X1,X2))
    | ~ v1_wellord1(X1)
    | ~ v6_relat_2(k2_wellord1(X1,X2))
    | ~ v4_relat_2(k2_wellord1(X1,X2))
    | ~ v8_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])).

cnf(c_0_16,plain,
    ( v6_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v6_relat_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_17,plain,(
    ! [X12,X13] :
      ( ~ v1_relat_1(X13)
      | ~ v4_relat_2(X13)
      | v4_relat_2(k2_wellord1(X13,X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_wellord1])])).

cnf(c_0_18,plain,
    ( v2_wellord1(k2_wellord1(X1,X2))
    | ~ v1_wellord1(X1)
    | ~ v6_relat_2(X1)
    | ~ v4_relat_2(k2_wellord1(X1,X2))
    | ~ v8_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,plain,
    ( v4_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v4_relat_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_20,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X11)
      | ~ v8_relat_2(X11)
      | v8_relat_2(k2_wellord1(X11,X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_wellord1])])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( v2_wellord1(X2)
         => v2_wellord1(k2_wellord1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t32_wellord1])).

cnf(c_0_22,plain,
    ( v2_wellord1(k2_wellord1(X1,X2))
    | ~ v1_wellord1(X1)
    | ~ v6_relat_2(X1)
    | ~ v4_relat_2(X1)
    | ~ v8_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( v8_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v8_relat_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_24,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(X7)
      | ~ v1_relat_2(X7)
      | v1_relat_2(k2_wellord1(X7,X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_wellord1])])).

fof(c_0_25,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v2_wellord1(esk2_0)
    & ~ v2_wellord1(k2_wellord1(esk2_0,esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

cnf(c_0_26,plain,
    ( v2_wellord1(k2_wellord1(X1,X2))
    | ~ v1_wellord1(X1)
    | ~ v6_relat_2(X1)
    | ~ v4_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ v1_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,plain,
    ( v1_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_wellord1(k2_wellord1(esk2_0,esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,plain,
    ( v2_wellord1(k2_wellord1(X1,X2))
    | ~ v1_wellord1(X1)
    | ~ v6_relat_2(X1)
    | ~ v4_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ v1_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_wellord1(esk2_0)
    | ~ v6_relat_2(esk2_0)
    | ~ v4_relat_2(esk2_0)
    | ~ v8_relat_2(esk2_0)
    | ~ v1_relat_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_32,plain,
    ( v1_wellord1(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_33,negated_conjecture,
    ( v2_wellord1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( ~ v6_relat_2(esk2_0)
    | ~ v4_relat_2(esk2_0)
    | ~ v8_relat_2(esk2_0)
    | ~ v1_relat_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_30])])).

cnf(c_0_35,plain,
    ( v6_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_36,negated_conjecture,
    ( ~ v4_relat_2(esk2_0)
    | ~ v8_relat_2(esk2_0)
    | ~ v1_relat_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_33]),c_0_30])])).

cnf(c_0_37,plain,
    ( v4_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_38,negated_conjecture,
    ( ~ v8_relat_2(esk2_0)
    | ~ v1_relat_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_33]),c_0_30])])).

cnf(c_0_39,plain,
    ( v8_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_40,negated_conjecture,
    ( ~ v1_relat_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_33]),c_0_30])])).

cnf(c_0_41,plain,
    ( v1_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_33]),c_0_30])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:15:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_E___103_C18_F1_PI_AE_Q4_CS_SP_S0Y
% 0.14/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.027 s
% 0.14/0.37  
% 0.14/0.37  # Proof found!
% 0.14/0.37  # SZS status Theorem
% 0.14/0.37  # SZS output start CNFRefutation
% 0.14/0.37  fof(d4_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v2_wellord1(X1)<=>((((v1_relat_2(X1)&v8_relat_2(X1))&v4_relat_2(X1))&v6_relat_2(X1))&v1_wellord1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_wellord1)).
% 0.14/0.37  fof(t31_wellord1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v1_wellord1(X2)=>v1_wellord1(k2_wellord1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_wellord1)).
% 0.14/0.37  fof(dt_k2_wellord1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k2_wellord1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_wellord1)).
% 0.14/0.37  fof(t23_wellord1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v6_relat_2(X2)=>v6_relat_2(k2_wellord1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_wellord1)).
% 0.14/0.37  fof(t25_wellord1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_2(X2)=>v4_relat_2(k2_wellord1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_wellord1)).
% 0.14/0.37  fof(t24_wellord1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v8_relat_2(X2)=>v8_relat_2(k2_wellord1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_wellord1)).
% 0.14/0.37  fof(t32_wellord1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(v2_wellord1(X2)=>v2_wellord1(k2_wellord1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_wellord1)).
% 0.14/0.37  fof(t22_wellord1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v1_relat_2(X2)=>v1_relat_2(k2_wellord1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_wellord1)).
% 0.14/0.37  fof(c_0_8, plain, ![X3]:((((((v1_relat_2(X3)|~v2_wellord1(X3)|~v1_relat_1(X3))&(v8_relat_2(X3)|~v2_wellord1(X3)|~v1_relat_1(X3)))&(v4_relat_2(X3)|~v2_wellord1(X3)|~v1_relat_1(X3)))&(v6_relat_2(X3)|~v2_wellord1(X3)|~v1_relat_1(X3)))&(v1_wellord1(X3)|~v2_wellord1(X3)|~v1_relat_1(X3)))&(~v1_relat_2(X3)|~v8_relat_2(X3)|~v4_relat_2(X3)|~v6_relat_2(X3)|~v1_wellord1(X3)|v2_wellord1(X3)|~v1_relat_1(X3))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).
% 0.14/0.37  fof(c_0_9, plain, ![X14, X15]:(~v1_relat_1(X15)|(~v1_wellord1(X15)|v1_wellord1(k2_wellord1(X15,X14)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_wellord1])])).
% 0.14/0.37  fof(c_0_10, plain, ![X4, X5]:(~v1_relat_1(X4)|v1_relat_1(k2_wellord1(X4,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_wellord1])])).
% 0.14/0.37  cnf(c_0_11, plain, (v2_wellord1(X1)|~v1_relat_2(X1)|~v8_relat_2(X1)|~v4_relat_2(X1)|~v6_relat_2(X1)|~v1_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_12, plain, (v1_wellord1(k2_wellord1(X1,X2))|~v1_relat_1(X1)|~v1_wellord1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.37  cnf(c_0_13, plain, (v1_relat_1(k2_wellord1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.37  fof(c_0_14, plain, ![X8, X9]:(~v1_relat_1(X9)|(~v6_relat_2(X9)|v6_relat_2(k2_wellord1(X9,X8)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_wellord1])])).
% 0.14/0.37  cnf(c_0_15, plain, (v2_wellord1(k2_wellord1(X1,X2))|~v1_wellord1(X1)|~v6_relat_2(k2_wellord1(X1,X2))|~v4_relat_2(k2_wellord1(X1,X2))|~v8_relat_2(k2_wellord1(X1,X2))|~v1_relat_2(k2_wellord1(X1,X2))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])).
% 0.14/0.37  cnf(c_0_16, plain, (v6_relat_2(k2_wellord1(X1,X2))|~v1_relat_1(X1)|~v6_relat_2(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.37  fof(c_0_17, plain, ![X12, X13]:(~v1_relat_1(X13)|(~v4_relat_2(X13)|v4_relat_2(k2_wellord1(X13,X12)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_wellord1])])).
% 0.14/0.37  cnf(c_0_18, plain, (v2_wellord1(k2_wellord1(X1,X2))|~v1_wellord1(X1)|~v6_relat_2(X1)|~v4_relat_2(k2_wellord1(X1,X2))|~v8_relat_2(k2_wellord1(X1,X2))|~v1_relat_2(k2_wellord1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.14/0.37  cnf(c_0_19, plain, (v4_relat_2(k2_wellord1(X1,X2))|~v1_relat_1(X1)|~v4_relat_2(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.37  fof(c_0_20, plain, ![X10, X11]:(~v1_relat_1(X11)|(~v8_relat_2(X11)|v8_relat_2(k2_wellord1(X11,X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_wellord1])])).
% 0.14/0.37  fof(c_0_21, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(v2_wellord1(X2)=>v2_wellord1(k2_wellord1(X2,X1))))), inference(assume_negation,[status(cth)],[t32_wellord1])).
% 0.14/0.37  cnf(c_0_22, plain, (v2_wellord1(k2_wellord1(X1,X2))|~v1_wellord1(X1)|~v6_relat_2(X1)|~v4_relat_2(X1)|~v8_relat_2(k2_wellord1(X1,X2))|~v1_relat_2(k2_wellord1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.14/0.37  cnf(c_0_23, plain, (v8_relat_2(k2_wellord1(X1,X2))|~v1_relat_1(X1)|~v8_relat_2(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.37  fof(c_0_24, plain, ![X6, X7]:(~v1_relat_1(X7)|(~v1_relat_2(X7)|v1_relat_2(k2_wellord1(X7,X6)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_wellord1])])).
% 0.14/0.37  fof(c_0_25, negated_conjecture, (v1_relat_1(esk2_0)&(v2_wellord1(esk2_0)&~v2_wellord1(k2_wellord1(esk2_0,esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.14/0.37  cnf(c_0_26, plain, (v2_wellord1(k2_wellord1(X1,X2))|~v1_wellord1(X1)|~v6_relat_2(X1)|~v4_relat_2(X1)|~v8_relat_2(X1)|~v1_relat_2(k2_wellord1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.14/0.37  cnf(c_0_27, plain, (v1_relat_2(k2_wellord1(X1,X2))|~v1_relat_1(X1)|~v1_relat_2(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.37  cnf(c_0_28, negated_conjecture, (~v2_wellord1(k2_wellord1(esk2_0,esk1_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.14/0.37  cnf(c_0_29, plain, (v2_wellord1(k2_wellord1(X1,X2))|~v1_wellord1(X1)|~v6_relat_2(X1)|~v4_relat_2(X1)|~v8_relat_2(X1)|~v1_relat_2(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.14/0.37  cnf(c_0_30, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.14/0.37  cnf(c_0_31, negated_conjecture, (~v1_wellord1(esk2_0)|~v6_relat_2(esk2_0)|~v4_relat_2(esk2_0)|~v8_relat_2(esk2_0)|~v1_relat_2(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])])).
% 0.14/0.37  cnf(c_0_32, plain, (v1_wellord1(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_33, negated_conjecture, (v2_wellord1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.14/0.37  cnf(c_0_34, negated_conjecture, (~v6_relat_2(esk2_0)|~v4_relat_2(esk2_0)|~v8_relat_2(esk2_0)|~v1_relat_2(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_30])])).
% 0.14/0.37  cnf(c_0_35, plain, (v6_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_36, negated_conjecture, (~v4_relat_2(esk2_0)|~v8_relat_2(esk2_0)|~v1_relat_2(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_33]), c_0_30])])).
% 0.14/0.37  cnf(c_0_37, plain, (v4_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_38, negated_conjecture, (~v8_relat_2(esk2_0)|~v1_relat_2(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_33]), c_0_30])])).
% 0.14/0.37  cnf(c_0_39, plain, (v8_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_40, negated_conjecture, (~v1_relat_2(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_33]), c_0_30])])).
% 0.14/0.37  cnf(c_0_41, plain, (v1_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_42, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_33]), c_0_30])]), ['proof']).
% 0.14/0.37  # SZS output end CNFRefutation
% 0.14/0.37  # Proof object total steps             : 43
% 0.14/0.37  # Proof object clause steps            : 26
% 0.14/0.37  # Proof object formula steps           : 17
% 0.14/0.37  # Proof object conjectures             : 12
% 0.14/0.37  # Proof object clause conjectures      : 9
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 15
% 0.14/0.37  # Proof object initial formulas used   : 8
% 0.14/0.37  # Proof object generating inferences   : 11
% 0.14/0.37  # Proof object simplifying inferences  : 18
% 0.14/0.37  # Training examples: 0 positive, 0 negative
% 0.14/0.37  # Parsed axioms                        : 8
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 15
% 0.14/0.37  # Removed in clause preprocessing      : 0
% 0.14/0.37  # Initial clauses in saturation        : 15
% 0.14/0.37  # Processed clauses                    : 25
% 0.14/0.37  # ...of these trivial                  : 0
% 0.14/0.37  # ...subsumed                          : 0
% 0.14/0.37  # ...remaining for further processing  : 25
% 0.14/0.37  # Other redundant clauses eliminated   : 0
% 0.14/0.37  # Clauses deleted for lack of memory   : 0
% 0.14/0.37  # Backward-subsumed                    : 3
% 0.14/0.37  # Backward-rewritten                   : 0
% 0.14/0.37  # Generated clauses                    : 16
% 0.14/0.37  # ...of the previous two non-trivial   : 10
% 0.14/0.37  # Contextual simplify-reflections      : 1
% 0.14/0.37  # Paramodulations                      : 16
% 0.14/0.37  # Factorizations                       : 0
% 0.14/0.37  # Equation resolutions                 : 0
% 0.14/0.37  # Propositional unsat checks           : 0
% 0.14/0.37  #    Propositional check models        : 0
% 0.14/0.37  #    Propositional check unsatisfiable : 0
% 0.14/0.37  #    Propositional clauses             : 0
% 0.14/0.37  #    Propositional clauses after purity: 0
% 0.14/0.37  #    Propositional unsat core size     : 0
% 0.14/0.37  #    Propositional preprocessing time  : 0.000
% 0.14/0.37  #    Propositional encoding time       : 0.000
% 0.14/0.37  #    Propositional solver time         : 0.000
% 0.14/0.37  #    Success case prop preproc time    : 0.000
% 0.14/0.37  #    Success case prop encoding time   : 0.000
% 0.14/0.37  #    Success case prop solver time     : 0.000
% 0.14/0.37  # Current number of processed clauses  : 22
% 0.14/0.37  #    Positive orientable unit clauses  : 2
% 0.14/0.37  #    Positive unorientable unit clauses: 0
% 0.14/0.37  #    Negative unit clauses             : 2
% 0.14/0.37  #    Non-unit-clauses                  : 18
% 0.14/0.37  # Current number of unprocessed clauses: 0
% 0.14/0.37  # ...number of literals in the above   : 0
% 0.14/0.37  # Current number of archived formulas  : 0
% 0.14/0.37  # Current number of archived clauses   : 3
% 0.14/0.37  # Clause-clause subsumption calls (NU) : 90
% 0.14/0.37  # Rec. Clause-clause subsumption calls : 20
% 0.14/0.37  # Non-unit clause-clause subsumptions  : 4
% 0.14/0.37  # Unit Clause-clause subsumption calls : 8
% 0.14/0.37  # Rewrite failures with RHS unbound    : 0
% 0.14/0.37  # BW rewrite match attempts            : 0
% 0.14/0.37  # BW rewrite match successes           : 0
% 0.14/0.37  # Condensation attempts                : 0
% 0.14/0.37  # Condensation successes               : 0
% 0.14/0.37  # Termbank termtop insertions          : 1404
% 0.14/0.37  
% 0.14/0.37  # -------------------------------------------------
% 0.14/0.37  # User time                : 0.028 s
% 0.14/0.37  # System time              : 0.003 s
% 0.14/0.37  # Total time               : 0.031 s
% 0.14/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
