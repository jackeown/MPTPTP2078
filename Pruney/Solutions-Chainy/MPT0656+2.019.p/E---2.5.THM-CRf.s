%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:03 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   44 (  90 expanded)
%              Number of clauses        :   23 (  31 expanded)
%              Number of leaves         :   10 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :  139 ( 412 expanded)
%              Number of equality atoms :   40 ( 138 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t80_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

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

fof(t63_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & k2_relat_1(X1) = k1_relat_1(X2)
              & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X1)) )
           => X2 = k2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

fof(t55_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(t61_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
          & k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(t45_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

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

fof(t77_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k5_relat_1(k6_relat_1(X1),X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(c_0_10,plain,(
    ! [X12] :
      ( ~ v1_relat_1(X12)
      | k5_relat_1(X12,k6_relat_1(k2_relat_1(X12))) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).

fof(c_0_11,plain,(
    ! [X15] :
      ( ( k2_relat_1(X15) = k1_relat_1(k2_funct_1(X15))
        | ~ v2_funct_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( k1_relat_1(X15) = k2_relat_1(k2_funct_1(X15))
        | ~ v2_funct_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_12,plain,(
    ! [X13] :
      ( ( v1_relat_1(k2_funct_1(X13))
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( v1_funct_1(k2_funct_1(X13))
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ( ( v2_funct_1(X1)
                & k2_relat_1(X1) = k1_relat_1(X2)
                & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X1)) )
             => X2 = k2_funct_1(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t63_funct_1])).

cnf(c_0_14,plain,
    ( k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & v2_funct_1(esk1_0)
    & k2_relat_1(esk1_0) = k1_relat_1(esk2_0)
    & k5_relat_1(esk1_0,esk2_0) = k6_relat_1(k1_relat_1(esk1_0))
    & esk2_0 != k2_funct_1(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_18,plain,(
    ! [X6,X7,X8] :
      ( ~ v1_relat_1(X6)
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X8)
      | k5_relat_1(k5_relat_1(X6,X7),X8) = k5_relat_1(X6,k5_relat_1(X7,X8)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).

fof(c_0_19,plain,(
    ! [X16] :
      ( ( k5_relat_1(X16,k2_funct_1(X16)) = k6_relat_1(k1_relat_1(X16))
        | ~ v2_funct_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( k5_relat_1(k2_funct_1(X16),X16) = k6_relat_1(k2_relat_1(X16))
        | ~ v2_funct_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).

fof(c_0_20,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X4)
      | ~ v1_relat_1(X5)
      | r1_tarski(k2_relat_1(k5_relat_1(X4,X5)),k2_relat_1(X5)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_relat_1])])])).

fof(c_0_21,plain,(
    ! [X9] :
      ( k1_relat_1(k6_relat_1(X9)) = X9
      & k2_relat_1(k6_relat_1(X9)) = X9 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_22,plain,(
    ! [X14] :
      ( v1_relat_1(k6_relat_1(X14))
      & v2_funct_1(k6_relat_1(X14)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

cnf(c_0_23,plain,
    ( k5_relat_1(k2_funct_1(X1),k6_relat_1(k1_relat_1(X1))) = k2_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( k5_relat_1(esk1_0,esk2_0) = k6_relat_1(k1_relat_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( v2_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_33,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X11)
      | ~ r1_tarski(k1_relat_1(X11),X10)
      | k5_relat_1(k6_relat_1(X10),X11) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).

cnf(c_0_34,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk1_0),k5_relat_1(esk1_0,esk2_0)) = k2_funct_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26]),c_0_27])])).

cnf(c_0_35,plain,
    ( k5_relat_1(k2_funct_1(X1),k5_relat_1(X1,X2)) = k5_relat_1(k6_relat_1(k2_relat_1(X1)),X2)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_16])).

cnf(c_0_36,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_37,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_14]),c_0_31]),c_0_32])])).

cnf(c_0_38,plain,
    ( k5_relat_1(k6_relat_1(X2),X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k2_relat_1(esk1_0)),esk2_0) = k2_funct_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_25]),c_0_26]),c_0_36]),c_0_27])])).

cnf(c_0_40,negated_conjecture,
    ( k2_relat_1(esk1_0) = k1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_31]),c_0_32])])).

cnf(c_0_42,negated_conjecture,
    ( esk2_0 != k2_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_41]),c_0_36])]),c_0_42]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:39:53 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S060A
% 0.18/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.18/0.38  #
% 0.18/0.38  # Preprocessing time       : 0.027 s
% 0.18/0.38  # Presaturation interreduction done
% 0.18/0.38  
% 0.18/0.38  # Proof found!
% 0.18/0.38  # SZS status Theorem
% 0.18/0.38  # SZS output start CNFRefutation
% 0.18/0.38  fof(t80_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 0.18/0.38  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 0.18/0.38  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.18/0.38  fof(t63_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(((v2_funct_1(X1)&k2_relat_1(X1)=k1_relat_1(X2))&k5_relat_1(X1,X2)=k6_relat_1(k1_relat_1(X1)))=>X2=k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_funct_1)).
% 0.18/0.38  fof(t55_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 0.18/0.38  fof(t61_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))&k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 0.18/0.38  fof(t45_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 0.18/0.38  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.18/0.38  fof(fc4_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v2_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 0.18/0.38  fof(t77_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k5_relat_1(k6_relat_1(X1),X2)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 0.18/0.38  fof(c_0_10, plain, ![X12]:(~v1_relat_1(X12)|k5_relat_1(X12,k6_relat_1(k2_relat_1(X12)))=X12), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).
% 0.18/0.38  fof(c_0_11, plain, ![X15]:((k2_relat_1(X15)=k1_relat_1(k2_funct_1(X15))|~v2_funct_1(X15)|(~v1_relat_1(X15)|~v1_funct_1(X15)))&(k1_relat_1(X15)=k2_relat_1(k2_funct_1(X15))|~v2_funct_1(X15)|(~v1_relat_1(X15)|~v1_funct_1(X15)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.18/0.38  fof(c_0_12, plain, ![X13]:((v1_relat_1(k2_funct_1(X13))|(~v1_relat_1(X13)|~v1_funct_1(X13)))&(v1_funct_1(k2_funct_1(X13))|(~v1_relat_1(X13)|~v1_funct_1(X13)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.18/0.38  fof(c_0_13, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(((v2_funct_1(X1)&k2_relat_1(X1)=k1_relat_1(X2))&k5_relat_1(X1,X2)=k6_relat_1(k1_relat_1(X1)))=>X2=k2_funct_1(X1))))), inference(assume_negation,[status(cth)],[t63_funct_1])).
% 0.18/0.38  cnf(c_0_14, plain, (k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.38  cnf(c_0_15, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.38  cnf(c_0_16, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.38  fof(c_0_17, negated_conjecture, ((v1_relat_1(esk1_0)&v1_funct_1(esk1_0))&((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&(((v2_funct_1(esk1_0)&k2_relat_1(esk1_0)=k1_relat_1(esk2_0))&k5_relat_1(esk1_0,esk2_0)=k6_relat_1(k1_relat_1(esk1_0)))&esk2_0!=k2_funct_1(esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.18/0.38  fof(c_0_18, plain, ![X6, X7, X8]:(~v1_relat_1(X6)|(~v1_relat_1(X7)|(~v1_relat_1(X8)|k5_relat_1(k5_relat_1(X6,X7),X8)=k5_relat_1(X6,k5_relat_1(X7,X8))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).
% 0.18/0.38  fof(c_0_19, plain, ![X16]:((k5_relat_1(X16,k2_funct_1(X16))=k6_relat_1(k1_relat_1(X16))|~v2_funct_1(X16)|(~v1_relat_1(X16)|~v1_funct_1(X16)))&(k5_relat_1(k2_funct_1(X16),X16)=k6_relat_1(k2_relat_1(X16))|~v2_funct_1(X16)|(~v1_relat_1(X16)|~v1_funct_1(X16)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).
% 0.18/0.38  fof(c_0_20, plain, ![X4, X5]:(~v1_relat_1(X4)|(~v1_relat_1(X5)|r1_tarski(k2_relat_1(k5_relat_1(X4,X5)),k2_relat_1(X5)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_relat_1])])])).
% 0.18/0.38  fof(c_0_21, plain, ![X9]:(k1_relat_1(k6_relat_1(X9))=X9&k2_relat_1(k6_relat_1(X9))=X9), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.18/0.38  fof(c_0_22, plain, ![X14]:(v1_relat_1(k6_relat_1(X14))&v2_funct_1(k6_relat_1(X14))), inference(variable_rename,[status(thm)],[fc4_funct_1])).
% 0.18/0.38  cnf(c_0_23, plain, (k5_relat_1(k2_funct_1(X1),k6_relat_1(k1_relat_1(X1)))=k2_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])).
% 0.18/0.38  cnf(c_0_24, negated_conjecture, (k5_relat_1(esk1_0,esk2_0)=k6_relat_1(k1_relat_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.38  cnf(c_0_25, negated_conjecture, (v2_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.38  cnf(c_0_26, negated_conjecture, (v1_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.38  cnf(c_0_27, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.38  cnf(c_0_28, plain, (k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.38  cnf(c_0_29, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.38  cnf(c_0_30, plain, (r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.38  cnf(c_0_31, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.38  cnf(c_0_32, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.38  fof(c_0_33, plain, ![X10, X11]:(~v1_relat_1(X11)|(~r1_tarski(k1_relat_1(X11),X10)|k5_relat_1(k6_relat_1(X10),X11)=X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).
% 0.18/0.38  cnf(c_0_34, negated_conjecture, (k5_relat_1(k2_funct_1(esk1_0),k5_relat_1(esk1_0,esk2_0))=k2_funct_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26]), c_0_27])])).
% 0.18/0.38  cnf(c_0_35, plain, (k5_relat_1(k2_funct_1(X1),k5_relat_1(X1,X2))=k5_relat_1(k6_relat_1(k2_relat_1(X1)),X2)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_16])).
% 0.18/0.38  cnf(c_0_36, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.38  cnf(c_0_37, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_14]), c_0_31]), c_0_32])])).
% 0.18/0.38  cnf(c_0_38, plain, (k5_relat_1(k6_relat_1(X2),X1)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.18/0.38  cnf(c_0_39, negated_conjecture, (k5_relat_1(k6_relat_1(k2_relat_1(esk1_0)),esk2_0)=k2_funct_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_25]), c_0_26]), c_0_36]), c_0_27])])).
% 0.18/0.38  cnf(c_0_40, negated_conjecture, (k2_relat_1(esk1_0)=k1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.38  cnf(c_0_41, plain, (r1_tarski(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_31]), c_0_32])])).
% 0.18/0.38  cnf(c_0_42, negated_conjecture, (esk2_0!=k2_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.38  cnf(c_0_43, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_41]), c_0_36])]), c_0_42]), ['proof']).
% 0.18/0.38  # SZS output end CNFRefutation
% 0.18/0.38  # Proof object total steps             : 44
% 0.18/0.38  # Proof object clause steps            : 23
% 0.18/0.38  # Proof object formula steps           : 21
% 0.18/0.38  # Proof object conjectures             : 13
% 0.18/0.38  # Proof object clause conjectures      : 10
% 0.18/0.38  # Proof object formula conjectures     : 3
% 0.18/0.38  # Proof object initial clauses used    : 16
% 0.18/0.38  # Proof object initial formulas used   : 10
% 0.18/0.38  # Proof object generating inferences   : 7
% 0.18/0.38  # Proof object simplifying inferences  : 21
% 0.18/0.38  # Training examples: 0 positive, 0 negative
% 0.18/0.38  # Parsed axioms                        : 10
% 0.18/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.38  # Initial clauses                      : 22
% 0.18/0.38  # Removed in clause preprocessing      : 0
% 0.18/0.38  # Initial clauses in saturation        : 22
% 0.18/0.38  # Processed clauses                    : 206
% 0.18/0.38  # ...of these trivial                  : 2
% 0.18/0.38  # ...subsumed                          : 42
% 0.18/0.38  # ...remaining for further processing  : 162
% 0.18/0.38  # Other redundant clauses eliminated   : 0
% 0.18/0.38  # Clauses deleted for lack of memory   : 0
% 0.18/0.38  # Backward-subsumed                    : 3
% 0.18/0.38  # Backward-rewritten                   : 8
% 0.18/0.38  # Generated clauses                    : 955
% 0.18/0.38  # ...of the previous two non-trivial   : 727
% 0.18/0.38  # Contextual simplify-reflections      : 11
% 0.18/0.38  # Paramodulations                      : 955
% 0.18/0.38  # Factorizations                       : 0
% 0.18/0.38  # Equation resolutions                 : 0
% 0.18/0.38  # Propositional unsat checks           : 0
% 0.18/0.38  #    Propositional check models        : 0
% 0.18/0.38  #    Propositional check unsatisfiable : 0
% 0.18/0.38  #    Propositional clauses             : 0
% 0.18/0.38  #    Propositional clauses after purity: 0
% 0.18/0.38  #    Propositional unsat core size     : 0
% 0.18/0.38  #    Propositional preprocessing time  : 0.000
% 0.18/0.38  #    Propositional encoding time       : 0.000
% 0.18/0.38  #    Propositional solver time         : 0.000
% 0.18/0.38  #    Success case prop preproc time    : 0.000
% 0.18/0.38  #    Success case prop encoding time   : 0.000
% 0.18/0.38  #    Success case prop solver time     : 0.000
% 0.18/0.38  # Current number of processed clauses  : 129
% 0.18/0.38  #    Positive orientable unit clauses  : 43
% 0.18/0.38  #    Positive unorientable unit clauses: 0
% 0.18/0.38  #    Negative unit clauses             : 1
% 0.18/0.38  #    Non-unit-clauses                  : 85
% 0.18/0.38  # Current number of unprocessed clauses: 551
% 0.18/0.38  # ...number of literals in the above   : 2677
% 0.18/0.38  # Current number of archived formulas  : 0
% 0.18/0.38  # Current number of archived clauses   : 33
% 0.18/0.38  # Clause-clause subsumption calls (NU) : 484
% 0.18/0.38  # Rec. Clause-clause subsumption calls : 337
% 0.18/0.38  # Non-unit clause-clause subsumptions  : 56
% 0.18/0.38  # Unit Clause-clause subsumption calls : 9
% 0.18/0.38  # Rewrite failures with RHS unbound    : 0
% 0.18/0.38  # BW rewrite match attempts            : 90
% 0.18/0.38  # BW rewrite match successes           : 6
% 0.18/0.38  # Condensation attempts                : 0
% 0.18/0.38  # Condensation successes               : 0
% 0.18/0.38  # Termbank termtop insertions          : 22698
% 0.18/0.39  
% 0.18/0.39  # -------------------------------------------------
% 0.18/0.39  # User time                : 0.047 s
% 0.18/0.39  # System time              : 0.004 s
% 0.18/0.39  # Total time               : 0.051 s
% 0.18/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
