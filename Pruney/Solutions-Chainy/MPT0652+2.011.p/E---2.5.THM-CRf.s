%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:54 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 126 expanded)
%              Number of clauses        :   30 (  47 expanded)
%              Number of leaves         :   10 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :  156 ( 462 expanded)
%              Number of equality atoms :   58 ( 168 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t59_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k1_relat_1(k5_relat_1(k2_funct_1(X1),X1)) = k2_relat_1(X1)
          & k2_relat_1(k5_relat_1(k2_funct_1(X1),X1)) = k2_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

fof(t198_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( k1_relat_1(X1) = k1_relat_1(X2)
               => k1_relat_1(k5_relat_1(X3,X1)) = k1_relat_1(k5_relat_1(X3,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_relat_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t199_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( k2_relat_1(X1) = k2_relat_1(X2)
               => k2_relat_1(k5_relat_1(X1,X3)) = k2_relat_1(k5_relat_1(X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t199_relat_1)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t80_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(t77_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k5_relat_1(k6_relat_1(X1),X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
         => ( k1_relat_1(k5_relat_1(k2_funct_1(X1),X1)) = k2_relat_1(X1)
            & k2_relat_1(k5_relat_1(k2_funct_1(X1),X1)) = k2_relat_1(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t59_funct_1])).

fof(c_0_11,plain,(
    ! [X6,X7,X8] :
      ( ~ v1_relat_1(X6)
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X8)
      | k1_relat_1(X6) != k1_relat_1(X7)
      | k1_relat_1(k5_relat_1(X8,X6)) = k1_relat_1(k5_relat_1(X8,X7)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t198_relat_1])])])).

fof(c_0_12,plain,(
    ! [X16] :
      ( ( v1_relat_1(k2_funct_1(X16))
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( v1_funct_1(k2_funct_1(X16))
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_13,plain,(
    ! [X9,X10,X11] :
      ( ~ v1_relat_1(X9)
      | ~ v1_relat_1(X10)
      | ~ v1_relat_1(X11)
      | k2_relat_1(X9) != k2_relat_1(X10)
      | k2_relat_1(k5_relat_1(X9,X11)) = k2_relat_1(k5_relat_1(X10,X11)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t199_relat_1])])])).

fof(c_0_14,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & v2_funct_1(esk1_0)
    & ( k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0)) != k2_relat_1(esk1_0)
      | k2_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0)) != k2_relat_1(esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_15,plain,
    ( k1_relat_1(k5_relat_1(X3,X1)) = k1_relat_1(k5_relat_1(X3,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | k1_relat_1(X1) != k1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X18] :
      ( ( k2_relat_1(X18) = k1_relat_1(k2_funct_1(X18))
        | ~ v2_funct_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( k1_relat_1(X18) = k2_relat_1(k2_funct_1(X18))
        | ~ v2_funct_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

cnf(c_0_18,plain,
    ( k2_relat_1(k5_relat_1(X1,X3)) = k2_relat_1(k5_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | k2_relat_1(X1) != k2_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,plain,(
    ! [X17] :
      ( v1_relat_1(k6_relat_1(X17))
      & v1_funct_1(k6_relat_1(X17)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_21,plain,(
    ! [X12] :
      ( k1_relat_1(k6_relat_1(X12)) = X12
      & k2_relat_1(k6_relat_1(X12)) = X12 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_22,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_23,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(X1),X2)) = k1_relat_1(k5_relat_1(k2_funct_1(X1),X3))
    | k1_relat_1(X2) != k1_relat_1(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_25,plain,(
    ! [X15] :
      ( ~ v1_relat_1(X15)
      | k5_relat_1(X15,k6_relat_1(k2_relat_1(X15))) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).

cnf(c_0_26,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( v2_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( k2_relat_1(k5_relat_1(X1,esk1_0)) = k2_relat_1(k5_relat_1(X2,esk1_0))
    | k2_relat_1(X1) != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_29,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_31,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X14)
      | ~ r1_tarski(k1_relat_1(X14),X13)
      | k5_relat_1(k6_relat_1(X13),X14) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),X1)) = k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),X2))
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_19])])).

cnf(c_0_34,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,plain,
    ( k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk1_0)) = k1_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_24]),c_0_19])])).

cnf(c_0_37,negated_conjecture,
    ( k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(X1)),esk1_0)) = k2_relat_1(k5_relat_1(X1,esk1_0))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_38,plain,
    ( k5_relat_1(k6_relat_1(X2),X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),k6_relat_1(k1_relat_1(X1)))) = k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_29]),c_0_34])])).

cnf(c_0_41,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk1_0),k6_relat_1(k1_relat_1(esk1_0))) = k2_funct_1(esk1_0)
    | ~ v1_relat_1(k2_funct_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),esk1_0)) = k2_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0))
    | ~ v1_relat_1(k2_funct_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_36])).

cnf(c_0_43,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0)) != k2_relat_1(esk1_0)
    | k2_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0)) != k2_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_45,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0)) = k1_relat_1(k2_funct_1(esk1_0))
    | ~ v1_relat_1(k2_funct_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_19])])).

cnf(c_0_46,negated_conjecture,
    ( k2_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0)) = k2_relat_1(esk1_0)
    | ~ v1_relat_1(k2_funct_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_19])])).

cnf(c_0_47,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk1_0)) != k2_relat_1(esk1_0)
    | ~ v1_relat_1(k2_funct_1(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])).

cnf(c_0_48,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_49,negated_conjecture,
    ( ~ v1_relat_1(k2_funct_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_27]),c_0_24]),c_0_19])])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_16]),c_0_24]),c_0_19])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:42:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t59_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k1_relat_1(k5_relat_1(k2_funct_1(X1),X1))=k2_relat_1(X1)&k2_relat_1(k5_relat_1(k2_funct_1(X1),X1))=k2_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_funct_1)).
% 0.13/0.38  fof(t198_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(k1_relat_1(X1)=k1_relat_1(X2)=>k1_relat_1(k5_relat_1(X3,X1))=k1_relat_1(k5_relat_1(X3,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t198_relat_1)).
% 0.13/0.38  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.13/0.38  fof(t199_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(k2_relat_1(X1)=k2_relat_1(X2)=>k2_relat_1(k5_relat_1(X1,X3))=k2_relat_1(k5_relat_1(X2,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t199_relat_1)).
% 0.13/0.38  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 0.13/0.38  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.13/0.38  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.13/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.38  fof(t80_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 0.13/0.38  fof(t77_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k5_relat_1(k6_relat_1(X1),X2)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 0.13/0.38  fof(c_0_10, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k1_relat_1(k5_relat_1(k2_funct_1(X1),X1))=k2_relat_1(X1)&k2_relat_1(k5_relat_1(k2_funct_1(X1),X1))=k2_relat_1(X1))))), inference(assume_negation,[status(cth)],[t59_funct_1])).
% 0.13/0.38  fof(c_0_11, plain, ![X6, X7, X8]:(~v1_relat_1(X6)|(~v1_relat_1(X7)|(~v1_relat_1(X8)|(k1_relat_1(X6)!=k1_relat_1(X7)|k1_relat_1(k5_relat_1(X8,X6))=k1_relat_1(k5_relat_1(X8,X7)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t198_relat_1])])])).
% 0.13/0.38  fof(c_0_12, plain, ![X16]:((v1_relat_1(k2_funct_1(X16))|(~v1_relat_1(X16)|~v1_funct_1(X16)))&(v1_funct_1(k2_funct_1(X16))|(~v1_relat_1(X16)|~v1_funct_1(X16)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.13/0.38  fof(c_0_13, plain, ![X9, X10, X11]:(~v1_relat_1(X9)|(~v1_relat_1(X10)|(~v1_relat_1(X11)|(k2_relat_1(X9)!=k2_relat_1(X10)|k2_relat_1(k5_relat_1(X9,X11))=k2_relat_1(k5_relat_1(X10,X11)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t199_relat_1])])])).
% 0.13/0.38  fof(c_0_14, negated_conjecture, ((v1_relat_1(esk1_0)&v1_funct_1(esk1_0))&(v2_funct_1(esk1_0)&(k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0))!=k2_relat_1(esk1_0)|k2_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0))!=k2_relat_1(esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.13/0.38  cnf(c_0_15, plain, (k1_relat_1(k5_relat_1(X3,X1))=k1_relat_1(k5_relat_1(X3,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)|k1_relat_1(X1)!=k1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_16, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  fof(c_0_17, plain, ![X18]:((k2_relat_1(X18)=k1_relat_1(k2_funct_1(X18))|~v2_funct_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18)))&(k1_relat_1(X18)=k2_relat_1(k2_funct_1(X18))|~v2_funct_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.13/0.38  cnf(c_0_18, plain, (k2_relat_1(k5_relat_1(X1,X3))=k2_relat_1(k5_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)|k2_relat_1(X1)!=k2_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  fof(c_0_20, plain, ![X17]:(v1_relat_1(k6_relat_1(X17))&v1_funct_1(k6_relat_1(X17))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.13/0.38  fof(c_0_21, plain, ![X12]:(k1_relat_1(k6_relat_1(X12))=X12&k2_relat_1(k6_relat_1(X12))=X12), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.13/0.38  fof(c_0_22, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.38  cnf(c_0_23, plain, (k1_relat_1(k5_relat_1(k2_funct_1(X1),X2))=k1_relat_1(k5_relat_1(k2_funct_1(X1),X3))|k1_relat_1(X2)!=k1_relat_1(X3)|~v1_funct_1(X1)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (v1_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  fof(c_0_25, plain, ![X15]:(~v1_relat_1(X15)|k5_relat_1(X15,k6_relat_1(k2_relat_1(X15)))=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).
% 0.13/0.38  cnf(c_0_26, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (v2_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (k2_relat_1(k5_relat_1(X1,esk1_0))=k2_relat_1(k5_relat_1(X2,esk1_0))|k2_relat_1(X1)!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.13/0.38  cnf(c_0_29, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_30, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  fof(c_0_31, plain, ![X13, X14]:(~v1_relat_1(X14)|(~r1_tarski(k1_relat_1(X14),X13)|k5_relat_1(k6_relat_1(X13),X14)=X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).
% 0.13/0.38  cnf(c_0_32, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),X1))=k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),X2))|k1_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_19])])).
% 0.13/0.38  cnf(c_0_34, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_35, plain, (k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (k2_relat_1(k2_funct_1(esk1_0))=k1_relat_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_24]), c_0_19])])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(X1)),esk1_0))=k2_relat_1(k5_relat_1(X1,esk1_0))|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])])).
% 0.13/0.38  cnf(c_0_38, plain, (k5_relat_1(k6_relat_1(X2),X1)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.38  cnf(c_0_39, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_32])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),k6_relat_1(k1_relat_1(X1))))=k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),X1))|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_29]), c_0_34])])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (k5_relat_1(k2_funct_1(esk1_0),k6_relat_1(k1_relat_1(esk1_0)))=k2_funct_1(esk1_0)|~v1_relat_1(k2_funct_1(esk1_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),esk1_0))=k2_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0))|~v1_relat_1(k2_funct_1(esk1_0))), inference(spm,[status(thm)],[c_0_37, c_0_36])).
% 0.13/0.38  cnf(c_0_43, plain, (k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0))!=k2_relat_1(esk1_0)|k2_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0))!=k2_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0))=k1_relat_1(k2_funct_1(esk1_0))|~v1_relat_1(k2_funct_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_19])])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (k2_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0))=k2_relat_1(esk1_0)|~v1_relat_1(k2_funct_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_19])])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, (k1_relat_1(k2_funct_1(esk1_0))!=k2_relat_1(esk1_0)|~v1_relat_1(k2_funct_1(esk1_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])).
% 0.13/0.38  cnf(c_0_48, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (~v1_relat_1(k2_funct_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_27]), c_0_24]), c_0_19])])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_16]), c_0_24]), c_0_19])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 51
% 0.13/0.38  # Proof object clause steps            : 30
% 0.13/0.38  # Proof object formula steps           : 21
% 0.13/0.38  # Proof object conjectures             : 19
% 0.13/0.38  # Proof object clause conjectures      : 16
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 15
% 0.13/0.38  # Proof object initial formulas used   : 10
% 0.13/0.38  # Proof object generating inferences   : 14
% 0.13/0.38  # Proof object simplifying inferences  : 22
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 10
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 19
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 19
% 0.13/0.38  # Processed clauses                    : 166
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 50
% 0.13/0.38  # ...remaining for further processing  : 116
% 0.13/0.38  # Other redundant clauses eliminated   : 13
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 0
% 0.13/0.38  # Generated clauses                    : 655
% 0.13/0.38  # ...of the previous two non-trivial   : 624
% 0.13/0.38  # Contextual simplify-reflections      : 6
% 0.13/0.38  # Paramodulations                      : 640
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 15
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
% 0.13/0.38  # Current number of processed clauses  : 96
% 0.13/0.38  #    Positive orientable unit clauses  : 11
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 1
% 0.13/0.38  #    Non-unit-clauses                  : 84
% 0.13/0.38  # Current number of unprocessed clauses: 495
% 0.13/0.38  # ...number of literals in the above   : 2281
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 18
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 582
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 391
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 56
% 0.13/0.38  # Unit Clause-clause subsumption calls : 30
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 2
% 0.13/0.38  # BW rewrite match successes           : 0
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 19454
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.039 s
% 0.13/0.38  # System time              : 0.009 s
% 0.13/0.38  # Total time               : 0.048 s
% 0.13/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
