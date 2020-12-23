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
% DateTime   : Thu Dec  3 10:53:54 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 134 expanded)
%              Number of clauses        :   32 (  50 expanded)
%              Number of leaves         :   11 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :  162 ( 482 expanded)
%              Number of equality atoms :   62 ( 178 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

fof(t199_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( k2_relat_1(X1) = k2_relat_1(X2)
               => k2_relat_1(k5_relat_1(X1,X3)) = k2_relat_1(k5_relat_1(X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t199_relat_1)).

fof(t198_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( k1_relat_1(X1) = k1_relat_1(X2)
               => k1_relat_1(k5_relat_1(X3,X1)) = k1_relat_1(k5_relat_1(X3,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t198_relat_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t80_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
         => ( k1_relat_1(k5_relat_1(k2_funct_1(X1),X1)) = k2_relat_1(X1)
            & k2_relat_1(k5_relat_1(k2_funct_1(X1),X1)) = k2_relat_1(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t59_funct_1])).

fof(c_0_12,plain,(
    ! [X10,X11,X12] :
      ( ~ v1_relat_1(X10)
      | ~ v1_relat_1(X11)
      | ~ v1_relat_1(X12)
      | k2_relat_1(X10) != k2_relat_1(X11)
      | k2_relat_1(k5_relat_1(X10,X12)) = k2_relat_1(k5_relat_1(X11,X12)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t199_relat_1])])])).

fof(c_0_13,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & v2_funct_1(esk1_0)
    & ( k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0)) != k2_relat_1(esk1_0)
      | k2_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0)) != k2_relat_1(esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_14,plain,(
    ! [X7,X8,X9] :
      ( ~ v1_relat_1(X7)
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(X9)
      | k1_relat_1(X7) != k1_relat_1(X8)
      | k1_relat_1(k5_relat_1(X9,X7)) = k1_relat_1(k5_relat_1(X9,X8)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t198_relat_1])])])).

fof(c_0_15,plain,(
    ! [X19] :
      ( ( v1_relat_1(k2_funct_1(X19))
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( v1_funct_1(k2_funct_1(X19))
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_16,plain,
    ( k2_relat_1(k5_relat_1(X1,X3)) = k2_relat_1(k5_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | k2_relat_1(X1) != k2_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X6] : v1_relat_1(k6_relat_1(X6)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_19,plain,(
    ! [X13] :
      ( k1_relat_1(k6_relat_1(X13)) = X13
      & k2_relat_1(k6_relat_1(X13)) = X13 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_20,plain,
    ( k1_relat_1(k5_relat_1(X3,X1)) = k1_relat_1(k5_relat_1(X3,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | k1_relat_1(X1) != k1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X20] :
      ( ( k2_relat_1(X20) = k1_relat_1(k2_funct_1(X20))
        | ~ v2_funct_1(X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( k1_relat_1(X20) = k2_relat_1(k2_funct_1(X20))
        | ~ v2_funct_1(X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

cnf(c_0_23,negated_conjecture,
    ( k2_relat_1(k5_relat_1(X1,esk1_0)) = k2_relat_1(k5_relat_1(X2,esk1_0))
    | k2_relat_1(X1) != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X16)
      | k7_relat_1(X16,X15) = k5_relat_1(k6_relat_1(X15),X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_27,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_28,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(X1),X2)) = k1_relat_1(k5_relat_1(k2_funct_1(X1),X3))
    | k1_relat_1(X2) != k1_relat_1(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_30,plain,(
    ! [X14] :
      ( ~ v1_relat_1(X14)
      | k5_relat_1(X14,k6_relat_1(k2_relat_1(X14))) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).

cnf(c_0_31,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( v2_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_33,negated_conjecture,
    ( k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(X1)),esk1_0)) = k2_relat_1(k5_relat_1(X1,esk1_0))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_34,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_35,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X18)
      | ~ r1_tarski(k1_relat_1(X18),X17)
      | k7_relat_1(X18,X17) = X18 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),X1)) = k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),X2))
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_17])])).

cnf(c_0_38,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_39,plain,
    ( k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk1_0)) = k1_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_29]),c_0_17])])).

cnf(c_0_41,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk1_0,k2_relat_1(X1))) = k2_relat_1(k5_relat_1(X1,esk1_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_17])])).

cnf(c_0_42,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),k6_relat_1(k1_relat_1(X1)))) = k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_24]),c_0_38])])).

cnf(c_0_45,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk1_0),k6_relat_1(k1_relat_1(esk1_0))) = k2_funct_1(esk1_0)
    | ~ v1_relat_1(k2_funct_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk1_0,k1_relat_1(esk1_0))) = k2_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0))
    | ~ v1_relat_1(k2_funct_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_40])).

cnf(c_0_47,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0)) != k2_relat_1(esk1_0)
    | k2_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0)) != k2_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_49,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0)) = k1_relat_1(k2_funct_1(esk1_0))
    | ~ v1_relat_1(k2_funct_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_17])])).

cnf(c_0_50,negated_conjecture,
    ( k2_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0)) = k2_relat_1(esk1_0)
    | ~ v1_relat_1(k2_funct_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_17])])).

cnf(c_0_51,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk1_0)) != k2_relat_1(esk1_0)
    | ~ v1_relat_1(k2_funct_1(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])).

cnf(c_0_52,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_53,negated_conjecture,
    ( ~ v1_relat_1(k2_funct_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_32]),c_0_29]),c_0_17])])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_21]),c_0_29]),c_0_17])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:50:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.027 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t59_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k1_relat_1(k5_relat_1(k2_funct_1(X1),X1))=k2_relat_1(X1)&k2_relat_1(k5_relat_1(k2_funct_1(X1),X1))=k2_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_funct_1)).
% 0.13/0.39  fof(t199_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(k2_relat_1(X1)=k2_relat_1(X2)=>k2_relat_1(k5_relat_1(X1,X3))=k2_relat_1(k5_relat_1(X2,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t199_relat_1)).
% 0.13/0.39  fof(t198_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(k1_relat_1(X1)=k1_relat_1(X2)=>k1_relat_1(k5_relat_1(X3,X1))=k1_relat_1(k5_relat_1(X3,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t198_relat_1)).
% 0.13/0.39  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.13/0.39  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.13/0.39  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.13/0.39  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 0.13/0.39  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 0.13/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.39  fof(t80_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 0.13/0.39  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 0.13/0.39  fof(c_0_11, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k1_relat_1(k5_relat_1(k2_funct_1(X1),X1))=k2_relat_1(X1)&k2_relat_1(k5_relat_1(k2_funct_1(X1),X1))=k2_relat_1(X1))))), inference(assume_negation,[status(cth)],[t59_funct_1])).
% 0.13/0.39  fof(c_0_12, plain, ![X10, X11, X12]:(~v1_relat_1(X10)|(~v1_relat_1(X11)|(~v1_relat_1(X12)|(k2_relat_1(X10)!=k2_relat_1(X11)|k2_relat_1(k5_relat_1(X10,X12))=k2_relat_1(k5_relat_1(X11,X12)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t199_relat_1])])])).
% 0.13/0.39  fof(c_0_13, negated_conjecture, ((v1_relat_1(esk1_0)&v1_funct_1(esk1_0))&(v2_funct_1(esk1_0)&(k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0))!=k2_relat_1(esk1_0)|k2_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0))!=k2_relat_1(esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.13/0.39  fof(c_0_14, plain, ![X7, X8, X9]:(~v1_relat_1(X7)|(~v1_relat_1(X8)|(~v1_relat_1(X9)|(k1_relat_1(X7)!=k1_relat_1(X8)|k1_relat_1(k5_relat_1(X9,X7))=k1_relat_1(k5_relat_1(X9,X8)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t198_relat_1])])])).
% 0.13/0.39  fof(c_0_15, plain, ![X19]:((v1_relat_1(k2_funct_1(X19))|(~v1_relat_1(X19)|~v1_funct_1(X19)))&(v1_funct_1(k2_funct_1(X19))|(~v1_relat_1(X19)|~v1_funct_1(X19)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.13/0.39  cnf(c_0_16, plain, (k2_relat_1(k5_relat_1(X1,X3))=k2_relat_1(k5_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)|k2_relat_1(X1)!=k2_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_17, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  fof(c_0_18, plain, ![X6]:v1_relat_1(k6_relat_1(X6)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.13/0.39  fof(c_0_19, plain, ![X13]:(k1_relat_1(k6_relat_1(X13))=X13&k2_relat_1(k6_relat_1(X13))=X13), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.13/0.39  cnf(c_0_20, plain, (k1_relat_1(k5_relat_1(X3,X1))=k1_relat_1(k5_relat_1(X3,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)|k1_relat_1(X1)!=k1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.39  cnf(c_0_21, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  fof(c_0_22, plain, ![X20]:((k2_relat_1(X20)=k1_relat_1(k2_funct_1(X20))|~v2_funct_1(X20)|(~v1_relat_1(X20)|~v1_funct_1(X20)))&(k1_relat_1(X20)=k2_relat_1(k2_funct_1(X20))|~v2_funct_1(X20)|(~v1_relat_1(X20)|~v1_funct_1(X20)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.13/0.39  cnf(c_0_23, negated_conjecture, (k2_relat_1(k5_relat_1(X1,esk1_0))=k2_relat_1(k5_relat_1(X2,esk1_0))|k2_relat_1(X1)!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.13/0.39  cnf(c_0_24, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_25, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.39  fof(c_0_26, plain, ![X15, X16]:(~v1_relat_1(X16)|k7_relat_1(X16,X15)=k5_relat_1(k6_relat_1(X15),X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.13/0.39  fof(c_0_27, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.39  cnf(c_0_28, plain, (k1_relat_1(k5_relat_1(k2_funct_1(X1),X2))=k1_relat_1(k5_relat_1(k2_funct_1(X1),X3))|k1_relat_1(X2)!=k1_relat_1(X3)|~v1_funct_1(X1)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.39  cnf(c_0_29, negated_conjecture, (v1_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  fof(c_0_30, plain, ![X14]:(~v1_relat_1(X14)|k5_relat_1(X14,k6_relat_1(k2_relat_1(X14)))=X14), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).
% 0.13/0.39  cnf(c_0_31, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  cnf(c_0_32, negated_conjecture, (v2_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_33, negated_conjecture, (k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(X1)),esk1_0))=k2_relat_1(k5_relat_1(X1,esk1_0))|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])])).
% 0.13/0.39  cnf(c_0_34, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.39  fof(c_0_35, plain, ![X17, X18]:(~v1_relat_1(X18)|(~r1_tarski(k1_relat_1(X18),X17)|k7_relat_1(X18,X17)=X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.13/0.39  cnf(c_0_36, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.39  cnf(c_0_37, negated_conjecture, (k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),X1))=k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),X2))|k1_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_17])])).
% 0.13/0.39  cnf(c_0_38, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.39  cnf(c_0_39, plain, (k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.39  cnf(c_0_40, negated_conjecture, (k2_relat_1(k2_funct_1(esk1_0))=k1_relat_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_29]), c_0_17])])).
% 0.13/0.39  cnf(c_0_41, negated_conjecture, (k2_relat_1(k7_relat_1(esk1_0,k2_relat_1(X1)))=k2_relat_1(k5_relat_1(X1,esk1_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_17])])).
% 0.13/0.39  cnf(c_0_42, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.39  cnf(c_0_43, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_36])).
% 0.13/0.39  cnf(c_0_44, negated_conjecture, (k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),k6_relat_1(k1_relat_1(X1))))=k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),X1))|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_24]), c_0_38])])).
% 0.13/0.39  cnf(c_0_45, negated_conjecture, (k5_relat_1(k2_funct_1(esk1_0),k6_relat_1(k1_relat_1(esk1_0)))=k2_funct_1(esk1_0)|~v1_relat_1(k2_funct_1(esk1_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.13/0.39  cnf(c_0_46, negated_conjecture, (k2_relat_1(k7_relat_1(esk1_0,k1_relat_1(esk1_0)))=k2_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0))|~v1_relat_1(k2_funct_1(esk1_0))), inference(spm,[status(thm)],[c_0_41, c_0_40])).
% 0.13/0.39  cnf(c_0_47, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.13/0.39  cnf(c_0_48, negated_conjecture, (k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0))!=k2_relat_1(esk1_0)|k2_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0))!=k2_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_49, negated_conjecture, (k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0))=k1_relat_1(k2_funct_1(esk1_0))|~v1_relat_1(k2_funct_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_17])])).
% 0.13/0.39  cnf(c_0_50, negated_conjecture, (k2_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0))=k2_relat_1(esk1_0)|~v1_relat_1(k2_funct_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_17])])).
% 0.13/0.39  cnf(c_0_51, negated_conjecture, (k1_relat_1(k2_funct_1(esk1_0))!=k2_relat_1(esk1_0)|~v1_relat_1(k2_funct_1(esk1_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])).
% 0.13/0.39  cnf(c_0_52, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  cnf(c_0_53, negated_conjecture, (~v1_relat_1(k2_funct_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_32]), c_0_29]), c_0_17])])).
% 0.13/0.39  cnf(c_0_54, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_21]), c_0_29]), c_0_17])]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 55
% 0.13/0.39  # Proof object clause steps            : 32
% 0.13/0.39  # Proof object formula steps           : 23
% 0.13/0.39  # Proof object conjectures             : 20
% 0.13/0.39  # Proof object clause conjectures      : 17
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 16
% 0.13/0.39  # Proof object initial formulas used   : 11
% 0.13/0.39  # Proof object generating inferences   : 15
% 0.13/0.39  # Proof object simplifying inferences  : 24
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 11
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 19
% 0.13/0.39  # Removed in clause preprocessing      : 0
% 0.13/0.39  # Initial clauses in saturation        : 19
% 0.13/0.39  # Processed clauses                    : 169
% 0.13/0.39  # ...of these trivial                  : 2
% 0.13/0.39  # ...subsumed                          : 57
% 0.13/0.39  # ...remaining for further processing  : 110
% 0.13/0.39  # Other redundant clauses eliminated   : 15
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 0
% 0.13/0.39  # Backward-rewritten                   : 3
% 0.13/0.39  # Generated clauses                    : 557
% 0.13/0.39  # ...of the previous two non-trivial   : 525
% 0.13/0.39  # Contextual simplify-reflections      : 6
% 0.13/0.39  # Paramodulations                      : 541
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 16
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 87
% 0.13/0.39  #    Positive orientable unit clauses  : 13
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 1
% 0.13/0.39  #    Non-unit-clauses                  : 73
% 0.13/0.39  # Current number of unprocessed clauses: 391
% 0.13/0.39  # ...number of literals in the above   : 1833
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 21
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 782
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 448
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 63
% 0.13/0.39  # Unit Clause-clause subsumption calls : 18
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 4
% 0.13/0.39  # BW rewrite match successes           : 3
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 14029
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.040 s
% 0.13/0.39  # System time              : 0.006 s
% 0.13/0.39  # Total time               : 0.046 s
% 0.13/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
