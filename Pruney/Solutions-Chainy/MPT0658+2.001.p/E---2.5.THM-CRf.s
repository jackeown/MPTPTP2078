%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:08 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 364 expanded)
%              Number of clauses        :   27 ( 126 expanded)
%              Number of leaves         :    7 (  88 expanded)
%              Depth                    :    8
%              Number of atoms          :  137 (1207 expanded)
%              Number of equality atoms :   37 ( 271 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t65_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(k2_funct_1(X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(fc6_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v2_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1))
        & v2_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

fof(d9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(X1) = k4_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t37_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
        & k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(t63_funct_1,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

fof(t61_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
          & k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
         => k2_funct_1(k2_funct_1(X1)) = X1 ) ) ),
    inference(assume_negation,[status(cth)],[t65_funct_1])).

fof(c_0_8,plain,(
    ! [X6] :
      ( ( v1_relat_1(k2_funct_1(X6))
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6)
        | ~ v2_funct_1(X6) )
      & ( v1_funct_1(k2_funct_1(X6))
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6)
        | ~ v2_funct_1(X6) )
      & ( v2_funct_1(k2_funct_1(X6))
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6)
        | ~ v2_funct_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_funct_1])])])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & v2_funct_1(esk1_0)
    & k2_funct_1(k2_funct_1(esk1_0)) != esk1_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X4] :
      ( ~ v1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | ~ v2_funct_1(X4)
      | k2_funct_1(X4) = k4_relat_1(X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).

fof(c_0_11,plain,(
    ! [X5] :
      ( ( v1_relat_1(k2_funct_1(X5))
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) )
      & ( v1_funct_1(k2_funct_1(X5))
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_12,plain,
    ( v2_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( v2_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k2_funct_1(X1) = k4_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( v2_funct_1(k2_funct_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_20,negated_conjecture,
    ( k2_funct_1(esk1_0) = k4_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_14]),c_0_15])])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_14]),c_0_15])])).

fof(c_0_23,plain,(
    ! [X3] :
      ( ( k2_relat_1(X3) = k1_relat_1(k4_relat_1(X3))
        | ~ v1_relat_1(X3) )
      & ( k1_relat_1(X3) = k2_relat_1(k4_relat_1(X3))
        | ~ v1_relat_1(X3) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).

fof(c_0_24,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(X8)
      | ~ v1_funct_1(X8)
      | ~ v1_relat_1(X9)
      | ~ v1_funct_1(X9)
      | ~ v2_funct_1(X8)
      | k2_relat_1(X8) != k1_relat_1(X9)
      | k5_relat_1(X8,X9) != k6_relat_1(k1_relat_1(X8))
      | X9 = k2_funct_1(X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_funct_1])])])).

cnf(c_0_25,negated_conjecture,
    ( v2_funct_1(k4_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_1(k4_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(k4_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_22,c_0_20])).

cnf(c_0_28,plain,
    ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_30,plain,(
    ! [X7] :
      ( ( k5_relat_1(X7,k2_funct_1(X7)) = k6_relat_1(k1_relat_1(X7))
        | ~ v2_funct_1(X7)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( k5_relat_1(k2_funct_1(X7),X7) = k6_relat_1(k2_relat_1(X7))
        | ~ v2_funct_1(X7)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).

cnf(c_0_31,negated_conjecture,
    ( k2_funct_1(k2_funct_1(esk1_0)) != esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,plain,
    ( X2 = k2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | k2_relat_1(X1) != k1_relat_1(X2)
    | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( k2_funct_1(k4_relat_1(esk1_0)) = k4_relat_1(k4_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_25]),c_0_26]),c_0_27])])).

cnf(c_0_34,negated_conjecture,
    ( k1_relat_1(k4_relat_1(esk1_0)) = k2_relat_1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_15])).

cnf(c_0_35,negated_conjecture,
    ( k2_relat_1(k4_relat_1(esk1_0)) = k1_relat_1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_15])).

cnf(c_0_36,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( k2_funct_1(k4_relat_1(esk1_0)) != esk1_0 ),
    inference(rw,[status(thm)],[c_0_31,c_0_20])).

cnf(c_0_38,negated_conjecture,
    ( X1 = k4_relat_1(k4_relat_1(esk1_0))
    | k5_relat_1(k4_relat_1(esk1_0),X1) != k6_relat_1(k2_relat_1(esk1_0))
    | k1_relat_1(X1) != k1_relat_1(esk1_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_25]),c_0_33]),c_0_34]),c_0_35]),c_0_26]),c_0_27])])).

cnf(c_0_39,negated_conjecture,
    ( k5_relat_1(k4_relat_1(esk1_0),esk1_0) = k6_relat_1(k2_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_13]),c_0_14]),c_0_15])]),c_0_20])).

cnf(c_0_40,negated_conjecture,
    ( k4_relat_1(k4_relat_1(esk1_0)) != esk1_0 ),
    inference(rw,[status(thm)],[c_0_37,c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_14]),c_0_39]),c_0_15])]),c_0_40]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:09:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___107_C00_02_nc_F1_PI_AE_Q4_CS_SP_PS_S00EN
% 0.19/0.38  # and selection function PSelectSmallestOrientable.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.027 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t65_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>k2_funct_1(k2_funct_1(X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 0.19/0.38  fof(fc6_funct_1, axiom, ![X1]:(((v1_relat_1(X1)&v1_funct_1(X1))&v2_funct_1(X1))=>((v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))&v2_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 0.19/0.38  fof(d9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>k2_funct_1(X1)=k4_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 0.19/0.38  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.19/0.38  fof(t37_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))&k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 0.19/0.38  fof(t63_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(((v2_funct_1(X1)&k2_relat_1(X1)=k1_relat_1(X2))&k5_relat_1(X1,X2)=k6_relat_1(k1_relat_1(X1)))=>X2=k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 0.19/0.38  fof(t61_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))&k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 0.19/0.38  fof(c_0_7, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>k2_funct_1(k2_funct_1(X1))=X1))), inference(assume_negation,[status(cth)],[t65_funct_1])).
% 0.19/0.38  fof(c_0_8, plain, ![X6]:(((v1_relat_1(k2_funct_1(X6))|(~v1_relat_1(X6)|~v1_funct_1(X6)|~v2_funct_1(X6)))&(v1_funct_1(k2_funct_1(X6))|(~v1_relat_1(X6)|~v1_funct_1(X6)|~v2_funct_1(X6))))&(v2_funct_1(k2_funct_1(X6))|(~v1_relat_1(X6)|~v1_funct_1(X6)|~v2_funct_1(X6)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_funct_1])])])).
% 0.19/0.38  fof(c_0_9, negated_conjecture, ((v1_relat_1(esk1_0)&v1_funct_1(esk1_0))&(v2_funct_1(esk1_0)&k2_funct_1(k2_funct_1(esk1_0))!=esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.19/0.38  fof(c_0_10, plain, ![X4]:(~v1_relat_1(X4)|~v1_funct_1(X4)|(~v2_funct_1(X4)|k2_funct_1(X4)=k4_relat_1(X4))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).
% 0.19/0.38  fof(c_0_11, plain, ![X5]:((v1_relat_1(k2_funct_1(X5))|(~v1_relat_1(X5)|~v1_funct_1(X5)))&(v1_funct_1(k2_funct_1(X5))|(~v1_relat_1(X5)|~v1_funct_1(X5)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.19/0.38  cnf(c_0_12, plain, (v2_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.38  cnf(c_0_13, negated_conjecture, (v2_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.38  cnf(c_0_14, negated_conjecture, (v1_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.38  cnf(c_0_15, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.38  cnf(c_0_16, plain, (k2_funct_1(X1)=k4_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_17, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_18, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_19, negated_conjecture, (v2_funct_1(k2_funct_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14]), c_0_15])])).
% 0.19/0.38  cnf(c_0_20, negated_conjecture, (k2_funct_1(esk1_0)=k4_relat_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_13]), c_0_14]), c_0_15])])).
% 0.19/0.38  cnf(c_0_21, negated_conjecture, (v1_funct_1(k2_funct_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_14]), c_0_15])])).
% 0.19/0.38  cnf(c_0_22, negated_conjecture, (v1_relat_1(k2_funct_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_14]), c_0_15])])).
% 0.19/0.38  fof(c_0_23, plain, ![X3]:((k2_relat_1(X3)=k1_relat_1(k4_relat_1(X3))|~v1_relat_1(X3))&(k1_relat_1(X3)=k2_relat_1(k4_relat_1(X3))|~v1_relat_1(X3))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).
% 0.19/0.38  fof(c_0_24, plain, ![X8, X9]:(~v1_relat_1(X8)|~v1_funct_1(X8)|(~v1_relat_1(X9)|~v1_funct_1(X9)|(~v2_funct_1(X8)|k2_relat_1(X8)!=k1_relat_1(X9)|k5_relat_1(X8,X9)!=k6_relat_1(k1_relat_1(X8))|X9=k2_funct_1(X8)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_funct_1])])])).
% 0.19/0.38  cnf(c_0_25, negated_conjecture, (v2_funct_1(k4_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.38  cnf(c_0_26, negated_conjecture, (v1_funct_1(k4_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_21, c_0_20])).
% 0.19/0.38  cnf(c_0_27, negated_conjecture, (v1_relat_1(k4_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_22, c_0_20])).
% 0.19/0.38  cnf(c_0_28, plain, (k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_29, plain, (k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  fof(c_0_30, plain, ![X7]:((k5_relat_1(X7,k2_funct_1(X7))=k6_relat_1(k1_relat_1(X7))|~v2_funct_1(X7)|(~v1_relat_1(X7)|~v1_funct_1(X7)))&(k5_relat_1(k2_funct_1(X7),X7)=k6_relat_1(k2_relat_1(X7))|~v2_funct_1(X7)|(~v1_relat_1(X7)|~v1_funct_1(X7)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).
% 0.19/0.38  cnf(c_0_31, negated_conjecture, (k2_funct_1(k2_funct_1(esk1_0))!=esk1_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.38  cnf(c_0_32, plain, (X2=k2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|k2_relat_1(X1)!=k1_relat_1(X2)|k5_relat_1(X1,X2)!=k6_relat_1(k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.38  cnf(c_0_33, negated_conjecture, (k2_funct_1(k4_relat_1(esk1_0))=k4_relat_1(k4_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_25]), c_0_26]), c_0_27])])).
% 0.19/0.38  cnf(c_0_34, negated_conjecture, (k1_relat_1(k4_relat_1(esk1_0))=k2_relat_1(esk1_0)), inference(spm,[status(thm)],[c_0_28, c_0_15])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (k2_relat_1(k4_relat_1(esk1_0))=k1_relat_1(esk1_0)), inference(spm,[status(thm)],[c_0_29, c_0_15])).
% 0.19/0.38  cnf(c_0_36, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.38  cnf(c_0_37, negated_conjecture, (k2_funct_1(k4_relat_1(esk1_0))!=esk1_0), inference(rw,[status(thm)],[c_0_31, c_0_20])).
% 0.19/0.38  cnf(c_0_38, negated_conjecture, (X1=k4_relat_1(k4_relat_1(esk1_0))|k5_relat_1(k4_relat_1(esk1_0),X1)!=k6_relat_1(k2_relat_1(esk1_0))|k1_relat_1(X1)!=k1_relat_1(esk1_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_25]), c_0_33]), c_0_34]), c_0_35]), c_0_26]), c_0_27])])).
% 0.19/0.38  cnf(c_0_39, negated_conjecture, (k5_relat_1(k4_relat_1(esk1_0),esk1_0)=k6_relat_1(k2_relat_1(esk1_0))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_13]), c_0_14]), c_0_15])]), c_0_20])).
% 0.19/0.38  cnf(c_0_40, negated_conjecture, (k4_relat_1(k4_relat_1(esk1_0))!=esk1_0), inference(rw,[status(thm)],[c_0_37, c_0_33])).
% 0.19/0.38  cnf(c_0_41, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_14]), c_0_39]), c_0_15])]), c_0_40]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 42
% 0.19/0.38  # Proof object clause steps            : 27
% 0.19/0.38  # Proof object formula steps           : 15
% 0.19/0.38  # Proof object conjectures             : 22
% 0.19/0.38  # Proof object clause conjectures      : 19
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 12
% 0.19/0.38  # Proof object initial formulas used   : 7
% 0.19/0.38  # Proof object generating inferences   : 10
% 0.19/0.38  # Proof object simplifying inferences  : 32
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 7
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 15
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 15
% 0.19/0.38  # Processed clauses                    : 225
% 0.19/0.38  # ...of these trivial                  : 48
% 0.19/0.38  # ...subsumed                          : 3
% 0.19/0.38  # ...remaining for further processing  : 174
% 0.19/0.38  # Other redundant clauses eliminated   : 0
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 95
% 0.19/0.38  # Generated clauses                    : 449
% 0.19/0.38  # ...of the previous two non-trivial   : 502
% 0.19/0.38  # Contextual simplify-reflections      : 0
% 0.19/0.38  # Paramodulations                      : 449
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
% 0.19/0.38  # Current number of processed clauses  : 66
% 0.19/0.38  #    Positive orientable unit clauses  : 53
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 1
% 0.19/0.38  #    Non-unit-clauses                  : 12
% 0.19/0.38  # Current number of unprocessed clauses: 242
% 0.19/0.38  # ...number of literals in the above   : 630
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 108
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 34
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 7
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 3
% 0.19/0.38  # Unit Clause-clause subsumption calls : 2
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 254
% 0.19/0.38  # BW rewrite match successes           : 5
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 15832
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.037 s
% 0.19/0.38  # System time              : 0.005 s
% 0.19/0.38  # Total time               : 0.042 s
% 0.19/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
