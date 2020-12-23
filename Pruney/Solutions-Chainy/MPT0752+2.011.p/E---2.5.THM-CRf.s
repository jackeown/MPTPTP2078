%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:36 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   44 (  48 expanded)
%              Number of clauses        :   23 (  23 expanded)
%              Number of leaves         :   11 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :  106 ( 122 expanded)
%              Number of equality atoms :   20 (  20 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t45_ordinal1,conjecture,(
    ! [X1] :
      ( v1_relat_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X1)
      & v1_funct_1(k1_xboole_0)
      & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(l222_relat_1,axiom,(
    ! [X1,X2] :
      ( v4_relat_1(k1_xboole_0,X1)
      & v5_relat_1(k1_xboole_0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l222_relat_1)).

fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(rc3_ordinal1,axiom,(
    ! [X1] :
    ? [X2] :
      ( v1_relat_1(X2)
      & v5_relat_1(X2,X1)
      & v1_funct_1(X2)
      & v5_ordinal1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_ordinal1)).

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(c_0_11,plain,(
    ! [X3,X4] :
      ( ( r1_tarski(X3,X4)
        | X3 != X4 )
      & ( r1_tarski(X4,X3)
        | X3 != X4 )
      & ( ~ r1_tarski(X3,X4)
        | ~ r1_tarski(X4,X3)
        | X3 = X4 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_12,plain,(
    ! [X5] : r1_tarski(k1_xboole_0,X5) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(k1_xboole_0)
        & v5_relat_1(k1_xboole_0,X1)
        & v1_funct_1(k1_xboole_0)
        & v5_ordinal1(k1_xboole_0) ) ),
    inference(assume_negation,[status(cth)],[t45_ordinal1])).

cnf(c_0_14,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X7,X8] :
      ( ( ~ v5_relat_1(X8,X7)
        | r1_tarski(k2_relat_1(X8),X7)
        | ~ v1_relat_1(X8) )
      & ( ~ r1_tarski(k2_relat_1(X8),X7)
        | v5_relat_1(X8,X7)
        | ~ v1_relat_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_17,negated_conjecture,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,esk2_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_18,plain,(
    ! [X9,X10] :
      ( v4_relat_1(k1_xboole_0,X9)
      & v5_relat_1(k1_xboole_0,X10) ) ),
    inference(variable_rename,[status(thm)],[l222_relat_1])).

fof(c_0_19,plain,(
    ! [X6] :
      ( ~ v1_xboole_0(X6)
      | v1_relat_1(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

fof(c_0_20,plain,(
    ! [X11] :
      ( ( k1_relat_1(X11) != k1_xboole_0
        | X11 = k1_xboole_0
        | ~ v1_relat_1(X11) )
      & ( k2_relat_1(X11) != k1_xboole_0
        | X11 = k1_xboole_0
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

cnf(c_0_21,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,esk2_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( v5_relat_1(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_27,plain,(
    ! [X12] :
      ( v1_relat_1(k6_relat_1(X12))
      & v1_funct_1(k6_relat_1(X12)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

cnf(c_0_28,plain,
    ( X1 = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | ~ v5_relat_1(X1,k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_30,plain,(
    ! [X13] :
      ( v1_relat_1(esk1_1(X13))
      & v5_relat_1(esk1_1(X13),X13)
      & v1_funct_1(esk1_1(X13))
      & v5_ordinal1(esk1_1(X13)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc3_ordinal1])])).

cnf(c_0_31,negated_conjecture,
    ( ~ v5_ordinal1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24])])).

cnf(c_0_32,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t81_relat_1])).

cnf(c_0_35,plain,
    ( X1 = k1_xboole_0
    | ~ v5_relat_1(X1,k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,plain,
    ( v5_relat_1(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( v1_relat_1(esk1_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( ~ v5_ordinal1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32])])).

cnf(c_0_39,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( v5_ordinal1(esk1_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( esk1_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])])).

cnf(c_0_42,negated_conjecture,
    ( ~ v5_ordinal1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39])])).

cnf(c_0_43,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:46:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.19/0.34  # No SInE strategy applied
% 0.19/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.35  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.35  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.35  #
% 0.19/0.35  # Preprocessing time       : 0.014 s
% 0.19/0.35  # Presaturation interreduction done
% 0.19/0.35  
% 0.19/0.35  # Proof found!
% 0.19/0.35  # SZS status Theorem
% 0.19/0.35  # SZS output start CNFRefutation
% 0.19/0.35  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.35  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.35  fof(t45_ordinal1, conjecture, ![X1]:(((v1_relat_1(k1_xboole_0)&v5_relat_1(k1_xboole_0,X1))&v1_funct_1(k1_xboole_0))&v5_ordinal1(k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_ordinal1)).
% 0.19/0.35  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.19/0.35  fof(l222_relat_1, axiom, ![X1, X2]:(v4_relat_1(k1_xboole_0,X1)&v5_relat_1(k1_xboole_0,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l222_relat_1)).
% 0.19/0.35  fof(cc1_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 0.19/0.35  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 0.19/0.35  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.35  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.19/0.35  fof(rc3_ordinal1, axiom, ![X1]:?[X2]:(((v1_relat_1(X2)&v5_relat_1(X2,X1))&v1_funct_1(X2))&v5_ordinal1(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_ordinal1)).
% 0.19/0.35  fof(t81_relat_1, axiom, k6_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 0.19/0.35  fof(c_0_11, plain, ![X3, X4]:(((r1_tarski(X3,X4)|X3!=X4)&(r1_tarski(X4,X3)|X3!=X4))&(~r1_tarski(X3,X4)|~r1_tarski(X4,X3)|X3=X4)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.35  fof(c_0_12, plain, ![X5]:r1_tarski(k1_xboole_0,X5), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.35  fof(c_0_13, negated_conjecture, ~(![X1]:(((v1_relat_1(k1_xboole_0)&v5_relat_1(k1_xboole_0,X1))&v1_funct_1(k1_xboole_0))&v5_ordinal1(k1_xboole_0))), inference(assume_negation,[status(cth)],[t45_ordinal1])).
% 0.19/0.35  cnf(c_0_14, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.35  cnf(c_0_15, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.35  fof(c_0_16, plain, ![X7, X8]:((~v5_relat_1(X8,X7)|r1_tarski(k2_relat_1(X8),X7)|~v1_relat_1(X8))&(~r1_tarski(k2_relat_1(X8),X7)|v5_relat_1(X8,X7)|~v1_relat_1(X8))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.19/0.35  fof(c_0_17, negated_conjecture, (~v1_relat_1(k1_xboole_0)|~v5_relat_1(k1_xboole_0,esk2_0)|~v1_funct_1(k1_xboole_0)|~v5_ordinal1(k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.19/0.35  fof(c_0_18, plain, ![X9, X10]:(v4_relat_1(k1_xboole_0,X9)&v5_relat_1(k1_xboole_0,X10)), inference(variable_rename,[status(thm)],[l222_relat_1])).
% 0.19/0.35  fof(c_0_19, plain, ![X6]:(~v1_xboole_0(X6)|v1_relat_1(X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).
% 0.19/0.35  fof(c_0_20, plain, ![X11]:((k1_relat_1(X11)!=k1_xboole_0|X11=k1_xboole_0|~v1_relat_1(X11))&(k2_relat_1(X11)!=k1_xboole_0|X11=k1_xboole_0|~v1_relat_1(X11))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.19/0.35  cnf(c_0_21, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.35  cnf(c_0_22, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.35  cnf(c_0_23, negated_conjecture, (~v1_relat_1(k1_xboole_0)|~v5_relat_1(k1_xboole_0,esk2_0)|~v1_funct_1(k1_xboole_0)|~v5_ordinal1(k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.35  cnf(c_0_24, plain, (v5_relat_1(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.35  cnf(c_0_25, plain, (v1_relat_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.35  cnf(c_0_26, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.35  fof(c_0_27, plain, ![X12]:(v1_relat_1(k6_relat_1(X12))&v1_funct_1(k6_relat_1(X12))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.19/0.35  cnf(c_0_28, plain, (X1=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.35  cnf(c_0_29, plain, (k2_relat_1(X1)=k1_xboole_0|~v5_relat_1(X1,k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.35  fof(c_0_30, plain, ![X13]:(((v1_relat_1(esk1_1(X13))&v5_relat_1(esk1_1(X13),X13))&v1_funct_1(esk1_1(X13)))&v5_ordinal1(esk1_1(X13))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc3_ordinal1])])).
% 0.19/0.35  cnf(c_0_31, negated_conjecture, (~v5_ordinal1(k1_xboole_0)|~v1_funct_1(k1_xboole_0)|~v1_relat_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24])])).
% 0.19/0.35  cnf(c_0_32, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.35  cnf(c_0_33, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.35  cnf(c_0_34, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t81_relat_1])).
% 0.19/0.35  cnf(c_0_35, plain, (X1=k1_xboole_0|~v5_relat_1(X1,k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.35  cnf(c_0_36, plain, (v5_relat_1(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.35  cnf(c_0_37, plain, (v1_relat_1(esk1_1(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.35  cnf(c_0_38, negated_conjecture, (~v5_ordinal1(k1_xboole_0)|~v1_funct_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32])])).
% 0.19/0.35  cnf(c_0_39, plain, (v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.35  cnf(c_0_40, plain, (v5_ordinal1(esk1_1(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.35  cnf(c_0_41, plain, (esk1_1(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])])).
% 0.19/0.35  cnf(c_0_42, negated_conjecture, (~v5_ordinal1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39])])).
% 0.19/0.35  cnf(c_0_43, plain, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42]), ['proof']).
% 0.19/0.35  # SZS output end CNFRefutation
% 0.19/0.35  # Proof object total steps             : 44
% 0.19/0.35  # Proof object clause steps            : 23
% 0.19/0.35  # Proof object formula steps           : 21
% 0.19/0.35  # Proof object conjectures             : 7
% 0.19/0.35  # Proof object clause conjectures      : 4
% 0.19/0.35  # Proof object formula conjectures     : 3
% 0.19/0.35  # Proof object initial clauses used    : 13
% 0.19/0.35  # Proof object initial formulas used   : 11
% 0.19/0.35  # Proof object generating inferences   : 7
% 0.19/0.35  # Proof object simplifying inferences  : 9
% 0.19/0.35  # Training examples: 0 positive, 0 negative
% 0.19/0.35  # Parsed axioms                        : 11
% 0.19/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.35  # Initial clauses                      : 20
% 0.19/0.35  # Removed in clause preprocessing      : 0
% 0.19/0.35  # Initial clauses in saturation        : 20
% 0.19/0.35  # Processed clauses                    : 52
% 0.19/0.35  # ...of these trivial                  : 1
% 0.19/0.35  # ...subsumed                          : 0
% 0.19/0.35  # ...remaining for further processing  : 51
% 0.19/0.35  # Other redundant clauses eliminated   : 2
% 0.19/0.35  # Clauses deleted for lack of memory   : 0
% 0.19/0.35  # Backward-subsumed                    : 0
% 0.19/0.35  # Backward-rewritten                   : 3
% 0.19/0.35  # Generated clauses                    : 22
% 0.19/0.35  # ...of the previous two non-trivial   : 17
% 0.19/0.35  # Contextual simplify-reflections      : 0
% 0.19/0.35  # Paramodulations                      : 20
% 0.19/0.35  # Factorizations                       : 0
% 0.19/0.35  # Equation resolutions                 : 2
% 0.19/0.35  # Propositional unsat checks           : 0
% 0.19/0.35  #    Propositional check models        : 0
% 0.19/0.35  #    Propositional check unsatisfiable : 0
% 0.19/0.35  #    Propositional clauses             : 0
% 0.19/0.35  #    Propositional clauses after purity: 0
% 0.19/0.35  #    Propositional unsat core size     : 0
% 0.19/0.35  #    Propositional preprocessing time  : 0.000
% 0.19/0.35  #    Propositional encoding time       : 0.000
% 0.19/0.35  #    Propositional solver time         : 0.000
% 0.19/0.35  #    Success case prop preproc time    : 0.000
% 0.19/0.35  #    Success case prop encoding time   : 0.000
% 0.19/0.35  #    Success case prop solver time     : 0.000
% 0.19/0.35  # Current number of processed clauses  : 27
% 0.19/0.35  #    Positive orientable unit clauses  : 15
% 0.19/0.35  #    Positive unorientable unit clauses: 0
% 0.19/0.35  #    Negative unit clauses             : 1
% 0.19/0.35  #    Non-unit-clauses                  : 11
% 0.19/0.35  # Current number of unprocessed clauses: 4
% 0.19/0.35  # ...number of literals in the above   : 16
% 0.19/0.35  # Current number of archived formulas  : 0
% 0.19/0.35  # Current number of archived clauses   : 22
% 0.19/0.35  # Clause-clause subsumption calls (NU) : 11
% 0.19/0.35  # Rec. Clause-clause subsumption calls : 11
% 0.19/0.35  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.35  # Unit Clause-clause subsumption calls : 0
% 0.19/0.35  # Rewrite failures with RHS unbound    : 0
% 0.19/0.35  # BW rewrite match attempts            : 4
% 0.19/0.35  # BW rewrite match successes           : 3
% 0.19/0.35  # Condensation attempts                : 0
% 0.19/0.35  # Condensation successes               : 0
% 0.19/0.35  # Termbank termtop insertions          : 1166
% 0.19/0.35  
% 0.19/0.35  # -------------------------------------------------
% 0.19/0.35  # User time                : 0.014 s
% 0.19/0.35  # System time              : 0.003 s
% 0.19/0.35  # Total time               : 0.017 s
% 0.19/0.35  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
