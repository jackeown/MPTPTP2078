%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:38 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   37 (  66 expanded)
%              Number of clauses        :   20 (  27 expanded)
%              Number of leaves         :    8 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :  108 ( 237 expanded)
%              Number of equality atoms :   19 (  34 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   19 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(t98_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(t46_ordinal1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v3_ordinal1(k1_relat_1(X1))
       => ( v1_relat_1(X1)
          & v5_relat_1(X1,k2_relat_1(X1))
          & v1_funct_1(X1)
          & v5_ordinal1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_ordinal1)).

fof(d7_ordinal1,axiom,(
    ! [X1] :
      ( v5_ordinal1(X1)
    <=> v3_ordinal1(k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_ordinal1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(c_0_8,plain,(
    ! [X12,X13,X14] :
      ( ( k1_relat_1(X13) = X12
        | X13 != k6_relat_1(X12)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( ~ r2_hidden(X14,X12)
        | k1_funct_1(X13,X14) = X14
        | X13 != k6_relat_1(X12)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( r2_hidden(esk1_2(X12,X13),X12)
        | k1_relat_1(X13) != X12
        | X13 = k6_relat_1(X12)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( k1_funct_1(X13,esk1_2(X12,X13)) != esk1_2(X12,X13)
        | k1_relat_1(X13) != X12
        | X13 = k6_relat_1(X12)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_funct_1])])])])])).

fof(c_0_9,plain,(
    ! [X11] :
      ( v1_relat_1(k6_relat_1(X11))
      & v1_funct_1(k6_relat_1(X11)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_10,plain,(
    ! [X6] : v1_relat_1(k6_relat_1(X6)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_11,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X8)
      | r1_tarski(k1_relat_1(k7_relat_1(X8,X7)),X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

fof(c_0_12,plain,(
    ! [X9] :
      ( ~ v1_relat_1(X9)
      | k7_relat_1(X9,k1_relat_1(X9)) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).

cnf(c_0_13,plain,
    ( k1_relat_1(X1) = X2
    | X1 != k6_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( v3_ordinal1(k1_relat_1(X1))
         => ( v1_relat_1(X1)
            & v5_relat_1(X1,k2_relat_1(X1))
            & v1_funct_1(X1)
            & v5_ordinal1(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t46_ordinal1])).

cnf(c_0_17,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_13]),c_0_14]),c_0_15])])).

fof(c_0_20,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & v3_ordinal1(k1_relat_1(esk2_0))
    & ( ~ v1_relat_1(esk2_0)
      | ~ v5_relat_1(esk2_0,k2_relat_1(esk2_0))
      | ~ v1_funct_1(esk2_0)
      | ~ v5_ordinal1(esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_21,plain,(
    ! [X16] :
      ( ( ~ v5_ordinal1(X16)
        | v3_ordinal1(k1_relat_1(X16)) )
      & ( ~ v3_ordinal1(k1_relat_1(X16))
        | v5_ordinal1(X16) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_ordinal1])])).

fof(c_0_22,plain,(
    ! [X4,X5] :
      ( ( ~ v5_relat_1(X5,X4)
        | r1_tarski(k2_relat_1(X5),X4)
        | ~ v1_relat_1(X5) )
      & ( ~ r1_tarski(k2_relat_1(X5),X4)
        | v5_relat_1(X5,X4)
        | ~ v1_relat_1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_23,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_15])).

cnf(c_0_24,plain,
    ( k7_relat_1(k6_relat_1(X1),X1) = k6_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_15]),c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( ~ v1_relat_1(esk2_0)
    | ~ v5_relat_1(esk2_0,k2_relat_1(esk2_0))
    | ~ v1_funct_1(esk2_0)
    | ~ v5_ordinal1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( v5_ordinal1(X1)
    | ~ v3_ordinal1(k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( v3_ordinal1(k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( v5_relat_1(X1,X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_19])).

cnf(c_0_32,negated_conjecture,
    ( ~ v5_ordinal1(esk2_0)
    | ~ v5_relat_1(esk2_0,k2_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_33,negated_conjecture,
    ( v5_ordinal1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,plain,
    ( v5_relat_1(X1,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( ~ v5_relat_1(esk2_0,k2_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33])])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_26]),c_0_35]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:47:59 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.35  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00AA
% 0.13/0.35  # and selection function SelectLargestOrientable.
% 0.13/0.35  #
% 0.13/0.35  # Preprocessing time       : 0.018 s
% 0.13/0.35  # Presaturation interreduction done
% 0.13/0.35  
% 0.13/0.35  # Proof found!
% 0.13/0.35  # SZS status Theorem
% 0.13/0.35  # SZS output start CNFRefutation
% 0.13/0.35  fof(t34_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(X2=k6_relat_1(X1)<=>(k1_relat_1(X2)=X1&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 0.13/0.35  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.13/0.35  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.13/0.35  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 0.13/0.35  fof(t98_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 0.13/0.35  fof(t46_ordinal1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v3_ordinal1(k1_relat_1(X1))=>(((v1_relat_1(X1)&v5_relat_1(X1,k2_relat_1(X1)))&v1_funct_1(X1))&v5_ordinal1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_ordinal1)).
% 0.13/0.35  fof(d7_ordinal1, axiom, ![X1]:(v5_ordinal1(X1)<=>v3_ordinal1(k1_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_ordinal1)).
% 0.13/0.35  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.13/0.35  fof(c_0_8, plain, ![X12, X13, X14]:(((k1_relat_1(X13)=X12|X13!=k6_relat_1(X12)|(~v1_relat_1(X13)|~v1_funct_1(X13)))&(~r2_hidden(X14,X12)|k1_funct_1(X13,X14)=X14|X13!=k6_relat_1(X12)|(~v1_relat_1(X13)|~v1_funct_1(X13))))&((r2_hidden(esk1_2(X12,X13),X12)|k1_relat_1(X13)!=X12|X13=k6_relat_1(X12)|(~v1_relat_1(X13)|~v1_funct_1(X13)))&(k1_funct_1(X13,esk1_2(X12,X13))!=esk1_2(X12,X13)|k1_relat_1(X13)!=X12|X13=k6_relat_1(X12)|(~v1_relat_1(X13)|~v1_funct_1(X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_funct_1])])])])])).
% 0.13/0.35  fof(c_0_9, plain, ![X11]:(v1_relat_1(k6_relat_1(X11))&v1_funct_1(k6_relat_1(X11))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.13/0.35  fof(c_0_10, plain, ![X6]:v1_relat_1(k6_relat_1(X6)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.13/0.35  fof(c_0_11, plain, ![X7, X8]:(~v1_relat_1(X8)|r1_tarski(k1_relat_1(k7_relat_1(X8,X7)),X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 0.13/0.35  fof(c_0_12, plain, ![X9]:(~v1_relat_1(X9)|k7_relat_1(X9,k1_relat_1(X9))=X9), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).
% 0.13/0.35  cnf(c_0_13, plain, (k1_relat_1(X1)=X2|X1!=k6_relat_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.35  cnf(c_0_14, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.35  cnf(c_0_15, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.35  fof(c_0_16, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v3_ordinal1(k1_relat_1(X1))=>(((v1_relat_1(X1)&v5_relat_1(X1,k2_relat_1(X1)))&v1_funct_1(X1))&v5_ordinal1(X1))))), inference(assume_negation,[status(cth)],[t46_ordinal1])).
% 0.13/0.35  cnf(c_0_17, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.35  cnf(c_0_18, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.35  cnf(c_0_19, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_13]), c_0_14]), c_0_15])])).
% 0.13/0.35  fof(c_0_20, negated_conjecture, ((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&(v3_ordinal1(k1_relat_1(esk2_0))&(~v1_relat_1(esk2_0)|~v5_relat_1(esk2_0,k2_relat_1(esk2_0))|~v1_funct_1(esk2_0)|~v5_ordinal1(esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.13/0.35  fof(c_0_21, plain, ![X16]:((~v5_ordinal1(X16)|v3_ordinal1(k1_relat_1(X16)))&(~v3_ordinal1(k1_relat_1(X16))|v5_ordinal1(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_ordinal1])])).
% 0.13/0.35  fof(c_0_22, plain, ![X4, X5]:((~v5_relat_1(X5,X4)|r1_tarski(k2_relat_1(X5),X4)|~v1_relat_1(X5))&(~r1_tarski(k2_relat_1(X5),X4)|v5_relat_1(X5,X4)|~v1_relat_1(X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.13/0.35  cnf(c_0_23, plain, (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X2)), inference(spm,[status(thm)],[c_0_17, c_0_15])).
% 0.13/0.35  cnf(c_0_24, plain, (k7_relat_1(k6_relat_1(X1),X1)=k6_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_15]), c_0_19])).
% 0.13/0.35  cnf(c_0_25, negated_conjecture, (~v1_relat_1(esk2_0)|~v5_relat_1(esk2_0,k2_relat_1(esk2_0))|~v1_funct_1(esk2_0)|~v5_ordinal1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.35  cnf(c_0_26, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.35  cnf(c_0_27, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.35  cnf(c_0_28, plain, (v5_ordinal1(X1)|~v3_ordinal1(k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.35  cnf(c_0_29, negated_conjecture, (v3_ordinal1(k1_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.35  cnf(c_0_30, plain, (v5_relat_1(X1,X2)|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.35  cnf(c_0_31, plain, (r1_tarski(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_19])).
% 0.13/0.35  cnf(c_0_32, negated_conjecture, (~v5_ordinal1(esk2_0)|~v5_relat_1(esk2_0,k2_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26]), c_0_27])])).
% 0.13/0.35  cnf(c_0_33, negated_conjecture, (v5_ordinal1(esk2_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.35  cnf(c_0_34, plain, (v5_relat_1(X1,k2_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.35  cnf(c_0_35, negated_conjecture, (~v5_relat_1(esk2_0,k2_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33])])).
% 0.13/0.35  cnf(c_0_36, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_26]), c_0_35]), ['proof']).
% 0.13/0.35  # SZS output end CNFRefutation
% 0.13/0.35  # Proof object total steps             : 37
% 0.13/0.35  # Proof object clause steps            : 20
% 0.13/0.35  # Proof object formula steps           : 17
% 0.13/0.35  # Proof object conjectures             : 11
% 0.13/0.35  # Proof object clause conjectures      : 8
% 0.13/0.35  # Proof object formula conjectures     : 3
% 0.13/0.35  # Proof object initial clauses used    : 11
% 0.13/0.35  # Proof object initial formulas used   : 8
% 0.13/0.35  # Proof object generating inferences   : 6
% 0.13/0.35  # Proof object simplifying inferences  : 12
% 0.13/0.35  # Training examples: 0 positive, 0 negative
% 0.13/0.35  # Parsed axioms                        : 9
% 0.13/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.35  # Initial clauses                      : 20
% 0.13/0.35  # Removed in clause preprocessing      : 0
% 0.13/0.35  # Initial clauses in saturation        : 20
% 0.13/0.35  # Processed clauses                    : 57
% 0.13/0.35  # ...of these trivial                  : 2
% 0.13/0.35  # ...subsumed                          : 0
% 0.13/0.35  # ...remaining for further processing  : 55
% 0.13/0.35  # Other redundant clauses eliminated   : 4
% 0.13/0.35  # Clauses deleted for lack of memory   : 0
% 0.13/0.35  # Backward-subsumed                    : 0
% 0.13/0.35  # Backward-rewritten                   : 2
% 0.13/0.35  # Generated clauses                    : 31
% 0.13/0.35  # ...of the previous two non-trivial   : 21
% 0.13/0.35  # Contextual simplify-reflections      : 0
% 0.13/0.35  # Paramodulations                      : 27
% 0.13/0.35  # Factorizations                       : 0
% 0.13/0.35  # Equation resolutions                 : 4
% 0.13/0.35  # Propositional unsat checks           : 0
% 0.13/0.35  #    Propositional check models        : 0
% 0.13/0.35  #    Propositional check unsatisfiable : 0
% 0.13/0.35  #    Propositional clauses             : 0
% 0.13/0.35  #    Propositional clauses after purity: 0
% 0.13/0.35  #    Propositional unsat core size     : 0
% 0.13/0.35  #    Propositional preprocessing time  : 0.000
% 0.13/0.35  #    Propositional encoding time       : 0.000
% 0.13/0.35  #    Propositional solver time         : 0.000
% 0.13/0.35  #    Success case prop preproc time    : 0.000
% 0.13/0.35  #    Success case prop encoding time   : 0.000
% 0.13/0.35  #    Success case prop solver time     : 0.000
% 0.13/0.35  # Current number of processed clauses  : 31
% 0.13/0.35  #    Positive orientable unit clauses  : 16
% 0.13/0.35  #    Positive unorientable unit clauses: 0
% 0.13/0.35  #    Negative unit clauses             : 1
% 0.13/0.35  #    Non-unit-clauses                  : 14
% 0.13/0.35  # Current number of unprocessed clauses: 2
% 0.13/0.35  # ...number of literals in the above   : 4
% 0.13/0.35  # Current number of archived formulas  : 0
% 0.13/0.35  # Current number of archived clauses   : 20
% 0.13/0.35  # Clause-clause subsumption calls (NU) : 30
% 0.13/0.35  # Rec. Clause-clause subsumption calls : 17
% 0.13/0.35  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.35  # Unit Clause-clause subsumption calls : 2
% 0.13/0.35  # Rewrite failures with RHS unbound    : 0
% 0.13/0.36  # BW rewrite match attempts            : 10
% 0.13/0.36  # BW rewrite match successes           : 2
% 0.13/0.36  # Condensation attempts                : 0
% 0.13/0.36  # Condensation successes               : 0
% 0.13/0.36  # Termbank termtop insertions          : 1527
% 0.13/0.36  
% 0.13/0.36  # -------------------------------------------------
% 0.13/0.36  # User time                : 0.017 s
% 0.13/0.36  # System time              : 0.005 s
% 0.13/0.36  # Total time               : 0.022 s
% 0.13/0.36  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
