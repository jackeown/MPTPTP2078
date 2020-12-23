%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:55 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 807 expanded)
%              Number of clauses        :   28 ( 356 expanded)
%              Number of leaves         :    7 ( 223 expanded)
%              Depth                    :   10
%              Number of atoms          :  107 (2377 expanded)
%              Number of equality atoms :   25 ( 559 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal clause size      :   19 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

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

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(t174_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => v5_funct_1(k1_xboole_0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(s3_funct_1__e2_24__funct_1,axiom,(
    ! [X1,X2] :
    ? [X3] :
      ( v1_relat_1(X3)
      & v1_funct_1(X3)
      & k1_relat_1(X3) = X1
      & ! [X4] :
          ( r2_hidden(X4,X1)
         => k1_funct_1(X3,X4) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_7,plain,(
    ! [X10] :
      ( v1_relat_1(k6_relat_1(X10))
      & v1_funct_1(k6_relat_1(X10)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_8,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v5_funct_1(X7,X6)
        | ~ r2_hidden(X8,k1_relat_1(X7))
        | r2_hidden(k1_funct_1(X7,X8),k1_funct_1(X6,X8))
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( r2_hidden(esk1_2(X6,X7),k1_relat_1(X7))
        | v5_funct_1(X7,X6)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( ~ r2_hidden(k1_funct_1(X7,esk1_2(X6,X7)),k1_funct_1(X6,esk1_2(X6,X7)))
        | v5_funct_1(X7,X6)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_funct_1])])])])])).

cnf(c_0_9,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t81_relat_1])).

cnf(c_0_11,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => v5_funct_1(k1_xboole_0,X1) ) ),
    inference(assume_negation,[status(cth)],[t174_funct_1])).

fof(c_0_13,plain,(
    ! [X5] :
      ( ( k1_relat_1(X5) != k1_xboole_0
        | X5 = k1_xboole_0
        | ~ v1_relat_1(X5) )
      & ( k2_relat_1(X5) != k1_xboole_0
        | X5 = k1_xboole_0
        | ~ v1_relat_1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

fof(c_0_14,plain,(
    ! [X11,X12,X14] :
      ( v1_relat_1(esk2_2(X11,X12))
      & v1_funct_1(esk2_2(X11,X12))
      & k1_relat_1(esk2_2(X11,X12)) = X11
      & ( ~ r2_hidden(X14,X11)
        | k1_funct_1(esk2_2(X11,X12),X14) = X12 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).

cnf(c_0_15,plain,
    ( r2_hidden(esk1_2(X1,X2),k1_relat_1(X2))
    | v5_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_17,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_18,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_10])).

fof(c_0_19,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & ~ v5_funct_1(k1_xboole_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_20,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k1_relat_1(esk2_2(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( v1_relat_1(esk2_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( r2_hidden(esk1_2(X1,k1_xboole_0),k1_xboole_0)
    | v5_funct_1(k1_xboole_0,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( ~ v5_funct_1(k1_xboole_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( esk2_2(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_28,plain,
    ( k1_funct_1(esk2_2(X2,X3),X1) = X3
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,k1_xboole_0),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_30,plain,
    ( esk2_2(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( k1_funct_1(k1_xboole_0,esk1_2(esk3_0,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_32,negated_conjecture,
    ( X1 = X2 ),
    inference(spm,[status(thm)],[c_0_31,c_0_31])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_32])).

cnf(c_0_34,negated_conjecture,
    ( ~ v5_funct_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_32])).

cnf(c_0_35,plain,
    ( v5_funct_1(X1,X2)
    | ~ r2_hidden(k1_funct_1(X1,esk1_2(X2,X1)),k1_funct_1(X2,esk1_2(X2,X1)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_36,negated_conjecture,
    ( v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_1(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( ~ v5_funct_1(X1,X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_32])).

cnf(c_0_40,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_36])]),c_0_37]),c_0_38]),c_0_38])]),c_0_39]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:21:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S064A
% 0.20/0.37  # and selection function SelectComplexG.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.020 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.20/0.37  fof(d20_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v5_funct_1(X2,X1)<=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X3),k1_funct_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 0.20/0.37  fof(t81_relat_1, axiom, k6_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 0.20/0.37  fof(t174_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>v5_funct_1(k1_xboole_0,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_funct_1)).
% 0.20/0.37  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 0.20/0.37  fof(s3_funct_1__e2_24__funct_1, axiom, ![X1, X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&![X4]:(r2_hidden(X4,X1)=>k1_funct_1(X3,X4)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 0.20/0.37  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.20/0.37  fof(c_0_7, plain, ![X10]:(v1_relat_1(k6_relat_1(X10))&v1_funct_1(k6_relat_1(X10))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.20/0.37  fof(c_0_8, plain, ![X6, X7, X8]:((~v5_funct_1(X7,X6)|(~r2_hidden(X8,k1_relat_1(X7))|r2_hidden(k1_funct_1(X7,X8),k1_funct_1(X6,X8)))|(~v1_relat_1(X7)|~v1_funct_1(X7))|(~v1_relat_1(X6)|~v1_funct_1(X6)))&((r2_hidden(esk1_2(X6,X7),k1_relat_1(X7))|v5_funct_1(X7,X6)|(~v1_relat_1(X7)|~v1_funct_1(X7))|(~v1_relat_1(X6)|~v1_funct_1(X6)))&(~r2_hidden(k1_funct_1(X7,esk1_2(X6,X7)),k1_funct_1(X6,esk1_2(X6,X7)))|v5_funct_1(X7,X6)|(~v1_relat_1(X7)|~v1_funct_1(X7))|(~v1_relat_1(X6)|~v1_funct_1(X6))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_funct_1])])])])])).
% 0.20/0.37  cnf(c_0_9, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.37  cnf(c_0_10, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t81_relat_1])).
% 0.20/0.37  cnf(c_0_11, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.37  fof(c_0_12, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>v5_funct_1(k1_xboole_0,X1))), inference(assume_negation,[status(cth)],[t174_funct_1])).
% 0.20/0.37  fof(c_0_13, plain, ![X5]:((k1_relat_1(X5)!=k1_xboole_0|X5=k1_xboole_0|~v1_relat_1(X5))&(k2_relat_1(X5)!=k1_xboole_0|X5=k1_xboole_0|~v1_relat_1(X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.20/0.37  fof(c_0_14, plain, ![X11, X12, X14]:(((v1_relat_1(esk2_2(X11,X12))&v1_funct_1(esk2_2(X11,X12)))&k1_relat_1(esk2_2(X11,X12))=X11)&(~r2_hidden(X14,X11)|k1_funct_1(esk2_2(X11,X12),X14)=X12)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).
% 0.20/0.37  cnf(c_0_15, plain, (r2_hidden(esk1_2(X1,X2),k1_relat_1(X2))|v5_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.37  cnf(c_0_16, plain, (v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.20/0.37  cnf(c_0_17, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.20/0.37  cnf(c_0_18, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_11, c_0_10])).
% 0.20/0.37  fof(c_0_19, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&~v5_funct_1(k1_xboole_0,esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.20/0.37  cnf(c_0_20, plain, (X1=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.37  cnf(c_0_21, plain, (k1_relat_1(esk2_2(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.37  cnf(c_0_22, plain, (v1_relat_1(esk2_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.37  cnf(c_0_23, plain, (r2_hidden(esk1_2(X1,k1_xboole_0),k1_xboole_0)|v5_funct_1(k1_xboole_0,X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18])])).
% 0.20/0.37  cnf(c_0_24, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.37  cnf(c_0_25, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.37  cnf(c_0_26, negated_conjecture, (~v5_funct_1(k1_xboole_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.37  cnf(c_0_27, plain, (esk2_2(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 0.20/0.37  cnf(c_0_28, plain, (k1_funct_1(esk2_2(X2,X3),X1)=X3|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.37  cnf(c_0_29, negated_conjecture, (r2_hidden(esk1_2(esk3_0,k1_xboole_0),k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])]), c_0_26])).
% 0.20/0.37  cnf(c_0_30, plain, (esk2_2(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_27])).
% 0.20/0.37  cnf(c_0_31, negated_conjecture, (k1_funct_1(k1_xboole_0,esk1_2(esk3_0,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 0.20/0.37  cnf(c_0_32, negated_conjecture, (X1=X2), inference(spm,[status(thm)],[c_0_31, c_0_31])).
% 0.20/0.37  cnf(c_0_33, negated_conjecture, (r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_29, c_0_32])).
% 0.20/0.37  cnf(c_0_34, negated_conjecture, (~v5_funct_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_26, c_0_32])).
% 0.20/0.37  cnf(c_0_35, plain, (v5_funct_1(X1,X2)|~r2_hidden(k1_funct_1(X1,esk1_2(X2,X1)),k1_funct_1(X2,esk1_2(X2,X1)))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.37  cnf(c_0_36, negated_conjecture, (v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_25, c_0_32])).
% 0.20/0.37  cnf(c_0_37, negated_conjecture, (r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_33, c_0_32])).
% 0.20/0.37  cnf(c_0_38, negated_conjecture, (v1_funct_1(X1)), inference(spm,[status(thm)],[c_0_24, c_0_32])).
% 0.20/0.37  cnf(c_0_39, negated_conjecture, (~v5_funct_1(X1,X2)), inference(spm,[status(thm)],[c_0_34, c_0_32])).
% 0.20/0.37  cnf(c_0_40, plain, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_36])]), c_0_37]), c_0_38]), c_0_38])]), c_0_39]), ['proof']).
% 0.20/0.37  # SZS output end CNFRefutation
% 0.20/0.37  # Proof object total steps             : 41
% 0.20/0.37  # Proof object clause steps            : 28
% 0.20/0.37  # Proof object formula steps           : 13
% 0.20/0.37  # Proof object conjectures             : 15
% 0.20/0.37  # Proof object clause conjectures      : 12
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 13
% 0.20/0.37  # Proof object initial formulas used   : 7
% 0.20/0.37  # Proof object generating inferences   : 14
% 0.20/0.37  # Proof object simplifying inferences  : 17
% 0.20/0.37  # Training examples: 0 positive, 0 negative
% 0.20/0.37  # Parsed axioms                        : 7
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 17
% 0.20/0.37  # Removed in clause preprocessing      : 0
% 0.20/0.37  # Initial clauses in saturation        : 17
% 0.20/0.37  # Processed clauses                    : 60
% 0.20/0.37  # ...of these trivial                  : 4
% 0.20/0.37  # ...subsumed                          : 4
% 0.20/0.37  # ...remaining for further processing  : 51
% 0.20/0.37  # Other redundant clauses eliminated   : 0
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 10
% 0.20/0.37  # Backward-rewritten                   : 15
% 0.20/0.37  # Generated clauses                    : 81
% 0.20/0.37  # ...of the previous two non-trivial   : 82
% 0.20/0.37  # Contextual simplify-reflections      : 0
% 0.20/0.37  # Paramodulations                      : 79
% 0.20/0.37  # Factorizations                       : 0
% 0.20/0.37  # Equation resolutions                 : 1
% 0.20/0.37  # Propositional unsat checks           : 0
% 0.20/0.37  #    Propositional check models        : 0
% 0.20/0.37  #    Propositional check unsatisfiable : 0
% 0.20/0.37  #    Propositional clauses             : 0
% 0.20/0.37  #    Propositional clauses after purity: 0
% 0.20/0.37  #    Propositional unsat core size     : 0
% 0.20/0.37  #    Propositional preprocessing time  : 0.000
% 0.20/0.37  #    Propositional encoding time       : 0.000
% 0.20/0.37  #    Propositional solver time         : 0.000
% 0.20/0.37  #    Success case prop preproc time    : 0.000
% 0.20/0.37  #    Success case prop encoding time   : 0.000
% 0.20/0.37  #    Success case prop solver time     : 0.000
% 0.20/0.37  # Current number of processed clauses  : 8
% 0.20/0.37  #    Positive orientable unit clauses  : 3
% 0.20/0.37  #    Positive unorientable unit clauses: 1
% 0.20/0.37  #    Negative unit clauses             : 4
% 0.20/0.37  #    Non-unit-clauses                  : 0
% 0.20/0.37  # Current number of unprocessed clauses: 3
% 0.20/0.37  # ...number of literals in the above   : 9
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 43
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 6
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 2
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.37  # Unit Clause-clause subsumption calls : 31
% 0.20/0.37  # Rewrite failures with RHS unbound    : 132
% 0.20/0.37  # BW rewrite match attempts            : 85
% 0.20/0.37  # BW rewrite match successes           : 82
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 1747
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.023 s
% 0.20/0.37  # System time              : 0.002 s
% 0.20/0.37  # Total time               : 0.025 s
% 0.20/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
