%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:42 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 188 expanded)
%              Number of clauses        :   28 (  64 expanded)
%              Number of leaves         :    5 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :  148 ( 956 expanded)
%              Number of equality atoms :   40 ( 185 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   23 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t53_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( ? [X2] :
            ( v1_relat_1(X2)
            & v1_funct_1(X2)
            & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X1)) )
       => v2_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).

fof(d8_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,k1_relat_1(X1))
              & r2_hidden(X3,k1_relat_1(X1))
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

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

fof(t23_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(X2))
           => k1_funct_1(k5_relat_1(X2,X3),X1) = k1_funct_1(X3,k1_funct_1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( ? [X2] :
              ( v1_relat_1(X2)
              & v1_funct_1(X2)
              & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X1)) )
         => v2_funct_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t53_funct_1])).

fof(c_0_6,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v2_funct_1(X4)
        | ~ r2_hidden(X5,k1_relat_1(X4))
        | ~ r2_hidden(X6,k1_relat_1(X4))
        | k1_funct_1(X4,X5) != k1_funct_1(X4,X6)
        | X5 = X6
        | ~ v1_relat_1(X4)
        | ~ v1_funct_1(X4) )
      & ( r2_hidden(esk1_1(X4),k1_relat_1(X4))
        | v2_funct_1(X4)
        | ~ v1_relat_1(X4)
        | ~ v1_funct_1(X4) )
      & ( r2_hidden(esk2_1(X4),k1_relat_1(X4))
        | v2_funct_1(X4)
        | ~ v1_relat_1(X4)
        | ~ v1_funct_1(X4) )
      & ( k1_funct_1(X4,esk1_1(X4)) = k1_funct_1(X4,esk2_1(X4))
        | v2_funct_1(X4)
        | ~ v1_relat_1(X4)
        | ~ v1_funct_1(X4) )
      & ( esk1_1(X4) != esk2_1(X4)
        | v2_funct_1(X4)
        | ~ v1_relat_1(X4)
        | ~ v1_funct_1(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & v1_funct_1(esk4_0)
    & v1_relat_1(esk5_0)
    & v1_funct_1(esk5_0)
    & k5_relat_1(esk4_0,esk5_0) = k6_relat_1(k1_relat_1(esk4_0))
    & ~ v2_funct_1(esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X14,X15,X16] :
      ( ( k1_relat_1(X15) = X14
        | X15 != k6_relat_1(X14)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( ~ r2_hidden(X16,X14)
        | k1_funct_1(X15,X16) = X16
        | X15 != k6_relat_1(X14)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( r2_hidden(esk3_2(X14,X15),X14)
        | k1_relat_1(X15) != X14
        | X15 = k6_relat_1(X14)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( k1_funct_1(X15,esk3_2(X14,X15)) != esk3_2(X14,X15)
        | k1_relat_1(X15) != X14
        | X15 = k6_relat_1(X14)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_funct_1])])])])])).

cnf(c_0_9,plain,
    ( r2_hidden(esk1_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( ~ v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_13,plain,(
    ! [X9] :
      ( v1_relat_1(k6_relat_1(X9))
      & v1_funct_1(k6_relat_1(X9)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

cnf(c_0_14,plain,
    ( r2_hidden(esk2_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_15,plain,(
    ! [X11,X12,X13] :
      ( ~ v1_relat_1(X12)
      | ~ v1_funct_1(X12)
      | ~ v1_relat_1(X13)
      | ~ v1_funct_1(X13)
      | ~ r2_hidden(X11,k1_relat_1(X12))
      | k1_funct_1(k5_relat_1(X12,X13),X11) = k1_funct_1(X13,k1_funct_1(X12,X11)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_1])])])).

cnf(c_0_16,plain,
    ( k1_funct_1(X3,X1) = X1
    | ~ r2_hidden(X1,X2)
    | X3 != k6_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk1_1(esk4_0),k1_relat_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])]),c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( k5_relat_1(esk4_0,esk5_0) = k6_relat_1(k1_relat_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k1_funct_1(X1,esk1_1(X1)) = k1_funct_1(X1,esk2_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk2_1(esk4_0),k1_relat_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_10]),c_0_11])]),c_0_12])).

cnf(c_0_23,plain,
    ( k1_funct_1(k5_relat_1(X1,X2),X3) = k1_funct_1(X2,k1_funct_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( k1_funct_1(X1,esk1_1(esk4_0)) = esk1_1(esk4_0)
    | X1 != k5_relat_1(esk4_0,esk5_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_1(k5_relat_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(k5_relat_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( k1_funct_1(esk4_0,esk2_1(esk4_0)) = k1_funct_1(esk4_0,esk1_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_10]),c_0_11])]),c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( k1_funct_1(X1,esk2_1(esk4_0)) = esk2_1(esk4_0)
    | X1 != k5_relat_1(esk4_0,esk5_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_22]),c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk4_0,X1),esk1_1(esk4_0)) = k1_funct_1(X1,k1_funct_1(esk4_0,esk1_1(esk4_0)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_17]),c_0_10]),c_0_11])])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_31,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk4_0,esk5_0),esk1_1(esk4_0)) = esk1_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_32,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_33,plain,
    ( v2_funct_1(X1)
    | esk1_1(X1) != esk2_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_34,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk4_0,X1),esk2_1(esk4_0)) = k1_funct_1(X1,k1_funct_1(esk4_0,esk1_1(esk4_0)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_22]),c_0_10]),c_0_11])]),c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk4_0,esk5_0),esk2_1(esk4_0)) = esk2_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_28]),c_0_25]),c_0_26])])).

cnf(c_0_36,negated_conjecture,
    ( k1_funct_1(esk5_0,k1_funct_1(esk4_0,esk1_1(esk4_0))) = esk1_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32])])).

cnf(c_0_37,negated_conjecture,
    ( esk2_1(esk4_0) != esk1_1(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_10]),c_0_11])]),c_0_12])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_30]),c_0_35]),c_0_36]),c_0_32])]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:47:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S064A
% 0.14/0.39  # and selection function SelectComplexG.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.042 s
% 0.14/0.39  # Presaturation interreduction done
% 0.14/0.39  
% 0.14/0.39  # Proof found!
% 0.14/0.39  # SZS status Theorem
% 0.14/0.39  # SZS output start CNFRefutation
% 0.14/0.39  fof(t53_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(?[X2]:((v1_relat_1(X2)&v1_funct_1(X2))&k5_relat_1(X1,X2)=k6_relat_1(k1_relat_1(X1)))=>v2_funct_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_funct_1)).
% 0.14/0.39  fof(d8_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)<=>![X2, X3]:(((r2_hidden(X2,k1_relat_1(X1))&r2_hidden(X3,k1_relat_1(X1)))&k1_funct_1(X1,X2)=k1_funct_1(X1,X3))=>X2=X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 0.14/0.39  fof(t34_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(X2=k6_relat_1(X1)<=>(k1_relat_1(X2)=X1&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 0.14/0.39  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.14/0.39  fof(t23_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(X2))=>k1_funct_1(k5_relat_1(X2,X3),X1)=k1_funct_1(X3,k1_funct_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 0.14/0.39  fof(c_0_5, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(?[X2]:((v1_relat_1(X2)&v1_funct_1(X2))&k5_relat_1(X1,X2)=k6_relat_1(k1_relat_1(X1)))=>v2_funct_1(X1)))), inference(assume_negation,[status(cth)],[t53_funct_1])).
% 0.14/0.39  fof(c_0_6, plain, ![X4, X5, X6]:((~v2_funct_1(X4)|(~r2_hidden(X5,k1_relat_1(X4))|~r2_hidden(X6,k1_relat_1(X4))|k1_funct_1(X4,X5)!=k1_funct_1(X4,X6)|X5=X6)|(~v1_relat_1(X4)|~v1_funct_1(X4)))&((((r2_hidden(esk1_1(X4),k1_relat_1(X4))|v2_funct_1(X4)|(~v1_relat_1(X4)|~v1_funct_1(X4)))&(r2_hidden(esk2_1(X4),k1_relat_1(X4))|v2_funct_1(X4)|(~v1_relat_1(X4)|~v1_funct_1(X4))))&(k1_funct_1(X4,esk1_1(X4))=k1_funct_1(X4,esk2_1(X4))|v2_funct_1(X4)|(~v1_relat_1(X4)|~v1_funct_1(X4))))&(esk1_1(X4)!=esk2_1(X4)|v2_funct_1(X4)|(~v1_relat_1(X4)|~v1_funct_1(X4))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).
% 0.14/0.39  fof(c_0_7, negated_conjecture, ((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&(((v1_relat_1(esk5_0)&v1_funct_1(esk5_0))&k5_relat_1(esk4_0,esk5_0)=k6_relat_1(k1_relat_1(esk4_0)))&~v2_funct_1(esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.14/0.39  fof(c_0_8, plain, ![X14, X15, X16]:(((k1_relat_1(X15)=X14|X15!=k6_relat_1(X14)|(~v1_relat_1(X15)|~v1_funct_1(X15)))&(~r2_hidden(X16,X14)|k1_funct_1(X15,X16)=X16|X15!=k6_relat_1(X14)|(~v1_relat_1(X15)|~v1_funct_1(X15))))&((r2_hidden(esk3_2(X14,X15),X14)|k1_relat_1(X15)!=X14|X15=k6_relat_1(X14)|(~v1_relat_1(X15)|~v1_funct_1(X15)))&(k1_funct_1(X15,esk3_2(X14,X15))!=esk3_2(X14,X15)|k1_relat_1(X15)!=X14|X15=k6_relat_1(X14)|(~v1_relat_1(X15)|~v1_funct_1(X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_funct_1])])])])])).
% 0.14/0.39  cnf(c_0_9, plain, (r2_hidden(esk1_1(X1),k1_relat_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.39  cnf(c_0_10, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.39  cnf(c_0_11, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.39  cnf(c_0_12, negated_conjecture, (~v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.39  fof(c_0_13, plain, ![X9]:(v1_relat_1(k6_relat_1(X9))&v1_funct_1(k6_relat_1(X9))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.14/0.39  cnf(c_0_14, plain, (r2_hidden(esk2_1(X1),k1_relat_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.39  fof(c_0_15, plain, ![X11, X12, X13]:(~v1_relat_1(X12)|~v1_funct_1(X12)|(~v1_relat_1(X13)|~v1_funct_1(X13)|(~r2_hidden(X11,k1_relat_1(X12))|k1_funct_1(k5_relat_1(X12,X13),X11)=k1_funct_1(X13,k1_funct_1(X12,X11))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_1])])])).
% 0.14/0.39  cnf(c_0_16, plain, (k1_funct_1(X3,X1)=X1|~r2_hidden(X1,X2)|X3!=k6_relat_1(X2)|~v1_relat_1(X3)|~v1_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.39  cnf(c_0_17, negated_conjecture, (r2_hidden(esk1_1(esk4_0),k1_relat_1(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11])]), c_0_12])).
% 0.14/0.39  cnf(c_0_18, negated_conjecture, (k5_relat_1(esk4_0,esk5_0)=k6_relat_1(k1_relat_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.39  cnf(c_0_19, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.39  cnf(c_0_20, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.39  cnf(c_0_21, plain, (k1_funct_1(X1,esk1_1(X1))=k1_funct_1(X1,esk2_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.39  cnf(c_0_22, negated_conjecture, (r2_hidden(esk2_1(esk4_0),k1_relat_1(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_10]), c_0_11])]), c_0_12])).
% 0.14/0.39  cnf(c_0_23, plain, (k1_funct_1(k5_relat_1(X1,X2),X3)=k1_funct_1(X2,k1_funct_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.39  cnf(c_0_24, negated_conjecture, (k1_funct_1(X1,esk1_1(esk4_0))=esk1_1(esk4_0)|X1!=k5_relat_1(esk4_0,esk5_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])).
% 0.14/0.39  cnf(c_0_25, negated_conjecture, (v1_funct_1(k5_relat_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_19, c_0_18])).
% 0.14/0.39  cnf(c_0_26, negated_conjecture, (v1_relat_1(k5_relat_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_20, c_0_18])).
% 0.14/0.39  cnf(c_0_27, negated_conjecture, (k1_funct_1(esk4_0,esk2_1(esk4_0))=k1_funct_1(esk4_0,esk1_1(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_10]), c_0_11])]), c_0_12])).
% 0.14/0.39  cnf(c_0_28, negated_conjecture, (k1_funct_1(X1,esk2_1(esk4_0))=esk2_1(esk4_0)|X1!=k5_relat_1(esk4_0,esk5_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_22]), c_0_18])).
% 0.14/0.39  cnf(c_0_29, negated_conjecture, (k1_funct_1(k5_relat_1(esk4_0,X1),esk1_1(esk4_0))=k1_funct_1(X1,k1_funct_1(esk4_0,esk1_1(esk4_0)))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_17]), c_0_10]), c_0_11])])).
% 0.14/0.39  cnf(c_0_30, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.39  cnf(c_0_31, negated_conjecture, (k1_funct_1(k5_relat_1(esk4_0,esk5_0),esk1_1(esk4_0))=esk1_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_24]), c_0_25]), c_0_26])])).
% 0.14/0.39  cnf(c_0_32, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.39  cnf(c_0_33, plain, (v2_funct_1(X1)|esk1_1(X1)!=esk2_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.39  cnf(c_0_34, negated_conjecture, (k1_funct_1(k5_relat_1(esk4_0,X1),esk2_1(esk4_0))=k1_funct_1(X1,k1_funct_1(esk4_0,esk1_1(esk4_0)))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_22]), c_0_10]), c_0_11])]), c_0_27])).
% 0.14/0.39  cnf(c_0_35, negated_conjecture, (k1_funct_1(k5_relat_1(esk4_0,esk5_0),esk2_1(esk4_0))=esk2_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_28]), c_0_25]), c_0_26])])).
% 0.14/0.39  cnf(c_0_36, negated_conjecture, (k1_funct_1(esk5_0,k1_funct_1(esk4_0,esk1_1(esk4_0)))=esk1_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32])])).
% 0.14/0.39  cnf(c_0_37, negated_conjecture, (esk2_1(esk4_0)!=esk1_1(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_10]), c_0_11])]), c_0_12])).
% 0.14/0.39  cnf(c_0_38, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_30]), c_0_35]), c_0_36]), c_0_32])]), c_0_37]), ['proof']).
% 0.14/0.39  # SZS output end CNFRefutation
% 0.14/0.39  # Proof object total steps             : 39
% 0.14/0.39  # Proof object clause steps            : 28
% 0.14/0.39  # Proof object formula steps           : 11
% 0.14/0.39  # Proof object conjectures             : 23
% 0.14/0.39  # Proof object clause conjectures      : 20
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 14
% 0.14/0.39  # Proof object initial formulas used   : 5
% 0.14/0.39  # Proof object generating inferences   : 14
% 0.14/0.39  # Proof object simplifying inferences  : 35
% 0.14/0.39  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 6
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 20
% 0.14/0.39  # Removed in clause preprocessing      : 0
% 0.14/0.39  # Initial clauses in saturation        : 20
% 0.14/0.39  # Processed clauses                    : 79
% 0.14/0.39  # ...of these trivial                  : 3
% 0.14/0.39  # ...subsumed                          : 0
% 0.14/0.39  # ...remaining for further processing  : 76
% 0.14/0.39  # Other redundant clauses eliminated   : 1
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 0
% 0.14/0.39  # Backward-rewritten                   : 1
% 0.14/0.39  # Generated clauses                    : 83
% 0.14/0.39  # ...of the previous two non-trivial   : 62
% 0.14/0.39  # Contextual simplify-reflections      : 0
% 0.14/0.39  # Paramodulations                      : 76
% 0.14/0.39  # Factorizations                       : 0
% 0.14/0.39  # Equation resolutions                 : 7
% 0.14/0.39  # Propositional unsat checks           : 0
% 0.14/0.39  #    Propositional check models        : 0
% 0.14/0.39  #    Propositional check unsatisfiable : 0
% 0.14/0.39  #    Propositional clauses             : 0
% 0.14/0.39  #    Propositional clauses after purity: 0
% 0.14/0.39  #    Propositional unsat core size     : 0
% 0.14/0.39  #    Propositional preprocessing time  : 0.000
% 0.14/0.39  #    Propositional encoding time       : 0.000
% 0.14/0.39  #    Propositional solver time         : 0.000
% 0.14/0.39  #    Success case prop preproc time    : 0.000
% 0.14/0.39  #    Success case prop encoding time   : 0.000
% 0.14/0.39  #    Success case prop solver time     : 0.000
% 0.14/0.39  # Current number of processed clauses  : 56
% 0.14/0.39  #    Positive orientable unit clauses  : 27
% 0.14/0.39  #    Positive unorientable unit clauses: 0
% 0.14/0.39  #    Negative unit clauses             : 2
% 0.14/0.39  #    Non-unit-clauses                  : 27
% 0.14/0.39  # Current number of unprocessed clauses: 20
% 0.14/0.39  # ...number of literals in the above   : 59
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 20
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 53
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 15
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.39  # Unit Clause-clause subsumption calls : 11
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 1
% 0.14/0.39  # BW rewrite match successes           : 1
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 3059
% 0.14/0.40  
% 0.14/0.40  # -------------------------------------------------
% 0.14/0.40  # User time                : 0.047 s
% 0.14/0.40  # System time              : 0.006 s
% 0.14/0.40  # Total time               : 0.053 s
% 0.14/0.40  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
