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
% DateTime   : Thu Dec  3 10:54:01 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   24 (  41 expanded)
%              Number of clauses        :   13 (  15 expanded)
%              Number of leaves         :    5 (  11 expanded)
%              Depth                    :    5
%              Number of atoms          :  233 ( 305 expanded)
%              Number of equality atoms :   60 (  60 expanded)
%              Maximal formula depth    :   31 (   6 average)
%              Maximal clause size      :  130 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t53_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( ? [X2] :
            ( v1_relat_1(X2)
            & v1_funct_1(X2)
            & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X1)) )
       => v2_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).

fof(t61_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
          & k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t54_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ( X2 = k2_funct_1(X1)
            <=> ( k1_relat_1(X2) = k2_relat_1(X1)
                & ! [X3,X4] :
                    ( ( ( r2_hidden(X3,k2_relat_1(X1))
                        & X4 = k1_funct_1(X2,X3) )
                     => ( r2_hidden(X4,k1_relat_1(X1))
                        & X3 = k1_funct_1(X1,X4) ) )
                    & ( ( r2_hidden(X4,k1_relat_1(X1))
                        & X3 = k1_funct_1(X1,X4) )
                     => ( r2_hidden(X3,k2_relat_1(X1))
                        & X4 = k1_funct_1(X2,X3) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_funct_1)).

fof(t62_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => v2_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_1)).

fof(c_0_5,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(X6)
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X7)
      | ~ v1_funct_1(X7)
      | k5_relat_1(X6,X7) != k6_relat_1(k1_relat_1(X6))
      | v2_funct_1(X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t53_funct_1])])])).

fof(c_0_6,plain,(
    ! [X18] :
      ( ( k5_relat_1(X18,k2_funct_1(X18)) = k6_relat_1(k1_relat_1(X18))
        | ~ v2_funct_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( k5_relat_1(k2_funct_1(X18),X18) = k6_relat_1(k2_relat_1(X18))
        | ~ v2_funct_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).

fof(c_0_7,plain,(
    ! [X5] :
      ( ( v1_relat_1(k2_funct_1(X5))
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) )
      & ( v1_funct_1(k2_funct_1(X5))
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_8,plain,(
    ! [X8,X9,X10,X11,X12,X13] :
      ( ( k1_relat_1(X9) = k2_relat_1(X8)
        | X9 != k2_funct_1(X8)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9)
        | ~ v2_funct_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( r2_hidden(X11,k1_relat_1(X8))
        | ~ r2_hidden(X10,k2_relat_1(X8))
        | X11 != k1_funct_1(X9,X10)
        | X9 != k2_funct_1(X8)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9)
        | ~ v2_funct_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( X10 = k1_funct_1(X8,X11)
        | ~ r2_hidden(X10,k2_relat_1(X8))
        | X11 != k1_funct_1(X9,X10)
        | X9 != k2_funct_1(X8)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9)
        | ~ v2_funct_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( r2_hidden(X12,k2_relat_1(X8))
        | ~ r2_hidden(X13,k1_relat_1(X8))
        | X12 != k1_funct_1(X8,X13)
        | X9 != k2_funct_1(X8)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9)
        | ~ v2_funct_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( X13 = k1_funct_1(X9,X12)
        | ~ r2_hidden(X13,k1_relat_1(X8))
        | X12 != k1_funct_1(X8,X13)
        | X9 != k2_funct_1(X8)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9)
        | ~ v2_funct_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( r2_hidden(esk4_2(X8,X9),k1_relat_1(X8))
        | r2_hidden(esk1_2(X8,X9),k2_relat_1(X8))
        | k1_relat_1(X9) != k2_relat_1(X8)
        | X9 = k2_funct_1(X8)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9)
        | ~ v2_funct_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( esk3_2(X8,X9) = k1_funct_1(X8,esk4_2(X8,X9))
        | r2_hidden(esk1_2(X8,X9),k2_relat_1(X8))
        | k1_relat_1(X9) != k2_relat_1(X8)
        | X9 = k2_funct_1(X8)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9)
        | ~ v2_funct_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( ~ r2_hidden(esk3_2(X8,X9),k2_relat_1(X8))
        | esk4_2(X8,X9) != k1_funct_1(X9,esk3_2(X8,X9))
        | r2_hidden(esk1_2(X8,X9),k2_relat_1(X8))
        | k1_relat_1(X9) != k2_relat_1(X8)
        | X9 = k2_funct_1(X8)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9)
        | ~ v2_funct_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( r2_hidden(esk4_2(X8,X9),k1_relat_1(X8))
        | esk2_2(X8,X9) = k1_funct_1(X9,esk1_2(X8,X9))
        | k1_relat_1(X9) != k2_relat_1(X8)
        | X9 = k2_funct_1(X8)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9)
        | ~ v2_funct_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( esk3_2(X8,X9) = k1_funct_1(X8,esk4_2(X8,X9))
        | esk2_2(X8,X9) = k1_funct_1(X9,esk1_2(X8,X9))
        | k1_relat_1(X9) != k2_relat_1(X8)
        | X9 = k2_funct_1(X8)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9)
        | ~ v2_funct_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( ~ r2_hidden(esk3_2(X8,X9),k2_relat_1(X8))
        | esk4_2(X8,X9) != k1_funct_1(X9,esk3_2(X8,X9))
        | esk2_2(X8,X9) = k1_funct_1(X9,esk1_2(X8,X9))
        | k1_relat_1(X9) != k2_relat_1(X8)
        | X9 = k2_funct_1(X8)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9)
        | ~ v2_funct_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( r2_hidden(esk4_2(X8,X9),k1_relat_1(X8))
        | ~ r2_hidden(esk2_2(X8,X9),k1_relat_1(X8))
        | esk1_2(X8,X9) != k1_funct_1(X8,esk2_2(X8,X9))
        | k1_relat_1(X9) != k2_relat_1(X8)
        | X9 = k2_funct_1(X8)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9)
        | ~ v2_funct_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( esk3_2(X8,X9) = k1_funct_1(X8,esk4_2(X8,X9))
        | ~ r2_hidden(esk2_2(X8,X9),k1_relat_1(X8))
        | esk1_2(X8,X9) != k1_funct_1(X8,esk2_2(X8,X9))
        | k1_relat_1(X9) != k2_relat_1(X8)
        | X9 = k2_funct_1(X8)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9)
        | ~ v2_funct_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( ~ r2_hidden(esk3_2(X8,X9),k2_relat_1(X8))
        | esk4_2(X8,X9) != k1_funct_1(X9,esk3_2(X8,X9))
        | ~ r2_hidden(esk2_2(X8,X9),k1_relat_1(X8))
        | esk1_2(X8,X9) != k1_funct_1(X8,esk2_2(X8,X9))
        | k1_relat_1(X9) != k2_relat_1(X8)
        | X9 = k2_funct_1(X8)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9)
        | ~ v2_funct_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_funct_1])])])])])])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
         => v2_funct_1(k2_funct_1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t62_funct_1])).

cnf(c_0_10,plain,
    ( v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( k1_relat_1(X1) = k2_relat_1(X2)
    | X1 != k2_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_15,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & v1_funct_1(esk5_0)
    & v2_funct_1(esk5_0)
    & ~ v2_funct_1(k2_funct_1(esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_16,plain,
    ( v2_funct_1(k2_funct_1(X1))
    | k6_relat_1(k1_relat_1(k2_funct_1(X1))) != k6_relat_1(k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13])).

cnf(c_0_17,plain,
    ( k1_relat_1(k2_funct_1(X1)) = k2_relat_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_14]),c_0_12]),c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_funct_1(k2_funct_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( v2_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21]),c_0_22])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:14:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.028 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t53_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(?[X2]:((v1_relat_1(X2)&v1_funct_1(X2))&k5_relat_1(X1,X2)=k6_relat_1(k1_relat_1(X1)))=>v2_funct_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_funct_1)).
% 0.12/0.37  fof(t61_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))&k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 0.12/0.37  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.12/0.37  fof(t54_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(X2=k2_funct_1(X1)<=>(k1_relat_1(X2)=k2_relat_1(X1)&![X3, X4]:(((r2_hidden(X3,k2_relat_1(X1))&X4=k1_funct_1(X2,X3))=>(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4)))&((r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))=>(r2_hidden(X3,k2_relat_1(X1))&X4=k1_funct_1(X2,X3))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_funct_1)).
% 0.12/0.37  fof(t62_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>v2_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_1)).
% 0.12/0.37  fof(c_0_5, plain, ![X6, X7]:(~v1_relat_1(X6)|~v1_funct_1(X6)|(~v1_relat_1(X7)|~v1_funct_1(X7)|k5_relat_1(X6,X7)!=k6_relat_1(k1_relat_1(X6))|v2_funct_1(X6))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t53_funct_1])])])).
% 0.12/0.37  fof(c_0_6, plain, ![X18]:((k5_relat_1(X18,k2_funct_1(X18))=k6_relat_1(k1_relat_1(X18))|~v2_funct_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18)))&(k5_relat_1(k2_funct_1(X18),X18)=k6_relat_1(k2_relat_1(X18))|~v2_funct_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).
% 0.12/0.37  fof(c_0_7, plain, ![X5]:((v1_relat_1(k2_funct_1(X5))|(~v1_relat_1(X5)|~v1_funct_1(X5)))&(v1_funct_1(k2_funct_1(X5))|(~v1_relat_1(X5)|~v1_funct_1(X5)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.12/0.37  fof(c_0_8, plain, ![X8, X9, X10, X11, X12, X13]:(((k1_relat_1(X9)=k2_relat_1(X8)|X9!=k2_funct_1(X8)|(~v1_relat_1(X9)|~v1_funct_1(X9))|~v2_funct_1(X8)|(~v1_relat_1(X8)|~v1_funct_1(X8)))&(((r2_hidden(X11,k1_relat_1(X8))|(~r2_hidden(X10,k2_relat_1(X8))|X11!=k1_funct_1(X9,X10))|X9!=k2_funct_1(X8)|(~v1_relat_1(X9)|~v1_funct_1(X9))|~v2_funct_1(X8)|(~v1_relat_1(X8)|~v1_funct_1(X8)))&(X10=k1_funct_1(X8,X11)|(~r2_hidden(X10,k2_relat_1(X8))|X11!=k1_funct_1(X9,X10))|X9!=k2_funct_1(X8)|(~v1_relat_1(X9)|~v1_funct_1(X9))|~v2_funct_1(X8)|(~v1_relat_1(X8)|~v1_funct_1(X8))))&((r2_hidden(X12,k2_relat_1(X8))|(~r2_hidden(X13,k1_relat_1(X8))|X12!=k1_funct_1(X8,X13))|X9!=k2_funct_1(X8)|(~v1_relat_1(X9)|~v1_funct_1(X9))|~v2_funct_1(X8)|(~v1_relat_1(X8)|~v1_funct_1(X8)))&(X13=k1_funct_1(X9,X12)|(~r2_hidden(X13,k1_relat_1(X8))|X12!=k1_funct_1(X8,X13))|X9!=k2_funct_1(X8)|(~v1_relat_1(X9)|~v1_funct_1(X9))|~v2_funct_1(X8)|(~v1_relat_1(X8)|~v1_funct_1(X8))))))&(((((r2_hidden(esk4_2(X8,X9),k1_relat_1(X8))|r2_hidden(esk1_2(X8,X9),k2_relat_1(X8))|k1_relat_1(X9)!=k2_relat_1(X8)|X9=k2_funct_1(X8)|(~v1_relat_1(X9)|~v1_funct_1(X9))|~v2_funct_1(X8)|(~v1_relat_1(X8)|~v1_funct_1(X8)))&(esk3_2(X8,X9)=k1_funct_1(X8,esk4_2(X8,X9))|r2_hidden(esk1_2(X8,X9),k2_relat_1(X8))|k1_relat_1(X9)!=k2_relat_1(X8)|X9=k2_funct_1(X8)|(~v1_relat_1(X9)|~v1_funct_1(X9))|~v2_funct_1(X8)|(~v1_relat_1(X8)|~v1_funct_1(X8))))&(~r2_hidden(esk3_2(X8,X9),k2_relat_1(X8))|esk4_2(X8,X9)!=k1_funct_1(X9,esk3_2(X8,X9))|r2_hidden(esk1_2(X8,X9),k2_relat_1(X8))|k1_relat_1(X9)!=k2_relat_1(X8)|X9=k2_funct_1(X8)|(~v1_relat_1(X9)|~v1_funct_1(X9))|~v2_funct_1(X8)|(~v1_relat_1(X8)|~v1_funct_1(X8))))&(((r2_hidden(esk4_2(X8,X9),k1_relat_1(X8))|esk2_2(X8,X9)=k1_funct_1(X9,esk1_2(X8,X9))|k1_relat_1(X9)!=k2_relat_1(X8)|X9=k2_funct_1(X8)|(~v1_relat_1(X9)|~v1_funct_1(X9))|~v2_funct_1(X8)|(~v1_relat_1(X8)|~v1_funct_1(X8)))&(esk3_2(X8,X9)=k1_funct_1(X8,esk4_2(X8,X9))|esk2_2(X8,X9)=k1_funct_1(X9,esk1_2(X8,X9))|k1_relat_1(X9)!=k2_relat_1(X8)|X9=k2_funct_1(X8)|(~v1_relat_1(X9)|~v1_funct_1(X9))|~v2_funct_1(X8)|(~v1_relat_1(X8)|~v1_funct_1(X8))))&(~r2_hidden(esk3_2(X8,X9),k2_relat_1(X8))|esk4_2(X8,X9)!=k1_funct_1(X9,esk3_2(X8,X9))|esk2_2(X8,X9)=k1_funct_1(X9,esk1_2(X8,X9))|k1_relat_1(X9)!=k2_relat_1(X8)|X9=k2_funct_1(X8)|(~v1_relat_1(X9)|~v1_funct_1(X9))|~v2_funct_1(X8)|(~v1_relat_1(X8)|~v1_funct_1(X8)))))&(((r2_hidden(esk4_2(X8,X9),k1_relat_1(X8))|(~r2_hidden(esk2_2(X8,X9),k1_relat_1(X8))|esk1_2(X8,X9)!=k1_funct_1(X8,esk2_2(X8,X9)))|k1_relat_1(X9)!=k2_relat_1(X8)|X9=k2_funct_1(X8)|(~v1_relat_1(X9)|~v1_funct_1(X9))|~v2_funct_1(X8)|(~v1_relat_1(X8)|~v1_funct_1(X8)))&(esk3_2(X8,X9)=k1_funct_1(X8,esk4_2(X8,X9))|(~r2_hidden(esk2_2(X8,X9),k1_relat_1(X8))|esk1_2(X8,X9)!=k1_funct_1(X8,esk2_2(X8,X9)))|k1_relat_1(X9)!=k2_relat_1(X8)|X9=k2_funct_1(X8)|(~v1_relat_1(X9)|~v1_funct_1(X9))|~v2_funct_1(X8)|(~v1_relat_1(X8)|~v1_funct_1(X8))))&(~r2_hidden(esk3_2(X8,X9),k2_relat_1(X8))|esk4_2(X8,X9)!=k1_funct_1(X9,esk3_2(X8,X9))|(~r2_hidden(esk2_2(X8,X9),k1_relat_1(X8))|esk1_2(X8,X9)!=k1_funct_1(X8,esk2_2(X8,X9)))|k1_relat_1(X9)!=k2_relat_1(X8)|X9=k2_funct_1(X8)|(~v1_relat_1(X9)|~v1_funct_1(X9))|~v2_funct_1(X8)|(~v1_relat_1(X8)|~v1_funct_1(X8)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_funct_1])])])])])])).
% 0.12/0.37  fof(c_0_9, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>v2_funct_1(k2_funct_1(X1))))), inference(assume_negation,[status(cth)],[t62_funct_1])).
% 0.12/0.37  cnf(c_0_10, plain, (v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|k5_relat_1(X1,X2)!=k6_relat_1(k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  cnf(c_0_11, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_12, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_13, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_14, plain, (k1_relat_1(X1)=k2_relat_1(X2)|X1!=k2_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  fof(c_0_15, negated_conjecture, ((v1_relat_1(esk5_0)&v1_funct_1(esk5_0))&(v2_funct_1(esk5_0)&~v2_funct_1(k2_funct_1(esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.12/0.37  cnf(c_0_16, plain, (v2_funct_1(k2_funct_1(X1))|k6_relat_1(k1_relat_1(k2_funct_1(X1)))!=k6_relat_1(k2_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12]), c_0_13])).
% 0.12/0.37  cnf(c_0_17, plain, (k1_relat_1(k2_funct_1(X1))=k2_relat_1(X1)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_14]), c_0_12]), c_0_13])).
% 0.12/0.37  cnf(c_0_18, negated_conjecture, (~v2_funct_1(k2_funct_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_19, plain, (v2_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.12/0.37  cnf(c_0_20, negated_conjecture, (v2_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_21, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_22, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_23, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21]), c_0_22])]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 24
% 0.12/0.37  # Proof object clause steps            : 13
% 0.12/0.37  # Proof object formula steps           : 11
% 0.12/0.37  # Proof object conjectures             : 8
% 0.12/0.37  # Proof object clause conjectures      : 5
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 9
% 0.12/0.37  # Proof object initial formulas used   : 5
% 0.12/0.37  # Proof object generating inferences   : 3
% 0.12/0.37  # Proof object simplifying inferences  : 9
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 5
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 23
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 23
% 0.12/0.37  # Processed clauses                    : 47
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 0
% 0.12/0.37  # ...remaining for further processing  : 47
% 0.12/0.37  # Other redundant clauses eliminated   : 9
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 1
% 0.12/0.37  # Backward-rewritten                   : 0
% 0.12/0.37  # Generated clauses                    : 18
% 0.12/0.37  # ...of the previous two non-trivial   : 16
% 0.12/0.37  # Contextual simplify-reflections      : 12
% 0.12/0.37  # Paramodulations                      : 13
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 9
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 18
% 0.12/0.37  #    Positive orientable unit clauses  : 3
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 1
% 0.12/0.37  #    Non-unit-clauses                  : 14
% 0.12/0.37  # Current number of unprocessed clauses: 13
% 0.12/0.37  # ...number of literals in the above   : 114
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 24
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 494
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 23
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 13
% 0.12/0.37  # Unit Clause-clause subsumption calls : 0
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 0
% 0.12/0.37  # BW rewrite match successes           : 0
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 3280
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.029 s
% 0.12/0.37  # System time              : 0.006 s
% 0.12/0.37  # Total time               : 0.035 s
% 0.12/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
