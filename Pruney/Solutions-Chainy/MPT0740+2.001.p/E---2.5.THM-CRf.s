%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:11 EST 2020

% Result     : Theorem 4.78s
% Output     : CNFRefutation 4.78s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 309 expanded)
%              Number of clauses        :   42 ( 140 expanded)
%              Number of leaves         :    8 (  78 expanded)
%              Depth                    :   15
%              Number of atoms          :  168 (1000 expanded)
%              Number of equality atoms :   10 (  25 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

fof(t94_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X3,X2) )
     => r1_tarski(k3_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(cc1_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v1_ordinal1(X1)
        & v2_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(t30_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v3_ordinal1(k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_ordinal1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t92_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_zfmisc_1)).

fof(d3_ordinal1,axiom,(
    ! [X1] :
      ( v2_ordinal1(X1)
    <=> ! [X2,X3] :
          ~ ( r2_hidden(X2,X1)
            & r2_hidden(X3,X1)
            & ~ r2_hidden(X2,X3)
            & X2 != X3
            & ~ r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_ordinal1)).

fof(d4_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
    <=> ( v1_ordinal1(X1)
        & v2_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_ordinal1)).

fof(c_0_8,plain,(
    ! [X18,X19,X20] :
      ( ( ~ v1_ordinal1(X18)
        | ~ r2_hidden(X19,X18)
        | r1_tarski(X19,X18) )
      & ( r2_hidden(esk3_1(X20),X20)
        | v1_ordinal1(X20) )
      & ( ~ r1_tarski(esk3_1(X20),X20)
        | v1_ordinal1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).

fof(c_0_9,plain,(
    ! [X14,X15] :
      ( ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_tarski(k3_tarski(X14),X15) )
      & ( ~ r1_tarski(esk2_2(X14,X15),X15)
        | r1_tarski(k3_tarski(X14),X15) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).

cnf(c_0_10,plain,
    ( r1_tarski(X2,X1)
    | ~ v1_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(k3_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X17] :
      ( ( v1_ordinal1(X17)
        | ~ v3_ordinal1(X17) )
      & ( v2_ordinal1(X17)
        | ~ v3_ordinal1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => v3_ordinal1(k3_tarski(X1)) ) ),
    inference(assume_negation,[status(cth)],[t30_ordinal1])).

cnf(c_0_14,plain,
    ( r1_tarski(esk2_2(X1,X2),X1)
    | r1_tarski(k3_tarski(X1),X2)
    | ~ v1_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,plain,
    ( v1_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,negated_conjecture,
    ( v3_ordinal1(esk6_0)
    & ~ v3_ordinal1(k3_tarski(esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_17,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_18,plain,
    ( r1_tarski(esk2_2(X1,X2),X1)
    | r1_tarski(k3_tarski(X1),X2)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( v3_ordinal1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X12,X13] :
      ( ~ r2_hidden(X12,X13)
      | r1_tarski(X12,k3_tarski(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t92_zfmisc_1])])).

fof(c_0_21,plain,(
    ! [X22,X23,X24,X25] :
      ( ( ~ v2_ordinal1(X22)
        | ~ r2_hidden(X23,X22)
        | ~ r2_hidden(X24,X22)
        | r2_hidden(X23,X24)
        | X23 = X24
        | r2_hidden(X24,X23) )
      & ( r2_hidden(esk4_1(X25),X25)
        | v2_ordinal1(X25) )
      & ( r2_hidden(esk5_1(X25),X25)
        | v2_ordinal1(X25) )
      & ( ~ r2_hidden(esk4_1(X25),esk5_1(X25))
        | v2_ordinal1(X25) )
      & ( esk4_1(X25) != esk5_1(X25)
        | v2_ordinal1(X25) )
      & ( ~ r2_hidden(esk5_1(X25),esk4_1(X25))
        | v2_ordinal1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_ordinal1])])])])])])])).

cnf(c_0_22,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | v1_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ r1_tarski(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(esk2_2(esk6_0,X1),esk6_0)
    | r1_tarski(k3_tarski(esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( v1_ordinal1(X1)
    | ~ r1_tarski(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( r2_hidden(esk5_1(X1),X1)
    | v2_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_29,plain,(
    ! [X28] :
      ( ( v1_ordinal1(X28)
        | ~ v3_ordinal1(X28) )
      & ( v2_ordinal1(X28)
        | ~ v3_ordinal1(X28) )
      & ( ~ v1_ordinal1(X28)
        | ~ v2_ordinal1(X28)
        | v3_ordinal1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_ordinal1])])])).

cnf(c_0_30,plain,
    ( v1_ordinal1(X1)
    | r2_hidden(esk3_1(X1),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(k3_tarski(esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,plain,
    ( v1_ordinal1(k3_tarski(X1))
    | ~ r2_hidden(esk3_1(k3_tarski(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( v2_ordinal1(X1)
    | r2_hidden(esk5_1(X1),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_28])).

cnf(c_0_34,plain,
    ( v3_ordinal1(X1)
    | ~ v1_ordinal1(X1)
    | ~ v2_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( v1_ordinal1(k3_tarski(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( ~ v3_ordinal1(k3_tarski(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_37,plain,
    ( r2_hidden(esk4_1(X1),X1)
    | v2_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_38,negated_conjecture,
    ( v2_ordinal1(k3_tarski(esk6_0))
    | r2_hidden(esk5_1(k3_tarski(esk6_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( ~ v2_ordinal1(k3_tarski(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_40,plain,
    ( v2_ordinal1(X1)
    | r2_hidden(esk4_1(X1),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_37])).

cnf(c_0_41,plain,
    ( r2_hidden(X2,X3)
    | X2 = X3
    | r2_hidden(X3,X2)
    | ~ v2_ordinal1(X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk5_1(k3_tarski(esk6_0)),esk6_0) ),
    inference(sr,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( v2_ordinal1(k3_tarski(esk6_0))
    | r2_hidden(esk4_1(k3_tarski(esk6_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( X1 = esk5_1(k3_tarski(esk6_0))
    | r2_hidden(X1,esk5_1(k3_tarski(esk6_0)))
    | r2_hidden(esk5_1(k3_tarski(esk6_0)),X1)
    | ~ v2_ordinal1(esk6_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_45,plain,
    ( v2_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk4_1(k3_tarski(esk6_0)),esk6_0) ),
    inference(sr,[status(thm)],[c_0_43,c_0_39])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_48,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_49,negated_conjecture,
    ( X1 = esk5_1(k3_tarski(esk6_0))
    | r2_hidden(esk5_1(k3_tarski(esk6_0)),X1)
    | r2_hidden(X1,esk5_1(k3_tarski(esk6_0)))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_19])])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk4_1(k3_tarski(esk6_0)),X1)
    | ~ r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_46])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,plain,
    ( v2_ordinal1(X1)
    | ~ r2_hidden(esk5_1(X1),esk4_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_53,negated_conjecture,
    ( esk5_1(k3_tarski(esk6_0)) = esk4_1(k3_tarski(esk6_0))
    | r2_hidden(esk4_1(k3_tarski(esk6_0)),esk5_1(k3_tarski(esk6_0)))
    | r2_hidden(esk5_1(k3_tarski(esk6_0)),esk4_1(k3_tarski(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])])).

cnf(c_0_54,plain,
    ( v2_ordinal1(X1)
    | ~ r2_hidden(esk4_1(X1),esk5_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_55,negated_conjecture,
    ( esk5_1(k3_tarski(esk6_0)) = esk4_1(k3_tarski(esk6_0))
    | r2_hidden(esk4_1(k3_tarski(esk6_0)),esk5_1(k3_tarski(esk6_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_39])).

cnf(c_0_56,plain,
    ( v2_ordinal1(X1)
    | esk4_1(X1) != esk5_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_57,negated_conjecture,
    ( esk5_1(k3_tarski(esk6_0)) = esk4_1(k3_tarski(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_39])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_39]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:32:05 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 4.78/4.98  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 4.78/4.98  # and selection function SelectComplexExceptUniqMaxHorn.
% 4.78/4.98  #
% 4.78/4.98  # Preprocessing time       : 0.028 s
% 4.78/4.98  # Presaturation interreduction done
% 4.78/4.98  
% 4.78/4.98  # Proof found!
% 4.78/4.98  # SZS status Theorem
% 4.78/4.98  # SZS output start CNFRefutation
% 4.78/4.98  fof(d2_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)<=>![X2]:(r2_hidden(X2,X1)=>r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 4.78/4.98  fof(t94_zfmisc_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X3,X2))=>r1_tarski(k3_tarski(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 4.78/4.98  fof(cc1_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>(v1_ordinal1(X1)&v2_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_ordinal1)).
% 4.78/4.98  fof(t30_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k3_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_ordinal1)).
% 4.78/4.98  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.78/4.98  fof(t92_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_zfmisc_1)).
% 4.78/4.98  fof(d3_ordinal1, axiom, ![X1]:(v2_ordinal1(X1)<=>![X2, X3]:~(((((r2_hidden(X2,X1)&r2_hidden(X3,X1))&~(r2_hidden(X2,X3)))&X2!=X3)&~(r2_hidden(X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_ordinal1)).
% 4.78/4.98  fof(d4_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)<=>(v1_ordinal1(X1)&v2_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_ordinal1)).
% 4.78/4.98  fof(c_0_8, plain, ![X18, X19, X20]:((~v1_ordinal1(X18)|(~r2_hidden(X19,X18)|r1_tarski(X19,X18)))&((r2_hidden(esk3_1(X20),X20)|v1_ordinal1(X20))&(~r1_tarski(esk3_1(X20),X20)|v1_ordinal1(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).
% 4.78/4.98  fof(c_0_9, plain, ![X14, X15]:((r2_hidden(esk2_2(X14,X15),X14)|r1_tarski(k3_tarski(X14),X15))&(~r1_tarski(esk2_2(X14,X15),X15)|r1_tarski(k3_tarski(X14),X15))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).
% 4.78/4.98  cnf(c_0_10, plain, (r1_tarski(X2,X1)|~v1_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 4.78/4.98  cnf(c_0_11, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(k3_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 4.78/4.98  fof(c_0_12, plain, ![X17]:((v1_ordinal1(X17)|~v3_ordinal1(X17))&(v2_ordinal1(X17)|~v3_ordinal1(X17))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).
% 4.78/4.98  fof(c_0_13, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k3_tarski(X1)))), inference(assume_negation,[status(cth)],[t30_ordinal1])).
% 4.78/4.98  cnf(c_0_14, plain, (r1_tarski(esk2_2(X1,X2),X1)|r1_tarski(k3_tarski(X1),X2)|~v1_ordinal1(X1)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 4.78/4.98  cnf(c_0_15, plain, (v1_ordinal1(X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 4.78/4.98  fof(c_0_16, negated_conjecture, (v3_ordinal1(esk6_0)&~v3_ordinal1(k3_tarski(esk6_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 4.78/4.98  fof(c_0_17, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 4.78/4.98  cnf(c_0_18, plain, (r1_tarski(esk2_2(X1,X2),X1)|r1_tarski(k3_tarski(X1),X2)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 4.78/4.98  cnf(c_0_19, negated_conjecture, (v3_ordinal1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 4.78/4.98  fof(c_0_20, plain, ![X12, X13]:(~r2_hidden(X12,X13)|r1_tarski(X12,k3_tarski(X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t92_zfmisc_1])])).
% 4.78/4.98  fof(c_0_21, plain, ![X22, X23, X24, X25]:((~v2_ordinal1(X22)|(~r2_hidden(X23,X22)|~r2_hidden(X24,X22)|r2_hidden(X23,X24)|X23=X24|r2_hidden(X24,X23)))&(((((r2_hidden(esk4_1(X25),X25)|v2_ordinal1(X25))&(r2_hidden(esk5_1(X25),X25)|v2_ordinal1(X25)))&(~r2_hidden(esk4_1(X25),esk5_1(X25))|v2_ordinal1(X25)))&(esk4_1(X25)!=esk5_1(X25)|v2_ordinal1(X25)))&(~r2_hidden(esk5_1(X25),esk4_1(X25))|v2_ordinal1(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_ordinal1])])])])])])])).
% 4.78/4.98  cnf(c_0_22, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 4.78/4.98  cnf(c_0_23, plain, (r2_hidden(esk3_1(X1),X1)|v1_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 4.78/4.98  cnf(c_0_24, plain, (r1_tarski(k3_tarski(X1),X2)|~r1_tarski(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 4.78/4.98  cnf(c_0_25, negated_conjecture, (r1_tarski(esk2_2(esk6_0,X1),esk6_0)|r1_tarski(k3_tarski(esk6_0),X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 4.78/4.98  cnf(c_0_26, plain, (v1_ordinal1(X1)|~r1_tarski(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 4.78/4.98  cnf(c_0_27, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 4.78/4.98  cnf(c_0_28, plain, (r2_hidden(esk5_1(X1),X1)|v2_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.78/4.98  fof(c_0_29, plain, ![X28]:(((v1_ordinal1(X28)|~v3_ordinal1(X28))&(v2_ordinal1(X28)|~v3_ordinal1(X28)))&(~v1_ordinal1(X28)|~v2_ordinal1(X28)|v3_ordinal1(X28))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_ordinal1])])])).
% 4.78/4.98  cnf(c_0_30, plain, (v1_ordinal1(X1)|r2_hidden(esk3_1(X1),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 4.78/4.98  cnf(c_0_31, negated_conjecture, (r1_tarski(k3_tarski(esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 4.78/4.98  cnf(c_0_32, plain, (v1_ordinal1(k3_tarski(X1))|~r2_hidden(esk3_1(k3_tarski(X1)),X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 4.78/4.98  cnf(c_0_33, plain, (v2_ordinal1(X1)|r2_hidden(esk5_1(X1),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_22, c_0_28])).
% 4.78/4.98  cnf(c_0_34, plain, (v3_ordinal1(X1)|~v1_ordinal1(X1)|~v2_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 4.78/4.98  cnf(c_0_35, negated_conjecture, (v1_ordinal1(k3_tarski(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 4.78/4.98  cnf(c_0_36, negated_conjecture, (~v3_ordinal1(k3_tarski(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 4.78/4.98  cnf(c_0_37, plain, (r2_hidden(esk4_1(X1),X1)|v2_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.78/4.98  cnf(c_0_38, negated_conjecture, (v2_ordinal1(k3_tarski(esk6_0))|r2_hidden(esk5_1(k3_tarski(esk6_0)),esk6_0)), inference(spm,[status(thm)],[c_0_33, c_0_31])).
% 4.78/4.98  cnf(c_0_39, negated_conjecture, (~v2_ordinal1(k3_tarski(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 4.78/4.98  cnf(c_0_40, plain, (v2_ordinal1(X1)|r2_hidden(esk4_1(X1),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_22, c_0_37])).
% 4.78/4.98  cnf(c_0_41, plain, (r2_hidden(X2,X3)|X2=X3|r2_hidden(X3,X2)|~v2_ordinal1(X1)|~r2_hidden(X2,X1)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.78/4.98  cnf(c_0_42, negated_conjecture, (r2_hidden(esk5_1(k3_tarski(esk6_0)),esk6_0)), inference(sr,[status(thm)],[c_0_38, c_0_39])).
% 4.78/4.98  cnf(c_0_43, negated_conjecture, (v2_ordinal1(k3_tarski(esk6_0))|r2_hidden(esk4_1(k3_tarski(esk6_0)),esk6_0)), inference(spm,[status(thm)],[c_0_40, c_0_31])).
% 4.78/4.98  cnf(c_0_44, negated_conjecture, (X1=esk5_1(k3_tarski(esk6_0))|r2_hidden(X1,esk5_1(k3_tarski(esk6_0)))|r2_hidden(esk5_1(k3_tarski(esk6_0)),X1)|~v2_ordinal1(esk6_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 4.78/4.98  cnf(c_0_45, plain, (v2_ordinal1(X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 4.78/4.98  cnf(c_0_46, negated_conjecture, (r2_hidden(esk4_1(k3_tarski(esk6_0)),esk6_0)), inference(sr,[status(thm)],[c_0_43, c_0_39])).
% 4.78/4.98  cnf(c_0_47, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 4.78/4.98  cnf(c_0_48, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 4.78/4.98  cnf(c_0_49, negated_conjecture, (X1=esk5_1(k3_tarski(esk6_0))|r2_hidden(esk5_1(k3_tarski(esk6_0)),X1)|r2_hidden(X1,esk5_1(k3_tarski(esk6_0)))|~r2_hidden(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_19])])).
% 4.78/4.98  cnf(c_0_50, negated_conjecture, (r2_hidden(esk4_1(k3_tarski(esk6_0)),X1)|~r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_22, c_0_46])).
% 4.78/4.98  cnf(c_0_51, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 4.78/4.98  cnf(c_0_52, plain, (v2_ordinal1(X1)|~r2_hidden(esk5_1(X1),esk4_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.78/4.98  cnf(c_0_53, negated_conjecture, (esk5_1(k3_tarski(esk6_0))=esk4_1(k3_tarski(esk6_0))|r2_hidden(esk4_1(k3_tarski(esk6_0)),esk5_1(k3_tarski(esk6_0)))|r2_hidden(esk5_1(k3_tarski(esk6_0)),esk4_1(k3_tarski(esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])])).
% 4.78/4.98  cnf(c_0_54, plain, (v2_ordinal1(X1)|~r2_hidden(esk4_1(X1),esk5_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.78/4.98  cnf(c_0_55, negated_conjecture, (esk5_1(k3_tarski(esk6_0))=esk4_1(k3_tarski(esk6_0))|r2_hidden(esk4_1(k3_tarski(esk6_0)),esk5_1(k3_tarski(esk6_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_39])).
% 4.78/4.98  cnf(c_0_56, plain, (v2_ordinal1(X1)|esk4_1(X1)!=esk5_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.78/4.98  cnf(c_0_57, negated_conjecture, (esk5_1(k3_tarski(esk6_0))=esk4_1(k3_tarski(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_39])).
% 4.78/4.98  cnf(c_0_58, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_39]), ['proof']).
% 4.78/4.98  # SZS output end CNFRefutation
% 4.78/4.98  # Proof object total steps             : 59
% 4.78/4.98  # Proof object clause steps            : 42
% 4.78/4.98  # Proof object formula steps           : 17
% 4.78/4.98  # Proof object conjectures             : 20
% 4.78/4.98  # Proof object clause conjectures      : 17
% 4.78/4.98  # Proof object formula conjectures     : 3
% 4.78/4.98  # Proof object initial clauses used    : 20
% 4.78/4.98  # Proof object initial formulas used   : 8
% 4.78/4.98  # Proof object generating inferences   : 20
% 4.78/4.98  # Proof object simplifying inferences  : 11
% 4.78/4.98  # Training examples: 0 positive, 0 negative
% 4.78/4.98  # Parsed axioms                        : 12
% 4.78/4.98  # Removed by relevancy pruning/SinE    : 0
% 4.78/4.98  # Initial clauses                      : 29
% 4.78/4.98  # Removed in clause preprocessing      : 0
% 4.78/4.98  # Initial clauses in saturation        : 29
% 4.78/4.98  # Processed clauses                    : 10080
% 4.78/4.98  # ...of these trivial                  : 29
% 4.78/4.98  # ...subsumed                          : 4017
% 4.78/4.98  # ...remaining for further processing  : 6034
% 4.78/4.98  # Other redundant clauses eliminated   : 1
% 4.78/4.98  # Clauses deleted for lack of memory   : 0
% 4.78/4.98  # Backward-subsumed                    : 422
% 4.78/4.98  # Backward-rewritten                   : 2135
% 4.78/4.98  # Generated clauses                    : 506056
% 4.78/4.98  # ...of the previous two non-trivial   : 487516
% 4.78/4.98  # Contextual simplify-reflections      : 21
% 4.78/4.98  # Paramodulations                      : 506047
% 4.78/4.98  # Factorizations                       : 0
% 4.78/4.98  # Equation resolutions                 : 1
% 4.78/4.98  # Propositional unsat checks           : 1
% 4.78/4.98  #    Propositional check models        : 1
% 4.78/4.98  #    Propositional check unsatisfiable : 0
% 4.78/4.98  #    Propositional clauses             : 0
% 4.78/4.98  #    Propositional clauses after purity: 0
% 4.78/4.98  #    Propositional unsat core size     : 0
% 4.78/4.98  #    Propositional preprocessing time  : 0.000
% 4.78/4.98  #    Propositional encoding time       : 0.212
% 4.78/4.98  #    Propositional solver time         : 0.010
% 4.78/4.98  #    Success case prop preproc time    : 0.000
% 4.78/4.98  #    Success case prop encoding time   : 0.000
% 4.78/4.98  #    Success case prop solver time     : 0.000
% 4.78/4.98  # Current number of processed clauses  : 3441
% 4.78/4.98  #    Positive orientable unit clauses  : 56
% 4.78/4.98  #    Positive unorientable unit clauses: 0
% 4.78/4.98  #    Negative unit clauses             : 4
% 4.78/4.98  #    Non-unit-clauses                  : 3381
% 4.78/4.98  # Current number of unprocessed clauses: 475181
% 4.78/4.98  # ...number of literals in the above   : 2263448
% 4.78/4.98  # Current number of archived formulas  : 0
% 4.78/4.98  # Current number of archived clauses   : 2592
% 4.78/4.98  # Clause-clause subsumption calls (NU) : 2426566
% 4.78/4.98  # Rec. Clause-clause subsumption calls : 792821
% 4.78/4.98  # Non-unit clause-clause subsumptions  : 4000
% 4.78/4.98  # Unit Clause-clause subsumption calls : 15556
% 4.78/4.98  # Rewrite failures with RHS unbound    : 0
% 4.78/4.98  # BW rewrite match attempts            : 306
% 4.78/4.98  # BW rewrite match successes           : 14
% 4.78/4.98  # Condensation attempts                : 0
% 4.78/4.98  # Condensation successes               : 0
% 4.78/4.98  # Termbank termtop insertions          : 19642292
% 4.78/5.00  
% 4.78/5.00  # -------------------------------------------------
% 4.78/5.00  # User time                : 4.446 s
% 4.78/5.00  # System time              : 0.217 s
% 4.78/5.00  # Total time               : 4.663 s
% 4.78/5.00  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
