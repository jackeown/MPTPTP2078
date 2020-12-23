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
% DateTime   : Thu Dec  3 11:19:15 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   35 (  76 expanded)
%              Number of clauses        :   20 (  29 expanded)
%              Number of leaves         :    7 (  19 expanded)
%              Depth                    :    9
%              Number of atoms          :  115 ( 249 expanded)
%              Number of equality atoms :   16 (  25 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_zfmisc_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,X1)
         => v1_subset_1(k6_domain_1(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tex_2)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(t63_subset_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(d1_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( v1_zfmisc_1(X1)
      <=> ? [X2] :
            ( m1_subset_1(X2,X1)
            & X1 = k6_domain_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

fof(cc2_realset1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_zfmisc_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_realset1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v1_xboole_0(X1)
          & ~ v1_zfmisc_1(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,X1)
           => v1_subset_1(k6_domain_1(X1,X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t7_tex_2])).

fof(c_0_8,plain,(
    ! [X7,X8] :
      ( v1_xboole_0(X7)
      | ~ m1_subset_1(X8,X7)
      | k6_domain_1(X7,X8) = k1_tarski(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_9,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    & ~ v1_zfmisc_1(esk2_0)
    & m1_subset_1(esk3_0,esk2_0)
    & ~ v1_subset_1(k6_domain_1(esk2_0,esk3_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

cnf(c_0_10,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( ~ v1_subset_1(k6_domain_1(esk2_0,esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( k6_domain_1(X1,X2) = k6_domain_1(X3,X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X2,X3) ),
    inference(spm,[status(thm)],[c_0_10,c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_15,plain,(
    ! [X13,X14] :
      ( ( ~ v1_subset_1(X14,X13)
        | X14 != X13
        | ~ m1_subset_1(X14,k1_zfmisc_1(X13)) )
      & ( X14 = X13
        | v1_subset_1(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(X13)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

fof(c_0_16,plain,(
    ! [X5,X6] :
      ( ~ r2_hidden(X5,X6)
      | m1_subset_1(k1_tarski(X5),k1_zfmisc_1(X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).

fof(c_0_17,plain,(
    ! [X10,X12] :
      ( ( m1_subset_1(esk1_1(X10),X10)
        | ~ v1_zfmisc_1(X10)
        | v1_xboole_0(X10) )
      & ( X10 = k6_domain_1(X10,esk1_1(X10))
        | ~ v1_zfmisc_1(X10)
        | v1_xboole_0(X10) )
      & ( ~ m1_subset_1(X12,X10)
        | X10 != k6_domain_1(X10,X12)
        | v1_zfmisc_1(X10)
        | v1_xboole_0(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tex_2])])])])])])).

fof(c_0_18,plain,(
    ! [X9] :
      ( ~ v1_xboole_0(X9)
      | v1_zfmisc_1(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_realset1])])).

cnf(c_0_19,negated_conjecture,
    ( v1_xboole_0(X1)
    | ~ v1_subset_1(k6_domain_1(X1,esk3_0),esk2_0)
    | ~ m1_subset_1(esk3_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_20,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( v1_zfmisc_1(X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2)
    | X2 != k6_domain_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( v1_zfmisc_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( v1_xboole_0(X1)
    | ~ v1_subset_1(k1_tarski(esk3_0),esk2_0)
    | ~ m1_subset_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_10])).

cnf(c_0_25,plain,
    ( k1_tarski(X1) = X2
    | v1_subset_1(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( v1_zfmisc_1(X1)
    | k6_domain_1(X1,X2) != X1
    | ~ m1_subset_1(X2,X1) ),
    inference(csr,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( k1_tarski(esk3_0) = esk2_0
    | v1_xboole_0(X1)
    | ~ r2_hidden(esk3_0,esk2_0)
    | ~ m1_subset_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_28,plain,
    ( v1_zfmisc_1(k1_tarski(X1))
    | ~ m1_subset_1(X1,k1_tarski(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_10])]),c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( k1_tarski(esk3_0) = esk2_0
    | ~ r2_hidden(esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_13]),c_0_14])).

cnf(c_0_30,negated_conjecture,
    ( ~ v1_zfmisc_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_31,plain,(
    ! [X3,X4] :
      ( ( ~ m1_subset_1(X4,X3)
        | r2_hidden(X4,X3)
        | v1_xboole_0(X3) )
      & ( ~ r2_hidden(X4,X3)
        | m1_subset_1(X4,X3)
        | v1_xboole_0(X3) )
      & ( ~ m1_subset_1(X4,X3)
        | v1_xboole_0(X4)
        | ~ v1_xboole_0(X3) )
      & ( ~ v1_xboole_0(X4)
        | m1_subset_1(X4,X3)
        | ~ v1_xboole_0(X3) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_32,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_13])]),c_0_30])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_13])]),c_0_14]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:34:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.20/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.027 s
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(t7_tex_2, conjecture, ![X1]:((~(v1_xboole_0(X1))&~(v1_zfmisc_1(X1)))=>![X2]:(m1_subset_1(X2,X1)=>v1_subset_1(k6_domain_1(X1,X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tex_2)).
% 0.20/0.37  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.20/0.37  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 0.20/0.37  fof(t63_subset_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 0.20/0.37  fof(d1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>(v1_zfmisc_1(X1)<=>?[X2]:(m1_subset_1(X2,X1)&X1=k6_domain_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 0.20/0.37  fof(cc2_realset1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_realset1)).
% 0.20/0.37  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.20/0.37  fof(c_0_7, negated_conjecture, ~(![X1]:((~(v1_xboole_0(X1))&~(v1_zfmisc_1(X1)))=>![X2]:(m1_subset_1(X2,X1)=>v1_subset_1(k6_domain_1(X1,X2),X1)))), inference(assume_negation,[status(cth)],[t7_tex_2])).
% 0.20/0.37  fof(c_0_8, plain, ![X7, X8]:(v1_xboole_0(X7)|~m1_subset_1(X8,X7)|k6_domain_1(X7,X8)=k1_tarski(X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.20/0.37  fof(c_0_9, negated_conjecture, ((~v1_xboole_0(esk2_0)&~v1_zfmisc_1(esk2_0))&(m1_subset_1(esk3_0,esk2_0)&~v1_subset_1(k6_domain_1(esk2_0,esk3_0),esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).
% 0.20/0.37  cnf(c_0_10, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.37  cnf(c_0_11, negated_conjecture, (~v1_subset_1(k6_domain_1(esk2_0,esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  cnf(c_0_12, plain, (k6_domain_1(X1,X2)=k6_domain_1(X3,X2)|v1_xboole_0(X3)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)|~m1_subset_1(X2,X3)), inference(spm,[status(thm)],[c_0_10, c_0_10])).
% 0.20/0.37  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  cnf(c_0_14, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  fof(c_0_15, plain, ![X13, X14]:((~v1_subset_1(X14,X13)|X14!=X13|~m1_subset_1(X14,k1_zfmisc_1(X13)))&(X14=X13|v1_subset_1(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(X13)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.20/0.37  fof(c_0_16, plain, ![X5, X6]:(~r2_hidden(X5,X6)|m1_subset_1(k1_tarski(X5),k1_zfmisc_1(X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).
% 0.20/0.37  fof(c_0_17, plain, ![X10, X12]:(((m1_subset_1(esk1_1(X10),X10)|~v1_zfmisc_1(X10)|v1_xboole_0(X10))&(X10=k6_domain_1(X10,esk1_1(X10))|~v1_zfmisc_1(X10)|v1_xboole_0(X10)))&(~m1_subset_1(X12,X10)|X10!=k6_domain_1(X10,X12)|v1_zfmisc_1(X10)|v1_xboole_0(X10))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tex_2])])])])])])).
% 0.20/0.37  fof(c_0_18, plain, ![X9]:(~v1_xboole_0(X9)|v1_zfmisc_1(X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_realset1])])).
% 0.20/0.37  cnf(c_0_19, negated_conjecture, (v1_xboole_0(X1)|~v1_subset_1(k6_domain_1(X1,esk3_0),esk2_0)|~m1_subset_1(esk3_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])]), c_0_14])).
% 0.20/0.37  cnf(c_0_20, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.37  cnf(c_0_21, plain, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.37  cnf(c_0_22, plain, (v1_zfmisc_1(X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)|X2!=k6_domain_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.37  cnf(c_0_23, plain, (v1_zfmisc_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.37  cnf(c_0_24, negated_conjecture, (v1_xboole_0(X1)|~v1_subset_1(k1_tarski(esk3_0),esk2_0)|~m1_subset_1(esk3_0,X1)), inference(spm,[status(thm)],[c_0_19, c_0_10])).
% 0.20/0.37  cnf(c_0_25, plain, (k1_tarski(X1)=X2|v1_subset_1(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.37  cnf(c_0_26, plain, (v1_zfmisc_1(X1)|k6_domain_1(X1,X2)!=X1|~m1_subset_1(X2,X1)), inference(csr,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.37  cnf(c_0_27, negated_conjecture, (k1_tarski(esk3_0)=esk2_0|v1_xboole_0(X1)|~r2_hidden(esk3_0,esk2_0)|~m1_subset_1(esk3_0,X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.37  cnf(c_0_28, plain, (v1_zfmisc_1(k1_tarski(X1))|~m1_subset_1(X1,k1_tarski(X1))), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_10])]), c_0_23])).
% 0.20/0.37  cnf(c_0_29, negated_conjecture, (k1_tarski(esk3_0)=esk2_0|~r2_hidden(esk3_0,esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_13]), c_0_14])).
% 0.20/0.37  cnf(c_0_30, negated_conjecture, (~v1_zfmisc_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  fof(c_0_31, plain, ![X3, X4]:(((~m1_subset_1(X4,X3)|r2_hidden(X4,X3)|v1_xboole_0(X3))&(~r2_hidden(X4,X3)|m1_subset_1(X4,X3)|v1_xboole_0(X3)))&((~m1_subset_1(X4,X3)|v1_xboole_0(X4)|~v1_xboole_0(X3))&(~v1_xboole_0(X4)|m1_subset_1(X4,X3)|~v1_xboole_0(X3)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.20/0.37  cnf(c_0_32, negated_conjecture, (~r2_hidden(esk3_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_13])]), c_0_30])).
% 0.20/0.37  cnf(c_0_33, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.37  cnf(c_0_34, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_13])]), c_0_14]), ['proof']).
% 0.20/0.37  # SZS output end CNFRefutation
% 0.20/0.37  # Proof object total steps             : 35
% 0.20/0.37  # Proof object clause steps            : 20
% 0.20/0.37  # Proof object formula steps           : 15
% 0.20/0.37  # Proof object conjectures             : 13
% 0.20/0.37  # Proof object clause conjectures      : 10
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 10
% 0.20/0.37  # Proof object initial formulas used   : 7
% 0.20/0.37  # Proof object generating inferences   : 9
% 0.20/0.37  # Proof object simplifying inferences  : 13
% 0.20/0.37  # Training examples: 0 positive, 0 negative
% 0.20/0.37  # Parsed axioms                        : 7
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 16
% 0.20/0.37  # Removed in clause preprocessing      : 0
% 0.20/0.37  # Initial clauses in saturation        : 16
% 0.20/0.37  # Processed clauses                    : 39
% 0.20/0.37  # ...of these trivial                  : 0
% 0.20/0.37  # ...subsumed                          : 4
% 0.20/0.37  # ...remaining for further processing  : 35
% 0.20/0.37  # Other redundant clauses eliminated   : 4
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 1
% 0.20/0.37  # Backward-rewritten                   : 0
% 0.20/0.37  # Generated clauses                    : 67
% 0.20/0.37  # ...of the previous two non-trivial   : 57
% 0.20/0.37  # Contextual simplify-reflections      : 3
% 0.20/0.37  # Paramodulations                      : 63
% 0.20/0.37  # Factorizations                       : 0
% 0.20/0.37  # Equation resolutions                 : 4
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
% 0.20/0.37  # Current number of processed clauses  : 33
% 0.20/0.37  #    Positive orientable unit clauses  : 1
% 0.20/0.37  #    Positive unorientable unit clauses: 0
% 0.20/0.37  #    Negative unit clauses             : 4
% 0.20/0.37  #    Non-unit-clauses                  : 28
% 0.20/0.37  # Current number of unprocessed clauses: 34
% 0.20/0.37  # ...number of literals in the above   : 169
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 1
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 31
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 26
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 6
% 0.20/0.37  # Unit Clause-clause subsumption calls : 1
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 0
% 0.20/0.37  # BW rewrite match successes           : 0
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 1859
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.032 s
% 0.20/0.37  # System time              : 0.001 s
% 0.20/0.37  # Total time               : 0.033 s
% 0.20/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
