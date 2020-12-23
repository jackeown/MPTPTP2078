%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:15 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 142 expanded)
%              Number of clauses        :   35 (  62 expanded)
%              Number of leaves         :    8 (  34 expanded)
%              Depth                    :   17
%              Number of atoms          :  164 ( 516 expanded)
%              Number of equality atoms :   35 (  86 expanded)
%              Maximal formula depth    :   13 (   4 average)
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

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(d1_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( v1_zfmisc_1(X1)
      <=> ? [X2] :
            ( m1_subset_1(X2,X1)
            & X1 = k6_domain_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v1_xboole_0(X1)
          & ~ v1_zfmisc_1(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,X1)
           => v1_subset_1(k6_domain_1(X1,X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t7_tex_2])).

fof(c_0_9,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0)
    & ~ v1_zfmisc_1(esk4_0)
    & m1_subset_1(esk5_0,esk4_0)
    & ~ v1_subset_1(k6_domain_1(esk4_0,esk5_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

fof(c_0_10,plain,(
    ! [X26,X27] :
      ( ( ~ v1_subset_1(X27,X26)
        | X27 != X26
        | ~ m1_subset_1(X27,k1_zfmisc_1(X26)) )
      & ( X27 = X26
        | v1_subset_1(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(X26)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

fof(c_0_11,plain,(
    ! [X10,X11,X12,X13,X14,X15] :
      ( ( ~ r2_hidden(X12,X11)
        | X12 = X10
        | X11 != k1_tarski(X10) )
      & ( X13 != X10
        | r2_hidden(X13,X11)
        | X11 != k1_tarski(X10) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | esk2_2(X14,X15) != X14
        | X15 = k1_tarski(X14) )
      & ( r2_hidden(esk2_2(X14,X15),X15)
        | esk2_2(X14,X15) = X14
        | X15 = k1_tarski(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_12,negated_conjecture,
    ( ~ v1_subset_1(k6_domain_1(esk4_0,esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X19,X20] :
      ( ( ~ m1_subset_1(X19,k1_zfmisc_1(X20))
        | r1_tarski(X19,X20) )
      & ( ~ r1_tarski(X19,X20)
        | m1_subset_1(X19,k1_zfmisc_1(X20)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_15,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_17,negated_conjecture,
    ( k6_domain_1(esk4_0,esk5_0) = esk4_0
    | ~ m1_subset_1(k6_domain_1(esk4_0,esk5_0),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X21,X22] :
      ( v1_xboole_0(X21)
      | ~ m1_subset_1(X22,X21)
      | k6_domain_1(X21,X22) = k1_tarski(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_20,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( k6_domain_1(esk4_0,esk5_0) = esk4_0
    | ~ r1_tarski(k6_domain_1(esk4_0,esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( esk1_2(k1_tarski(X1),X2) = X1
    | r1_tarski(k1_tarski(X1),X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( k1_tarski(esk5_0) = esk4_0
    | ~ r1_tarski(k1_tarski(esk5_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_29,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( k1_tarski(esk5_0) = esk4_0
    | ~ r2_hidden(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_31,plain,(
    ! [X17,X18] :
      ( ( ~ m1_subset_1(X18,X17)
        | r2_hidden(X18,X17)
        | v1_xboole_0(X17) )
      & ( ~ r2_hidden(X18,X17)
        | m1_subset_1(X18,X17)
        | v1_xboole_0(X17) )
      & ( ~ m1_subset_1(X18,X17)
        | v1_xboole_0(X18)
        | ~ v1_xboole_0(X17) )
      & ( ~ v1_xboole_0(X18)
        | m1_subset_1(X18,X17)
        | ~ v1_xboole_0(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_32,negated_conjecture,
    ( X1 = esk5_0
    | ~ r2_hidden(esk5_0,esk4_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_30])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( X1 = esk5_0
    | ~ r2_hidden(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_24])]),c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( esk1_2(esk4_0,X1) = esk5_0
    | r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_21])).

cnf(c_0_36,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0)
    | r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0)
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_33]),c_0_25])).

fof(c_0_41,plain,(
    ! [X23,X25] :
      ( ( m1_subset_1(esk3_1(X23),X23)
        | ~ v1_zfmisc_1(X23)
        | v1_xboole_0(X23) )
      & ( X23 = k6_domain_1(X23,esk3_1(X23))
        | ~ v1_zfmisc_1(X23)
        | v1_xboole_0(X23) )
      & ( ~ m1_subset_1(X25,X23)
        | X23 != k6_domain_1(X23,X25)
        | v1_zfmisc_1(X23)
        | v1_xboole_0(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tex_2])])])])])])).

cnf(c_0_42,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_39])])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0)
    | r2_hidden(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_24])).

cnf(c_0_45,plain,
    ( v1_zfmisc_1(X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2)
    | X2 != k6_domain_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,plain,
    ( m1_subset_1(X1,k1_tarski(X1))
    | v1_xboole_0(k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(ef,[status(thm)],[c_0_44])).

cnf(c_0_48,plain,
    ( v1_zfmisc_1(k1_tarski(X1))
    | v1_xboole_0(k1_tarski(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_23])]),c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( k1_tarski(esk5_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_47])])).

cnf(c_0_50,negated_conjecture,
    ( ~ v1_zfmisc_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_25]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:37:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.20/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.028 s
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t7_tex_2, conjecture, ![X1]:((~(v1_xboole_0(X1))&~(v1_zfmisc_1(X1)))=>![X2]:(m1_subset_1(X2,X1)=>v1_subset_1(k6_domain_1(X1,X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tex_2)).
% 0.20/0.38  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 0.20/0.38  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.20/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.38  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.20/0.38  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.20/0.38  fof(d1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>(v1_zfmisc_1(X1)<=>?[X2]:(m1_subset_1(X2,X1)&X1=k6_domain_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 0.20/0.38  fof(c_0_8, negated_conjecture, ~(![X1]:((~(v1_xboole_0(X1))&~(v1_zfmisc_1(X1)))=>![X2]:(m1_subset_1(X2,X1)=>v1_subset_1(k6_domain_1(X1,X2),X1)))), inference(assume_negation,[status(cth)],[t7_tex_2])).
% 0.20/0.38  fof(c_0_9, negated_conjecture, ((~v1_xboole_0(esk4_0)&~v1_zfmisc_1(esk4_0))&(m1_subset_1(esk5_0,esk4_0)&~v1_subset_1(k6_domain_1(esk4_0,esk5_0),esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 0.20/0.38  fof(c_0_10, plain, ![X26, X27]:((~v1_subset_1(X27,X26)|X27!=X26|~m1_subset_1(X27,k1_zfmisc_1(X26)))&(X27=X26|v1_subset_1(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(X26)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.20/0.38  fof(c_0_11, plain, ![X10, X11, X12, X13, X14, X15]:(((~r2_hidden(X12,X11)|X12=X10|X11!=k1_tarski(X10))&(X13!=X10|r2_hidden(X13,X11)|X11!=k1_tarski(X10)))&((~r2_hidden(esk2_2(X14,X15),X15)|esk2_2(X14,X15)!=X14|X15=k1_tarski(X14))&(r2_hidden(esk2_2(X14,X15),X15)|esk2_2(X14,X15)=X14|X15=k1_tarski(X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.20/0.38  cnf(c_0_12, negated_conjecture, (~v1_subset_1(k6_domain_1(esk4_0,esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  cnf(c_0_13, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  fof(c_0_14, plain, ![X19, X20]:((~m1_subset_1(X19,k1_zfmisc_1(X20))|r1_tarski(X19,X20))&(~r1_tarski(X19,X20)|m1_subset_1(X19,k1_zfmisc_1(X20)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.38  cnf(c_0_15, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  fof(c_0_16, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.38  cnf(c_0_17, negated_conjecture, (k6_domain_1(esk4_0,esk5_0)=esk4_0|~m1_subset_1(k6_domain_1(esk4_0,esk5_0),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.20/0.38  cnf(c_0_18, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  fof(c_0_19, plain, ![X21, X22]:(v1_xboole_0(X21)|~m1_subset_1(X22,X21)|k6_domain_1(X21,X22)=k1_tarski(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.20/0.38  cnf(c_0_20, plain, (X1=X2|~r2_hidden(X1,k1_tarski(X2))), inference(er,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_21, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  cnf(c_0_22, negated_conjecture, (k6_domain_1(esk4_0,esk5_0)=esk4_0|~r1_tarski(k6_domain_1(esk4_0,esk5_0),esk4_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.38  cnf(c_0_23, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  cnf(c_0_25, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  cnf(c_0_26, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  cnf(c_0_27, plain, (esk1_2(k1_tarski(X1),X2)=X1|r1_tarski(k1_tarski(X1),X2)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.38  cnf(c_0_28, negated_conjecture, (k1_tarski(esk5_0)=esk4_0|~r1_tarski(k1_tarski(esk5_0),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])]), c_0_25])).
% 0.20/0.38  cnf(c_0_29, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.38  cnf(c_0_30, negated_conjecture, (k1_tarski(esk5_0)=esk4_0|~r2_hidden(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.38  fof(c_0_31, plain, ![X17, X18]:(((~m1_subset_1(X18,X17)|r2_hidden(X18,X17)|v1_xboole_0(X17))&(~r2_hidden(X18,X17)|m1_subset_1(X18,X17)|v1_xboole_0(X17)))&((~m1_subset_1(X18,X17)|v1_xboole_0(X18)|~v1_xboole_0(X17))&(~v1_xboole_0(X18)|m1_subset_1(X18,X17)|~v1_xboole_0(X17)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.20/0.38  cnf(c_0_32, negated_conjecture, (X1=esk5_0|~r2_hidden(esk5_0,esk4_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_20, c_0_30])).
% 0.20/0.38  cnf(c_0_33, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.38  cnf(c_0_34, negated_conjecture, (X1=esk5_0|~r2_hidden(X1,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_24])]), c_0_25])).
% 0.20/0.38  cnf(c_0_35, negated_conjecture, (esk1_2(esk4_0,X1)=esk5_0|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_34, c_0_21])).
% 0.20/0.38  cnf(c_0_36, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  cnf(c_0_37, negated_conjecture, (r2_hidden(esk5_0,esk4_0)|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_21, c_0_35])).
% 0.20/0.38  cnf(c_0_38, negated_conjecture, (r2_hidden(esk5_0,esk4_0)|r2_hidden(X1,X2)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.38  cnf(c_0_39, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_40, negated_conjecture, (r2_hidden(esk5_0,esk4_0)|r2_hidden(X1,X2)|~m1_subset_1(X1,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_33]), c_0_25])).
% 0.20/0.38  fof(c_0_41, plain, ![X23, X25]:(((m1_subset_1(esk3_1(X23),X23)|~v1_zfmisc_1(X23)|v1_xboole_0(X23))&(X23=k6_domain_1(X23,esk3_1(X23))|~v1_zfmisc_1(X23)|v1_xboole_0(X23)))&(~m1_subset_1(X25,X23)|X23!=k6_domain_1(X23,X25)|v1_zfmisc_1(X23)|v1_xboole_0(X23))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tex_2])])])])])])).
% 0.20/0.38  cnf(c_0_42, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.38  cnf(c_0_43, plain, (r2_hidden(X1,k1_tarski(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_39])])).
% 0.20/0.38  cnf(c_0_44, negated_conjecture, (r2_hidden(esk5_0,esk4_0)|r2_hidden(esk5_0,X1)), inference(spm,[status(thm)],[c_0_40, c_0_24])).
% 0.20/0.38  cnf(c_0_45, plain, (v1_zfmisc_1(X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)|X2!=k6_domain_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.38  cnf(c_0_46, plain, (m1_subset_1(X1,k1_tarski(X1))|v1_xboole_0(k1_tarski(X1))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.38  cnf(c_0_47, negated_conjecture, (r2_hidden(esk5_0,esk4_0)), inference(ef,[status(thm)],[c_0_44])).
% 0.20/0.38  cnf(c_0_48, plain, (v1_zfmisc_1(k1_tarski(X1))|v1_xboole_0(k1_tarski(X1))), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_23])]), c_0_46])).
% 0.20/0.38  cnf(c_0_49, negated_conjecture, (k1_tarski(esk5_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_47])])).
% 0.20/0.38  cnf(c_0_50, negated_conjecture, (~v1_zfmisc_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  cnf(c_0_51, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_25]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 52
% 0.20/0.38  # Proof object clause steps            : 35
% 0.20/0.38  # Proof object formula steps           : 17
% 0.20/0.38  # Proof object conjectures             : 21
% 0.20/0.38  # Proof object clause conjectures      : 18
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 15
% 0.20/0.38  # Proof object initial formulas used   : 8
% 0.20/0.38  # Proof object generating inferences   : 17
% 0.20/0.38  # Proof object simplifying inferences  : 16
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 8
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 23
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 23
% 0.20/0.38  # Processed clauses                    : 92
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 22
% 0.20/0.38  # ...remaining for further processing  : 70
% 0.20/0.38  # Other redundant clauses eliminated   : 11
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 2
% 0.20/0.38  # Backward-rewritten                   : 8
% 0.20/0.38  # Generated clauses                    : 156
% 0.20/0.38  # ...of the previous two non-trivial   : 114
% 0.20/0.38  # Contextual simplify-reflections      : 1
% 0.20/0.38  # Paramodulations                      : 140
% 0.20/0.38  # Factorizations                       : 6
% 0.20/0.38  # Equation resolutions                 : 11
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 57
% 0.20/0.38  #    Positive orientable unit clauses  : 5
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 4
% 0.20/0.38  #    Non-unit-clauses                  : 48
% 0.20/0.38  # Current number of unprocessed clauses: 35
% 0.20/0.38  # ...number of literals in the above   : 131
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 10
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 231
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 190
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 21
% 0.20/0.38  # Unit Clause-clause subsumption calls : 30
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 6
% 0.20/0.38  # BW rewrite match successes           : 2
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 3114
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.029 s
% 0.20/0.38  # System time              : 0.007 s
% 0.20/0.38  # Total time               : 0.037 s
% 0.20/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
