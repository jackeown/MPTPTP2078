%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:59 EST 2020

% Result     : Theorem 0.07s
% Output     : CNFRefutation 0.07s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 101 expanded)
%              Number of clauses        :   27 (  40 expanded)
%              Number of leaves         :    9 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :  121 ( 295 expanded)
%              Number of equality atoms :   22 (  29 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t6_tex_2,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,X1)
         => ~ ( v1_subset_1(k6_domain_1(X1,X2),X1)
              & v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(rc3_subset_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
      & ~ v1_subset_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

fof(cc2_subset_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => ( ~ v1_subset_1(X2,X1)
           => ~ v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_subset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t1_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_zfmisc_1(X2) )
         => ( r1_tarski(X1,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,X1)
           => ~ ( v1_subset_1(k6_domain_1(X1,X2),X1)
                & v1_zfmisc_1(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t6_tex_2])).

fof(c_0_10,plain,(
    ! [X23,X24] :
      ( v1_xboole_0(X23)
      | ~ m1_subset_1(X24,X23)
      | k6_domain_1(X23,X24) = k1_tarski(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_11,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0)
    & m1_subset_1(esk5_0,esk4_0)
    & v1_subset_1(k6_domain_1(esk4_0,esk5_0),esk4_0)
    & v1_zfmisc_1(esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
    ! [X8,X9,X10,X11,X12,X13] :
      ( ( ~ r2_hidden(X10,X9)
        | X10 = X8
        | X9 != k1_tarski(X8) )
      & ( X11 != X8
        | r2_hidden(X11,X9)
        | X9 != k1_tarski(X8) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | esk2_2(X12,X13) != X12
        | X13 = k1_tarski(X12) )
      & ( r2_hidden(esk2_2(X12,X13),X13)
        | esk2_2(X12,X13) = X12
        | X13 = k1_tarski(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_13,plain,(
    ! [X21,X22] :
      ( v1_xboole_0(X21)
      | ~ m1_subset_1(X22,X21)
      | m1_subset_1(k6_domain_1(X21,X22),k1_zfmisc_1(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

cnf(c_0_14,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X19,X20] :
      ( ( ~ m1_subset_1(X19,k1_zfmisc_1(X20))
        | r1_tarski(X19,X20) )
      & ( ~ r1_tarski(X19,X20)
        | m1_subset_1(X19,k1_zfmisc_1(X20)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_19,plain,(
    ! [X17] :
      ( m1_subset_1(esk3_1(X17),k1_zfmisc_1(X17))
      & ~ v1_subset_1(esk3_1(X17),X17) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_subset_1])])])).

fof(c_0_20,plain,(
    ! [X15,X16] :
      ( v1_xboole_0(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(X15))
      | v1_subset_1(X16,X15)
      | ~ v1_xboole_0(X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_subset_1])])])])).

cnf(c_0_21,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( k6_domain_1(esk4_0,esk5_0) = k1_tarski(esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

fof(c_0_23,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | X2 != k1_tarski(X1) ),
    inference(er,[status(thm)],[c_0_17])).

fof(c_0_25,plain,(
    ! [X25,X26] :
      ( v1_xboole_0(X25)
      | v1_xboole_0(X26)
      | ~ v1_zfmisc_1(X26)
      | ~ r1_tarski(X25,X26)
      | X25 = X26 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( m1_subset_1(esk3_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( v1_xboole_0(X1)
    | v1_subset_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( ~ v1_subset_1(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk5_0),k1_zfmisc_1(esk4_0)) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_15]),c_0_16]),c_0_22])).

cnf(c_0_31,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X1 = X2
    | ~ v1_zfmisc_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( r1_tarski(esk3_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_35,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(esk3_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_27]),c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( v1_subset_1(k6_domain_1(esk4_0,esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k1_tarski(esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( v1_zfmisc_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_39,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,plain,
    ( esk3_1(X1) = X1
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( v1_subset_1(k1_tarski(esk5_0),esk4_0) ),
    inference(rw,[status(thm)],[c_0_36,c_0_22])).

cnf(c_0_42,negated_conjecture,
    ( k1_tarski(esk5_0) = esk4_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_37]),c_0_38])]),c_0_39]),c_0_16])).

cnf(c_0_43,plain,
    ( v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1)
    | ~ v1_subset_1(X1,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( v1_subset_1(esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_38])]),c_0_16]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.08  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.07/0.28  % Computer   : n002.cluster.edu
% 0.07/0.28  % Model      : x86_64 x86_64
% 0.07/0.28  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.28  % Memory     : 8042.1875MB
% 0.07/0.28  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.28  % CPULimit   : 60
% 0.07/0.28  % WCLimit    : 600
% 0.07/0.28  % DateTime   : Tue Dec  1 09:59:21 EST 2020
% 0.07/0.28  % CPUTime    : 
% 0.07/0.28  # Version: 2.5pre002
% 0.07/0.28  # No SInE strategy applied
% 0.07/0.28  # Trying AutoSched0 for 299 seconds
% 0.07/0.30  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.07/0.30  # and selection function SelectNewComplexAHP.
% 0.07/0.30  #
% 0.07/0.30  # Preprocessing time       : 0.012 s
% 0.07/0.30  
% 0.07/0.30  # Proof found!
% 0.07/0.30  # SZS status Theorem
% 0.07/0.30  # SZS output start CNFRefutation
% 0.07/0.30  fof(t6_tex_2, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,X1)=>~((v1_subset_1(k6_domain_1(X1,X2),X1)&v1_zfmisc_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 0.07/0.30  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.07/0.30  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.07/0.30  fof(dt_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 0.07/0.30  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.07/0.30  fof(rc3_subset_1, axiom, ![X1]:?[X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))&~(v1_subset_1(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 0.07/0.30  fof(cc2_subset_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(~(v1_subset_1(X2,X1))=>~(v1_xboole_0(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_subset_1)).
% 0.07/0.30  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.07/0.30  fof(t1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((~(v1_xboole_0(X2))&v1_zfmisc_1(X2))=>(r1_tarski(X1,X2)=>X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 0.07/0.30  fof(c_0_9, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,X1)=>~((v1_subset_1(k6_domain_1(X1,X2),X1)&v1_zfmisc_1(X1)))))), inference(assume_negation,[status(cth)],[t6_tex_2])).
% 0.07/0.30  fof(c_0_10, plain, ![X23, X24]:(v1_xboole_0(X23)|~m1_subset_1(X24,X23)|k6_domain_1(X23,X24)=k1_tarski(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.07/0.30  fof(c_0_11, negated_conjecture, (~v1_xboole_0(esk4_0)&(m1_subset_1(esk5_0,esk4_0)&(v1_subset_1(k6_domain_1(esk4_0,esk5_0),esk4_0)&v1_zfmisc_1(esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 0.07/0.30  fof(c_0_12, plain, ![X8, X9, X10, X11, X12, X13]:(((~r2_hidden(X10,X9)|X10=X8|X9!=k1_tarski(X8))&(X11!=X8|r2_hidden(X11,X9)|X9!=k1_tarski(X8)))&((~r2_hidden(esk2_2(X12,X13),X13)|esk2_2(X12,X13)!=X12|X13=k1_tarski(X12))&(r2_hidden(esk2_2(X12,X13),X13)|esk2_2(X12,X13)=X12|X13=k1_tarski(X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.07/0.30  fof(c_0_13, plain, ![X21, X22]:(v1_xboole_0(X21)|~m1_subset_1(X22,X21)|m1_subset_1(k6_domain_1(X21,X22),k1_zfmisc_1(X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).
% 0.07/0.30  cnf(c_0_14, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.07/0.30  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.07/0.30  cnf(c_0_16, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.07/0.30  cnf(c_0_17, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.07/0.30  fof(c_0_18, plain, ![X19, X20]:((~m1_subset_1(X19,k1_zfmisc_1(X20))|r1_tarski(X19,X20))&(~r1_tarski(X19,X20)|m1_subset_1(X19,k1_zfmisc_1(X20)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.07/0.30  fof(c_0_19, plain, ![X17]:(m1_subset_1(esk3_1(X17),k1_zfmisc_1(X17))&~v1_subset_1(esk3_1(X17),X17)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[rc3_subset_1])])])).
% 0.07/0.30  fof(c_0_20, plain, ![X15, X16]:(v1_xboole_0(X15)|(~m1_subset_1(X16,k1_zfmisc_1(X15))|(v1_subset_1(X16,X15)|~v1_xboole_0(X16)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_subset_1])])])])).
% 0.07/0.30  cnf(c_0_21, plain, (v1_xboole_0(X1)|m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.07/0.30  cnf(c_0_22, negated_conjecture, (k6_domain_1(esk4_0,esk5_0)=k1_tarski(esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])).
% 0.07/0.30  fof(c_0_23, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.07/0.30  cnf(c_0_24, plain, (r2_hidden(X1,X2)|X2!=k1_tarski(X1)), inference(er,[status(thm)],[c_0_17])).
% 0.07/0.30  fof(c_0_25, plain, ![X25, X26]:(v1_xboole_0(X25)|(v1_xboole_0(X26)|~v1_zfmisc_1(X26)|(~r1_tarski(X25,X26)|X25=X26))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).
% 0.07/0.30  cnf(c_0_26, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.07/0.30  cnf(c_0_27, plain, (m1_subset_1(esk3_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.07/0.30  cnf(c_0_28, plain, (v1_xboole_0(X1)|v1_subset_1(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.07/0.30  cnf(c_0_29, plain, (~v1_subset_1(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.07/0.30  cnf(c_0_30, negated_conjecture, (m1_subset_1(k1_tarski(esk5_0),k1_zfmisc_1(esk4_0))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_15]), c_0_16]), c_0_22])).
% 0.07/0.30  cnf(c_0_31, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.07/0.30  cnf(c_0_32, plain, (r2_hidden(X1,k1_tarski(X1))), inference(er,[status(thm)],[c_0_24])).
% 0.07/0.30  cnf(c_0_33, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|X1=X2|~v1_zfmisc_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.07/0.30  cnf(c_0_34, plain, (r1_tarski(esk3_1(X1),X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.07/0.30  cnf(c_0_35, plain, (v1_xboole_0(X1)|~v1_xboole_0(esk3_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_27]), c_0_29])).
% 0.07/0.30  cnf(c_0_36, negated_conjecture, (v1_subset_1(k6_domain_1(esk4_0,esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.07/0.30  cnf(c_0_37, negated_conjecture, (r1_tarski(k1_tarski(esk5_0),esk4_0)), inference(spm,[status(thm)],[c_0_26, c_0_30])).
% 0.07/0.30  cnf(c_0_38, negated_conjecture, (v1_zfmisc_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.07/0.30  cnf(c_0_39, plain, (~v1_xboole_0(k1_tarski(X1))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.07/0.30  cnf(c_0_40, plain, (esk3_1(X1)=X1|v1_xboole_0(X1)|~v1_zfmisc_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 0.07/0.30  cnf(c_0_41, negated_conjecture, (v1_subset_1(k1_tarski(esk5_0),esk4_0)), inference(rw,[status(thm)],[c_0_36, c_0_22])).
% 0.07/0.30  cnf(c_0_42, negated_conjecture, (k1_tarski(esk5_0)=esk4_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_37]), c_0_38])]), c_0_39]), c_0_16])).
% 0.07/0.30  cnf(c_0_43, plain, (v1_xboole_0(X1)|~v1_zfmisc_1(X1)|~v1_subset_1(X1,X1)), inference(spm,[status(thm)],[c_0_29, c_0_40])).
% 0.07/0.30  cnf(c_0_44, negated_conjecture, (v1_subset_1(esk4_0,esk4_0)), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 0.07/0.30  cnf(c_0_45, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_38])]), c_0_16]), ['proof']).
% 0.07/0.30  # SZS output end CNFRefutation
% 0.07/0.30  # Proof object total steps             : 46
% 0.07/0.30  # Proof object clause steps            : 27
% 0.07/0.30  # Proof object formula steps           : 19
% 0.07/0.30  # Proof object conjectures             : 14
% 0.07/0.30  # Proof object clause conjectures      : 11
% 0.07/0.30  # Proof object formula conjectures     : 3
% 0.07/0.30  # Proof object initial clauses used    : 13
% 0.07/0.30  # Proof object initial formulas used   : 9
% 0.07/0.30  # Proof object generating inferences   : 11
% 0.07/0.30  # Proof object simplifying inferences  : 15
% 0.07/0.30  # Training examples: 0 positive, 0 negative
% 0.07/0.30  # Parsed axioms                        : 9
% 0.07/0.30  # Removed by relevancy pruning/SinE    : 0
% 0.07/0.30  # Initial clauses                      : 18
% 0.07/0.30  # Removed in clause preprocessing      : 0
% 0.07/0.30  # Initial clauses in saturation        : 18
% 0.07/0.30  # Processed clauses                    : 48
% 0.07/0.30  # ...of these trivial                  : 2
% 0.07/0.30  # ...subsumed                          : 4
% 0.07/0.30  # ...remaining for further processing  : 42
% 0.07/0.30  # Other redundant clauses eliminated   : 1
% 0.07/0.30  # Clauses deleted for lack of memory   : 0
% 0.07/0.30  # Backward-subsumed                    : 0
% 0.07/0.30  # Backward-rewritten                   : 5
% 0.07/0.30  # Generated clauses                    : 46
% 0.07/0.30  # ...of the previous two non-trivial   : 40
% 0.07/0.30  # Contextual simplify-reflections      : 1
% 0.07/0.30  # Paramodulations                      : 41
% 0.07/0.30  # Factorizations                       : 0
% 0.07/0.30  # Equation resolutions                 : 5
% 0.07/0.30  # Propositional unsat checks           : 0
% 0.07/0.30  #    Propositional check models        : 0
% 0.07/0.30  #    Propositional check unsatisfiable : 0
% 0.07/0.30  #    Propositional clauses             : 0
% 0.07/0.30  #    Propositional clauses after purity: 0
% 0.07/0.30  #    Propositional unsat core size     : 0
% 0.07/0.30  #    Propositional preprocessing time  : 0.000
% 0.07/0.30  #    Propositional encoding time       : 0.000
% 0.07/0.30  #    Propositional solver time         : 0.000
% 0.07/0.30  #    Success case prop preproc time    : 0.000
% 0.07/0.30  #    Success case prop encoding time   : 0.000
% 0.07/0.30  #    Success case prop solver time     : 0.000
% 0.07/0.30  # Current number of processed clauses  : 36
% 0.07/0.30  #    Positive orientable unit clauses  : 13
% 0.07/0.30  #    Positive unorientable unit clauses: 0
% 0.07/0.30  #    Negative unit clauses             : 3
% 0.07/0.30  #    Non-unit-clauses                  : 20
% 0.07/0.30  # Current number of unprocessed clauses: 10
% 0.07/0.30  # ...number of literals in the above   : 24
% 0.07/0.30  # Current number of archived formulas  : 0
% 0.07/0.30  # Current number of archived clauses   : 5
% 0.07/0.30  # Clause-clause subsumption calls (NU) : 40
% 0.07/0.30  # Rec. Clause-clause subsumption calls : 23
% 0.07/0.30  # Non-unit clause-clause subsumptions  : 3
% 0.07/0.30  # Unit Clause-clause subsumption calls : 15
% 0.07/0.30  # Rewrite failures with RHS unbound    : 0
% 0.07/0.30  # BW rewrite match attempts            : 3
% 0.07/0.30  # BW rewrite match successes           : 2
% 0.07/0.30  # Condensation attempts                : 0
% 0.07/0.30  # Condensation successes               : 0
% 0.07/0.30  # Termbank termtop insertions          : 1634
% 0.07/0.30  
% 0.07/0.30  # -------------------------------------------------
% 0.07/0.30  # User time                : 0.013 s
% 0.07/0.30  # System time              : 0.002 s
% 0.07/0.30  # Total time               : 0.015 s
% 0.07/0.30  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
