%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:53 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   54 (  74 expanded)
%              Number of clauses        :   28 (  31 expanded)
%              Number of leaves         :   13 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :  113 ( 178 expanded)
%              Number of equality atoms :   25 (  28 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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

fof(cc2_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_zfmisc_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => ( ~ v1_xboole_0(X2)
           => ~ v1_subset_1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,X1)
           => ~ ( v1_subset_1(k6_domain_1(X1,X2),X1)
                & v1_zfmisc_1(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t6_tex_2])).

fof(c_0_14,plain,(
    ! [X25,X26] :
      ( v1_xboole_0(X25)
      | ~ v1_zfmisc_1(X25)
      | ~ m1_subset_1(X26,k1_zfmisc_1(X25))
      | v1_xboole_0(X26)
      | ~ v1_subset_1(X26,X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_tex_2])])])])).

fof(c_0_15,plain,(
    ! [X14,X15] :
      ( ~ v1_xboole_0(X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(X14))
      | v1_xboole_0(X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

fof(c_0_16,plain,(
    ! [X21,X22] :
      ( v1_xboole_0(X21)
      | ~ m1_subset_1(X22,X21)
      | m1_subset_1(k6_domain_1(X21,X22),k1_zfmisc_1(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

fof(c_0_17,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    & m1_subset_1(esk2_0,esk1_0)
    & v1_subset_1(k6_domain_1(esk1_0,esk2_0),esk1_0)
    & v1_zfmisc_1(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_18,plain,(
    ! [X11,X12] : k2_xboole_0(k1_tarski(X11),X12) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

fof(c_0_19,plain,(
    ! [X10] : k2_tarski(X10,X10) = k1_tarski(X10) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_20,plain,(
    ! [X16,X17] :
      ( ( ~ m1_subset_1(X16,k1_zfmisc_1(X17))
        | r1_tarski(X16,X17) )
      & ( ~ r1_tarski(X16,X17)
        | m1_subset_1(X16,k1_zfmisc_1(X17)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_21,plain,(
    ! [X13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X13)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_22,plain,(
    ! [X8,X9] :
      ( ~ v1_xboole_0(X8)
      | X8 = X9
      | ~ v1_xboole_0(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_23,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_zfmisc_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_30,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_31,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,X7)
      | k2_xboole_0(X6,X7) = X7 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_34,plain,(
    ! [X23,X24] :
      ( v1_xboole_0(X23)
      | ~ m1_subset_1(X24,X23)
      | k6_domain_1(X23,X24) = k1_tarski(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_35,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_37,plain,
    ( v1_xboole_0(X1)
    | ~ v1_subset_1(X1,X2)
    | ~ v1_zfmisc_1(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(k6_domain_1(esk1_0,esk2_0),k1_zfmisc_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_39,negated_conjecture,
    ( v1_subset_1(k6_domain_1(esk1_0,esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_40,negated_conjecture,
    ( v1_zfmisc_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_41,plain,
    ( k2_xboole_0(k2_tarski(X1,X1),X2) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_42,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_45,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,plain,
    ( k1_xboole_0 = X1
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( v1_xboole_0(k6_domain_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40])])).

cnf(c_0_48,plain,
    ( k2_xboole_0(X1,k2_tarski(X2,X2)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,plain,
    ( k6_domain_1(X1,X2) = k2_tarski(X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[c_0_45,c_0_29])).

cnf(c_0_51,negated_conjecture,
    ( k6_domain_1(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,plain,
    ( k2_tarski(X1,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_26]),c_0_51]),c_0_52]),c_0_27]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:10:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S083N
% 0.12/0.36  # and selection function SelectCQArNT.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.027 s
% 0.12/0.36  # Presaturation interreduction done
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(t6_tex_2, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,X1)=>~((v1_subset_1(k6_domain_1(X1,X2),X1)&v1_zfmisc_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 0.12/0.36  fof(cc2_tex_2, axiom, ![X1]:((~(v1_xboole_0(X1))&v1_zfmisc_1(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(~(v1_xboole_0(X2))=>~(v1_subset_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 0.12/0.36  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.12/0.36  fof(dt_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 0.12/0.36  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.12/0.36  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.12/0.36  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.12/0.36  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.12/0.36  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 0.12/0.36  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.12/0.36  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.12/0.36  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.12/0.36  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.12/0.36  fof(c_0_13, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,X1)=>~((v1_subset_1(k6_domain_1(X1,X2),X1)&v1_zfmisc_1(X1)))))), inference(assume_negation,[status(cth)],[t6_tex_2])).
% 0.12/0.36  fof(c_0_14, plain, ![X25, X26]:(v1_xboole_0(X25)|~v1_zfmisc_1(X25)|(~m1_subset_1(X26,k1_zfmisc_1(X25))|(v1_xboole_0(X26)|~v1_subset_1(X26,X25)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_tex_2])])])])).
% 0.12/0.36  fof(c_0_15, plain, ![X14, X15]:(~v1_xboole_0(X14)|(~m1_subset_1(X15,k1_zfmisc_1(X14))|v1_xboole_0(X15))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.12/0.36  fof(c_0_16, plain, ![X21, X22]:(v1_xboole_0(X21)|~m1_subset_1(X22,X21)|m1_subset_1(k6_domain_1(X21,X22),k1_zfmisc_1(X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).
% 0.12/0.36  fof(c_0_17, negated_conjecture, (~v1_xboole_0(esk1_0)&(m1_subset_1(esk2_0,esk1_0)&(v1_subset_1(k6_domain_1(esk1_0,esk2_0),esk1_0)&v1_zfmisc_1(esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.12/0.36  fof(c_0_18, plain, ![X11, X12]:k2_xboole_0(k1_tarski(X11),X12)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.12/0.36  fof(c_0_19, plain, ![X10]:k2_tarski(X10,X10)=k1_tarski(X10), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.36  fof(c_0_20, plain, ![X16, X17]:((~m1_subset_1(X16,k1_zfmisc_1(X17))|r1_tarski(X16,X17))&(~r1_tarski(X16,X17)|m1_subset_1(X16,k1_zfmisc_1(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.12/0.36  fof(c_0_21, plain, ![X13]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X13)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.12/0.36  fof(c_0_22, plain, ![X8, X9]:(~v1_xboole_0(X8)|X8=X9|~v1_xboole_0(X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 0.12/0.36  cnf(c_0_23, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|~v1_zfmisc_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.36  cnf(c_0_24, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.36  cnf(c_0_25, plain, (v1_xboole_0(X1)|m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.36  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.36  cnf(c_0_27, negated_conjecture, (~v1_xboole_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.36  cnf(c_0_28, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.36  cnf(c_0_29, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.36  fof(c_0_30, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.12/0.36  fof(c_0_31, plain, ![X6, X7]:(~r1_tarski(X6,X7)|k2_xboole_0(X6,X7)=X7), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.12/0.36  cnf(c_0_32, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.36  cnf(c_0_33, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.36  fof(c_0_34, plain, ![X23, X24]:(v1_xboole_0(X23)|~m1_subset_1(X24,X23)|k6_domain_1(X23,X24)=k1_tarski(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.12/0.36  cnf(c_0_35, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.36  cnf(c_0_36, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.12/0.36  cnf(c_0_37, plain, (v1_xboole_0(X1)|~v1_subset_1(X1,X2)|~v1_zfmisc_1(X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(csr,[status(thm)],[c_0_23, c_0_24])).
% 0.12/0.36  cnf(c_0_38, negated_conjecture, (m1_subset_1(k6_domain_1(esk1_0,esk2_0),k1_zfmisc_1(esk1_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])).
% 0.12/0.36  cnf(c_0_39, negated_conjecture, (v1_subset_1(k6_domain_1(esk1_0,esk2_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.36  cnf(c_0_40, negated_conjecture, (v1_zfmisc_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.36  cnf(c_0_41, plain, (k2_xboole_0(k2_tarski(X1,X1),X2)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.12/0.36  cnf(c_0_42, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.36  cnf(c_0_43, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.36  cnf(c_0_44, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.12/0.36  cnf(c_0_45, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.12/0.36  cnf(c_0_46, plain, (k1_xboole_0=X1|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.12/0.36  cnf(c_0_47, negated_conjecture, (v1_xboole_0(k6_domain_1(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40])])).
% 0.12/0.36  cnf(c_0_48, plain, (k2_xboole_0(X1,k2_tarski(X2,X2))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.12/0.36  cnf(c_0_49, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.12/0.36  cnf(c_0_50, plain, (k6_domain_1(X1,X2)=k2_tarski(X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[c_0_45, c_0_29])).
% 0.12/0.36  cnf(c_0_51, negated_conjecture, (k6_domain_1(esk1_0,esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.12/0.36  cnf(c_0_52, plain, (k2_tarski(X1,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.12/0.36  cnf(c_0_53, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_26]), c_0_51]), c_0_52]), c_0_27]), ['proof']).
% 0.12/0.36  # SZS output end CNFRefutation
% 0.12/0.36  # Proof object total steps             : 54
% 0.12/0.36  # Proof object clause steps            : 28
% 0.12/0.36  # Proof object formula steps           : 26
% 0.12/0.36  # Proof object conjectures             : 11
% 0.12/0.36  # Proof object clause conjectures      : 8
% 0.12/0.36  # Proof object formula conjectures     : 3
% 0.12/0.36  # Proof object initial clauses used    : 16
% 0.12/0.36  # Proof object initial formulas used   : 13
% 0.12/0.36  # Proof object generating inferences   : 9
% 0.12/0.36  # Proof object simplifying inferences  : 10
% 0.12/0.36  # Training examples: 0 positive, 0 negative
% 0.12/0.36  # Parsed axioms                        : 14
% 0.12/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.36  # Initial clauses                      : 18
% 0.12/0.36  # Removed in clause preprocessing      : 1
% 0.12/0.36  # Initial clauses in saturation        : 17
% 0.12/0.36  # Processed clauses                    : 94
% 0.12/0.36  # ...of these trivial                  : 2
% 0.12/0.36  # ...subsumed                          : 39
% 0.12/0.36  # ...remaining for further processing  : 53
% 0.12/0.36  # Other redundant clauses eliminated   : 10
% 0.12/0.36  # Clauses deleted for lack of memory   : 0
% 0.12/0.36  # Backward-subsumed                    : 0
% 0.12/0.36  # Backward-rewritten                   : 4
% 0.12/0.36  # Generated clauses                    : 95
% 0.12/0.36  # ...of the previous two non-trivial   : 77
% 0.12/0.36  # Contextual simplify-reflections      : 1
% 0.12/0.36  # Paramodulations                      : 85
% 0.12/0.36  # Factorizations                       : 0
% 0.12/0.36  # Equation resolutions                 : 10
% 0.12/0.36  # Propositional unsat checks           : 0
% 0.12/0.36  #    Propositional check models        : 0
% 0.12/0.36  #    Propositional check unsatisfiable : 0
% 0.12/0.36  #    Propositional clauses             : 0
% 0.12/0.36  #    Propositional clauses after purity: 0
% 0.12/0.36  #    Propositional unsat core size     : 0
% 0.12/0.36  #    Propositional preprocessing time  : 0.000
% 0.12/0.36  #    Propositional encoding time       : 0.000
% 0.12/0.36  #    Propositional solver time         : 0.000
% 0.12/0.36  #    Success case prop preproc time    : 0.000
% 0.12/0.36  #    Success case prop encoding time   : 0.000
% 0.12/0.36  #    Success case prop solver time     : 0.000
% 0.12/0.36  # Current number of processed clauses  : 32
% 0.12/0.36  #    Positive orientable unit clauses  : 9
% 0.12/0.36  #    Positive unorientable unit clauses: 1
% 0.12/0.36  #    Negative unit clauses             : 7
% 0.12/0.36  #    Non-unit-clauses                  : 15
% 0.12/0.36  # Current number of unprocessed clauses: 10
% 0.12/0.36  # ...number of literals in the above   : 43
% 0.12/0.36  # Current number of archived formulas  : 0
% 0.12/0.36  # Current number of archived clauses   : 22
% 0.12/0.36  # Clause-clause subsumption calls (NU) : 62
% 0.12/0.36  # Rec. Clause-clause subsumption calls : 27
% 0.12/0.36  # Non-unit clause-clause subsumptions  : 8
% 0.12/0.36  # Unit Clause-clause subsumption calls : 45
% 0.12/0.36  # Rewrite failures with RHS unbound    : 0
% 0.12/0.36  # BW rewrite match attempts            : 8
% 0.12/0.36  # BW rewrite match successes           : 8
% 0.12/0.36  # Condensation attempts                : 0
% 0.12/0.36  # Condensation successes               : 0
% 0.12/0.36  # Termbank termtop insertions          : 1930
% 0.12/0.36  
% 0.12/0.36  # -------------------------------------------------
% 0.12/0.36  # User time                : 0.031 s
% 0.12/0.36  # System time              : 0.002 s
% 0.12/0.36  # Total time               : 0.033 s
% 0.12/0.36  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
