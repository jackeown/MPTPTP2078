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
% DateTime   : Thu Dec  3 11:18:43 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 132 expanded)
%              Number of clauses        :   37 (  57 expanded)
%              Number of leaves         :   12 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :  158 ( 403 expanded)
%              Number of equality atoms :   56 ( 124 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(d1_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( v1_zfmisc_1(X1)
      <=> ? [X2] :
            ( m1_subset_1(X2,X1)
            & X1 = k6_domain_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

fof(t1_tex_2,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_zfmisc_1(X2) )
         => ( r1_tarski(X1,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(c_0_12,plain,(
    ! [X31,X32] :
      ( v1_xboole_0(X31)
      | ~ m1_subset_1(X32,X31)
      | k6_domain_1(X31,X32) = k1_tarski(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_13,plain,(
    ! [X28] : k2_tarski(X28,X28) = k1_tarski(X28) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_14,plain,(
    ! [X21,X22,X23,X24,X25,X26] :
      ( ( ~ r2_hidden(X23,X22)
        | X23 = X21
        | X22 != k1_tarski(X21) )
      & ( X24 != X21
        | r2_hidden(X24,X22)
        | X22 != k1_tarski(X21) )
      & ( ~ r2_hidden(esk3_2(X25,X26),X26)
        | esk3_2(X25,X26) != X25
        | X26 = k1_tarski(X25) )
      & ( r2_hidden(esk3_2(X25,X26),X26)
        | esk3_2(X25,X26) = X25
        | X26 = k1_tarski(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_15,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X33,X35] :
      ( ( m1_subset_1(esk4_1(X33),X33)
        | ~ v1_zfmisc_1(X33)
        | v1_xboole_0(X33) )
      & ( X33 = k6_domain_1(X33,esk4_1(X33))
        | ~ v1_zfmisc_1(X33)
        | v1_xboole_0(X33) )
      & ( ~ m1_subset_1(X35,X33)
        | X33 != k6_domain_1(X33,X35)
        | v1_zfmisc_1(X33)
        | v1_xboole_0(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tex_2])])])])])])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v1_zfmisc_1(X2) )
           => ( r1_tarski(X1,X2)
             => X1 = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t1_tex_2])).

cnf(c_0_19,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k6_domain_1(X1,X2) = k2_tarski(X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( m1_subset_1(esk4_1(X1),X1)
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk2_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk2_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_23,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0)
    & ~ v1_xboole_0(esk6_0)
    & v1_zfmisc_1(esk6_0)
    & r1_tarski(esk5_0,esk6_0)
    & esk5_0 != esk6_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).

fof(c_0_24,plain,(
    ! [X19,X20] : k2_xboole_0(X19,k4_xboole_0(X20,X19)) = k2_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_25,plain,(
    ! [X29,X30] : k3_tarski(k2_tarski(X29,X30)) = k2_xboole_0(X29,X30) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_26,plain,(
    ! [X18] : k2_xboole_0(X18,k1_xboole_0) = X18 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_27,plain,
    ( X1 = X3
    | X2 != k2_tarski(X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_16])).

cnf(c_0_28,plain,
    ( k2_tarski(esk4_1(X1),esk4_1(X1)) = k6_domain_1(X1,esk4_1(X1))
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_29,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_30,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_32,plain,(
    ! [X16,X17] :
      ( ~ r1_tarski(X16,X17)
      | k2_xboole_0(X16,X17) = X17 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_33,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_35,plain,(
    ! [X14,X15] :
      ( ( k4_xboole_0(X14,X15) != k1_xboole_0
        | r1_tarski(X14,X15) )
      & ( ~ r1_tarski(X14,X15)
        | k4_xboole_0(X14,X15) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_36,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( X1 = esk4_1(X2)
    | v1_xboole_0(X2)
    | X3 != k6_domain_1(X2,esk4_1(X2))
    | ~ v1_zfmisc_1(X2)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_38,plain,
    ( X1 = k6_domain_1(X1,esk4_1(X1))
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_39,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_41,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_43,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( k3_tarski(k2_tarski(X1,k4_xboole_0(X2,X1))) = k3_tarski(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_34])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,plain,
    ( k3_tarski(k2_tarski(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_36,c_0_34])).

cnf(c_0_47,plain,
    ( X1 = esk4_1(X2)
    | ~ v1_zfmisc_1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38])]),c_0_39])).

cnf(c_0_48,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk1_1(esk5_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( v1_zfmisc_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_51,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_43,c_0_34])).

cnf(c_0_52,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_54,plain,
    ( esk2_2(X1,X2) = esk4_1(X1)
    | r1_tarski(X1,X2)
    | ~ v1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( esk1_1(esk5_0) = esk4_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_49]),c_0_50])])).

cnf(c_0_56,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( esk5_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_zfmisc_1(X1)
    | ~ r2_hidden(esk4_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk4_1(esk6_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_55]),c_0_42])).

cnf(c_0_60,negated_conjecture,
    ( ~ r1_tarski(esk6_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_31]),c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_50])]),c_0_60]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:42:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.43  # AutoSched0-Mode selected heuristic G_E___103_C18_F1_PI_AE_Q4_CS_SP_S0Y
% 0.20/0.43  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.43  #
% 0.20/0.43  # Preprocessing time       : 0.029 s
% 0.20/0.43  
% 0.20/0.43  # Proof found!
% 0.20/0.43  # SZS status Theorem
% 0.20/0.43  # SZS output start CNFRefutation
% 0.20/0.43  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.20/0.43  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.43  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.20/0.43  fof(d1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>(v1_zfmisc_1(X1)<=>?[X2]:(m1_subset_1(X2,X1)&X1=k6_domain_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 0.20/0.43  fof(t1_tex_2, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((~(v1_xboole_0(X2))&v1_zfmisc_1(X2))=>(r1_tarski(X1,X2)=>X1=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 0.20/0.43  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.43  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.20/0.43  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.20/0.43  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.20/0.43  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.43  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.20/0.43  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.20/0.43  fof(c_0_12, plain, ![X31, X32]:(v1_xboole_0(X31)|~m1_subset_1(X32,X31)|k6_domain_1(X31,X32)=k1_tarski(X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.20/0.43  fof(c_0_13, plain, ![X28]:k2_tarski(X28,X28)=k1_tarski(X28), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.43  fof(c_0_14, plain, ![X21, X22, X23, X24, X25, X26]:(((~r2_hidden(X23,X22)|X23=X21|X22!=k1_tarski(X21))&(X24!=X21|r2_hidden(X24,X22)|X22!=k1_tarski(X21)))&((~r2_hidden(esk3_2(X25,X26),X26)|esk3_2(X25,X26)!=X25|X26=k1_tarski(X25))&(r2_hidden(esk3_2(X25,X26),X26)|esk3_2(X25,X26)=X25|X26=k1_tarski(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.20/0.43  cnf(c_0_15, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.43  cnf(c_0_16, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.43  fof(c_0_17, plain, ![X33, X35]:(((m1_subset_1(esk4_1(X33),X33)|~v1_zfmisc_1(X33)|v1_xboole_0(X33))&(X33=k6_domain_1(X33,esk4_1(X33))|~v1_zfmisc_1(X33)|v1_xboole_0(X33)))&(~m1_subset_1(X35,X33)|X33!=k6_domain_1(X33,X35)|v1_zfmisc_1(X33)|v1_xboole_0(X33))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tex_2])])])])])])).
% 0.20/0.43  fof(c_0_18, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:((~(v1_xboole_0(X2))&v1_zfmisc_1(X2))=>(r1_tarski(X1,X2)=>X1=X2)))), inference(assume_negation,[status(cth)],[t1_tex_2])).
% 0.20/0.43  cnf(c_0_19, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.43  cnf(c_0_20, plain, (k6_domain_1(X1,X2)=k2_tarski(X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.43  cnf(c_0_21, plain, (m1_subset_1(esk4_1(X1),X1)|v1_xboole_0(X1)|~v1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.43  fof(c_0_22, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk2_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk2_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.43  fof(c_0_23, negated_conjecture, (~v1_xboole_0(esk5_0)&((~v1_xboole_0(esk6_0)&v1_zfmisc_1(esk6_0))&(r1_tarski(esk5_0,esk6_0)&esk5_0!=esk6_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).
% 0.20/0.43  fof(c_0_24, plain, ![X19, X20]:k2_xboole_0(X19,k4_xboole_0(X20,X19))=k2_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.20/0.43  fof(c_0_25, plain, ![X29, X30]:k3_tarski(k2_tarski(X29,X30))=k2_xboole_0(X29,X30), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.20/0.43  fof(c_0_26, plain, ![X18]:k2_xboole_0(X18,k1_xboole_0)=X18, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.20/0.43  cnf(c_0_27, plain, (X1=X3|X2!=k2_tarski(X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_19, c_0_16])).
% 0.20/0.43  cnf(c_0_28, plain, (k2_tarski(esk4_1(X1),esk4_1(X1))=k6_domain_1(X1,esk4_1(X1))|v1_xboole_0(X1)|~v1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.43  fof(c_0_29, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.43  cnf(c_0_30, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.43  cnf(c_0_31, negated_conjecture, (r1_tarski(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.43  fof(c_0_32, plain, ![X16, X17]:(~r1_tarski(X16,X17)|k2_xboole_0(X16,X17)=X17), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.20/0.43  cnf(c_0_33, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.43  cnf(c_0_34, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.43  fof(c_0_35, plain, ![X14, X15]:((k4_xboole_0(X14,X15)!=k1_xboole_0|r1_tarski(X14,X15))&(~r1_tarski(X14,X15)|k4_xboole_0(X14,X15)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.20/0.43  cnf(c_0_36, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.43  cnf(c_0_37, plain, (X1=esk4_1(X2)|v1_xboole_0(X2)|X3!=k6_domain_1(X2,esk4_1(X2))|~v1_zfmisc_1(X2)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.43  cnf(c_0_38, plain, (X1=k6_domain_1(X1,esk4_1(X1))|v1_xboole_0(X1)|~v1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.43  cnf(c_0_39, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.43  cnf(c_0_40, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.43  cnf(c_0_41, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.43  cnf(c_0_42, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.43  cnf(c_0_43, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.43  cnf(c_0_44, plain, (k3_tarski(k2_tarski(X1,k4_xboole_0(X2,X1)))=k3_tarski(k2_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34]), c_0_34])).
% 0.20/0.43  cnf(c_0_45, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.43  cnf(c_0_46, plain, (k3_tarski(k2_tarski(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_36, c_0_34])).
% 0.20/0.43  cnf(c_0_47, plain, (X1=esk4_1(X2)|~v1_zfmisc_1(X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38])]), c_0_39])).
% 0.20/0.43  cnf(c_0_48, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.43  cnf(c_0_49, negated_conjecture, (r2_hidden(esk1_1(esk5_0),esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 0.20/0.43  cnf(c_0_50, negated_conjecture, (v1_zfmisc_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.43  cnf(c_0_51, plain, (k3_tarski(k2_tarski(X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_43, c_0_34])).
% 0.20/0.43  cnf(c_0_52, plain, (k3_tarski(k2_tarski(X1,X2))=X1|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])).
% 0.20/0.43  cnf(c_0_53, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.43  cnf(c_0_54, plain, (esk2_2(X1,X2)=esk4_1(X1)|r1_tarski(X1,X2)|~v1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.43  cnf(c_0_55, negated_conjecture, (esk1_1(esk5_0)=esk4_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_49]), c_0_50])])).
% 0.20/0.43  cnf(c_0_56, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.20/0.43  cnf(c_0_57, negated_conjecture, (esk5_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.43  cnf(c_0_58, plain, (r1_tarski(X1,X2)|~v1_zfmisc_1(X1)|~r2_hidden(esk4_1(X1),X2)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.43  cnf(c_0_59, negated_conjecture, (r2_hidden(esk4_1(esk6_0),esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_55]), c_0_42])).
% 0.20/0.43  cnf(c_0_60, negated_conjecture, (~r1_tarski(esk6_0,esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_31]), c_0_57])).
% 0.20/0.43  cnf(c_0_61, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_50])]), c_0_60]), ['proof']).
% 0.20/0.43  # SZS output end CNFRefutation
% 0.20/0.43  # Proof object total steps             : 62
% 0.20/0.43  # Proof object clause steps            : 37
% 0.20/0.43  # Proof object formula steps           : 25
% 0.20/0.43  # Proof object conjectures             : 13
% 0.20/0.43  # Proof object clause conjectures      : 10
% 0.20/0.43  # Proof object formula conjectures     : 3
% 0.20/0.43  # Proof object initial clauses used    : 19
% 0.20/0.43  # Proof object initial formulas used   : 12
% 0.20/0.43  # Proof object generating inferences   : 13
% 0.20/0.43  # Proof object simplifying inferences  : 17
% 0.20/0.43  # Training examples: 0 positive, 0 negative
% 0.20/0.43  # Parsed axioms                        : 12
% 0.20/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.43  # Initial clauses                      : 25
% 0.20/0.43  # Removed in clause preprocessing      : 2
% 0.20/0.43  # Initial clauses in saturation        : 23
% 0.20/0.43  # Processed clauses                    : 305
% 0.20/0.43  # ...of these trivial                  : 9
% 0.20/0.43  # ...subsumed                          : 130
% 0.20/0.43  # ...remaining for further processing  : 166
% 0.20/0.43  # Other redundant clauses eliminated   : 37
% 0.20/0.43  # Clauses deleted for lack of memory   : 0
% 0.20/0.43  # Backward-subsumed                    : 6
% 0.20/0.43  # Backward-rewritten                   : 2
% 0.20/0.43  # Generated clauses                    : 1997
% 0.20/0.43  # ...of the previous two non-trivial   : 1863
% 0.20/0.43  # Contextual simplify-reflections      : 8
% 0.20/0.43  # Paramodulations                      : 1937
% 0.20/0.43  # Factorizations                       : 8
% 0.20/0.43  # Equation resolutions                 : 46
% 0.20/0.43  # Propositional unsat checks           : 0
% 0.20/0.43  #    Propositional check models        : 0
% 0.20/0.43  #    Propositional check unsatisfiable : 0
% 0.20/0.43  #    Propositional clauses             : 0
% 0.20/0.43  #    Propositional clauses after purity: 0
% 0.20/0.43  #    Propositional unsat core size     : 0
% 0.20/0.43  #    Propositional preprocessing time  : 0.000
% 0.20/0.43  #    Propositional encoding time       : 0.000
% 0.20/0.43  #    Propositional solver time         : 0.000
% 0.20/0.43  #    Success case prop preproc time    : 0.000
% 0.20/0.43  #    Success case prop encoding time   : 0.000
% 0.20/0.43  #    Success case prop solver time     : 0.000
% 0.20/0.43  # Current number of processed clauses  : 155
% 0.20/0.43  #    Positive orientable unit clauses  : 10
% 0.20/0.43  #    Positive unorientable unit clauses: 0
% 0.20/0.43  #    Negative unit clauses             : 5
% 0.20/0.43  #    Non-unit-clauses                  : 140
% 0.20/0.43  # Current number of unprocessed clauses: 1571
% 0.20/0.43  # ...number of literals in the above   : 8782
% 0.20/0.43  # Current number of archived formulas  : 0
% 0.20/0.43  # Current number of archived clauses   : 10
% 0.20/0.43  # Clause-clause subsumption calls (NU) : 2127
% 0.20/0.43  # Rec. Clause-clause subsumption calls : 1360
% 0.20/0.43  # Non-unit clause-clause subsumptions  : 133
% 0.20/0.43  # Unit Clause-clause subsumption calls : 68
% 0.20/0.43  # Rewrite failures with RHS unbound    : 0
% 0.20/0.43  # BW rewrite match attempts            : 5
% 0.20/0.43  # BW rewrite match successes           : 1
% 0.20/0.43  # Condensation attempts                : 0
% 0.20/0.43  # Condensation successes               : 0
% 0.20/0.43  # Termbank termtop insertions          : 30107
% 0.20/0.43  
% 0.20/0.43  # -------------------------------------------------
% 0.20/0.43  # User time                : 0.078 s
% 0.20/0.43  # System time              : 0.005 s
% 0.20/0.43  # Total time               : 0.082 s
% 0.20/0.43  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
