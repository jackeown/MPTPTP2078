%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0678+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:01 EST 2020

% Result     : Theorem 0.08s
% Output     : CNFRefutation 0.08s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 196 expanded)
%              Number of clauses        :   38 (  73 expanded)
%              Number of leaves         :   11 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :  158 ( 670 expanded)
%              Number of equality atoms :   46 ( 171 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal clause size      :   23 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t122_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( ! [X2,X3] : k9_relat_1(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
       => v2_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t122_funct_1)).

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

fof(d16_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(t117_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => k11_relat_1(X2,X1) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t17_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X1 != X2
     => r1_xboole_0(k1_tarski(X1),k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(t149_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_relat_1)).

fof(redefinition_r1_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2) )
     => ( r1_subset_1(X1,X2)
      <=> r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(irreflexivity_r1_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2) )
     => ~ r1_subset_1(X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r1_subset_1)).

fof(fc2_xboole_0,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( ! [X2,X3] : k9_relat_1(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
         => v2_funct_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t122_funct_1])).

fof(c_0_12,plain,(
    ! [X10,X11,X12] :
      ( ( ~ v2_funct_1(X10)
        | ~ r2_hidden(X11,k1_relat_1(X10))
        | ~ r2_hidden(X12,k1_relat_1(X10))
        | k1_funct_1(X10,X11) != k1_funct_1(X10,X12)
        | X11 = X12
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( r2_hidden(esk1_1(X10),k1_relat_1(X10))
        | v2_funct_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( r2_hidden(esk2_1(X10),k1_relat_1(X10))
        | v2_funct_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( k1_funct_1(X10,esk1_1(X10)) = k1_funct_1(X10,esk2_1(X10))
        | v2_funct_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( esk1_1(X10) != esk2_1(X10)
        | v2_funct_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).

fof(c_0_13,negated_conjecture,(
    ! [X27,X28] :
      ( v1_relat_1(esk3_0)
      & v1_funct_1(esk3_0)
      & k9_relat_1(esk3_0,k3_xboole_0(X27,X28)) = k3_xboole_0(k9_relat_1(esk3_0,X27),k9_relat_1(esk3_0,X28))
      & ~ v2_funct_1(esk3_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).

fof(c_0_14,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(X6)
      | k11_relat_1(X6,X7) = k9_relat_1(X6,k1_tarski(X7)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

fof(c_0_15,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X22)
      | ~ v1_funct_1(X22)
      | ~ r2_hidden(X21,k1_relat_1(X22))
      | k11_relat_1(X22,X21) = k1_tarski(k1_funct_1(X22,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t117_funct_1])])).

cnf(c_0_16,plain,
    ( r2_hidden(esk1_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,plain,(
    ! [X8,X9] :
      ( ( ~ r1_xboole_0(X8,X9)
        | k3_xboole_0(X8,X9) = k1_xboole_0 )
      & ( k3_xboole_0(X8,X9) != k1_xboole_0
        | r1_xboole_0(X8,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_21,plain,(
    ! [X16] : k3_xboole_0(X16,X16) = X16 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_22,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( r2_hidden(esk2_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,plain,
    ( k1_funct_1(X1,esk1_1(X1)) = k1_funct_1(X1,esk2_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,plain,
    ( k11_relat_1(X1,X2) = k1_tarski(k1_funct_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk1_1(esk3_0),k1_relat_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_27,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( k9_relat_1(esk3_0,k3_xboole_0(X1,X2)) = k3_xboole_0(k9_relat_1(esk3_0,X1),k9_relat_1(esk3_0,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,negated_conjecture,
    ( k9_relat_1(esk3_0,k1_tarski(X1)) = k11_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_18])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk2_1(esk3_0),k1_relat_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_32,negated_conjecture,
    ( k1_funct_1(esk3_0,esk2_1(esk3_0)) = k1_funct_1(esk3_0,esk1_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_33,negated_conjecture,
    ( k1_tarski(k1_funct_1(esk3_0,esk1_1(esk3_0))) = k11_relat_1(esk3_0,esk1_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_17]),c_0_18])])).

fof(c_0_34,plain,(
    ! [X24,X25] :
      ( X24 = X25
      | r1_xboole_0(k1_tarski(X24),k1_tarski(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_zfmisc_1])])).

fof(c_0_35,plain,(
    ! [X23] :
      ( ~ v1_relat_1(X23)
      | k9_relat_1(X23,k1_xboole_0) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t149_relat_1])])).

fof(c_0_36,plain,(
    ! [X19,X20] :
      ( ( ~ r1_subset_1(X19,X20)
        | r1_xboole_0(X19,X20)
        | v1_xboole_0(X19)
        | v1_xboole_0(X20) )
      & ( ~ r1_xboole_0(X19,X20)
        | r1_subset_1(X19,X20)
        | v1_xboole_0(X19)
        | v1_xboole_0(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).

cnf(c_0_37,plain,
    ( r1_xboole_0(X1,X1)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( k3_xboole_0(k11_relat_1(esk3_0,X1),k9_relat_1(esk3_0,X2)) = k9_relat_1(esk3_0,k3_xboole_0(k1_tarski(X1),X2)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( k11_relat_1(esk3_0,esk2_1(esk3_0)) = k11_relat_1(esk3_0,esk1_1(esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_31]),c_0_17]),c_0_18])]),c_0_32]),c_0_33])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_41,plain,
    ( X1 = X2
    | r1_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( k9_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_43,plain,(
    ! [X17,X18] :
      ( v1_xboole_0(X17)
      | v1_xboole_0(X18)
      | ~ r1_subset_1(X17,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[irreflexivity_r1_subset_1])])])).

cnf(c_0_44,plain,
    ( r1_subset_1(X1,X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_37])).

fof(c_0_46,plain,(
    ! [X15] : ~ v1_xboole_0(k1_tarski(X15)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

cnf(c_0_47,negated_conjecture,
    ( k9_relat_1(esk3_0,k3_xboole_0(k1_tarski(esk2_1(esk3_0)),X1)) = k9_relat_1(esk3_0,k3_xboole_0(k1_tarski(esk1_1(esk3_0)),X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_38])).

cnf(c_0_48,plain,
    ( k3_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_xboole_0
    | X1 = X2 ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( k9_relat_1(esk3_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_18])).

cnf(c_0_50,plain,
    ( v2_funct_1(X1)
    | esk1_1(X1) != esk2_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_51,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( r1_subset_1(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_53,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( k9_relat_1(esk3_0,k3_xboole_0(k1_tarski(esk1_1(esk3_0)),k1_tarski(X1))) = k1_xboole_0
    | esk2_1(esk3_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( esk2_1(esk3_0) != esk1_1(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_56,plain,
    ( v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( ~ v1_xboole_0(k11_relat_1(esk3_0,esk1_1(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_33])).

cnf(c_0_58,negated_conjecture,
    ( k11_relat_1(esk3_0,esk1_1(esk3_0)) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_28]),c_0_30]),c_0_55])).

cnf(c_0_59,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_58]),c_0_59])]),
    [proof]).

%------------------------------------------------------------------------------
