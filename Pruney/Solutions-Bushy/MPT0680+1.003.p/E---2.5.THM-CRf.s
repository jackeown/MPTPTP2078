%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0680+1.003 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 500 expanded)
%              Number of clauses        :   33 ( 178 expanded)
%              Number of leaves         :    6 ( 120 expanded)
%              Depth                    :   13
%              Number of atoms          :  117 (1864 expanded)
%              Number of equality atoms :   51 ( 483 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal clause size      :   23 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t124_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( ! [X2,X3] : k9_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
       => v2_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_funct_1)).

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

fof(t20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( ! [X2,X3] : k9_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
         => v2_funct_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t124_funct_1])).

fof(c_0_7,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X4)
      | k11_relat_1(X4,X5) = k9_relat_1(X4,k1_tarski(X5)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

fof(c_0_8,negated_conjecture,(
    ! [X19,X20] :
      ( v1_relat_1(esk3_0)
      & v1_funct_1(esk3_0)
      & k9_relat_1(esk3_0,k6_subset_1(X19,X20)) = k6_subset_1(k9_relat_1(esk3_0,X19),k9_relat_1(esk3_0,X20))
      & ~ v2_funct_1(esk3_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).

fof(c_0_9,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X14)
      | ~ v1_funct_1(X14)
      | ~ r2_hidden(X13,k1_relat_1(X14))
      | k11_relat_1(X14,X13) = k1_tarski(k1_funct_1(X14,X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t117_funct_1])])).

cnf(c_0_10,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v2_funct_1(X6)
        | ~ r2_hidden(X7,k1_relat_1(X6))
        | ~ r2_hidden(X8,k1_relat_1(X6))
        | k1_funct_1(X6,X7) != k1_funct_1(X6,X8)
        | X7 = X8
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( r2_hidden(esk1_1(X6),k1_relat_1(X6))
        | v2_funct_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( r2_hidden(esk2_1(X6),k1_relat_1(X6))
        | v2_funct_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( k1_funct_1(X6,esk1_1(X6)) = k1_funct_1(X6,esk2_1(X6))
        | v2_funct_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( esk1_1(X6) != esk2_1(X6)
        | v2_funct_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).

cnf(c_0_13,plain,
    ( k11_relat_1(X1,X2) = k1_tarski(k1_funct_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( k11_relat_1(esk3_0,X1) = k9_relat_1(esk3_0,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(esk2_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,plain,
    ( k1_funct_1(X1,esk1_1(X1)) = k1_funct_1(X1,esk2_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r2_hidden(esk1_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( k9_relat_1(esk3_0,k1_tarski(X1)) = k1_tarski(k1_funct_1(esk3_0,X1))
    | ~ r2_hidden(X1,k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_11])])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk2_1(esk3_0),k1_relat_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_14]),c_0_11])]),c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( k1_funct_1(esk3_0,esk2_1(esk3_0)) = k1_funct_1(esk3_0,esk1_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_14]),c_0_11])]),c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk1_1(esk3_0),k1_relat_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_14]),c_0_11])]),c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( k9_relat_1(esk3_0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(esk3_0,X1),k9_relat_1(esk3_0,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,negated_conjecture,
    ( k9_relat_1(esk3_0,k1_tarski(esk2_1(esk3_0))) = k1_tarski(k1_funct_1(esk3_0,esk1_1(esk3_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

fof(c_0_26,plain,(
    ! [X15,X16] :
      ( ( k4_xboole_0(k1_tarski(X15),k1_tarski(X16)) != k1_tarski(X15)
        | X15 != X16 )
      & ( X15 = X16
        | k4_xboole_0(k1_tarski(X15),k1_tarski(X16)) = k1_tarski(X15) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).

fof(c_0_27,plain,(
    ! [X11,X12] : k6_subset_1(X11,X12) = k4_xboole_0(X11,X12) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_28,negated_conjecture,
    ( k9_relat_1(esk3_0,k1_tarski(esk1_1(esk3_0))) = k1_tarski(k1_funct_1(esk3_0,esk1_1(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( k6_subset_1(k1_tarski(k1_funct_1(esk3_0,esk1_1(esk3_0))),k9_relat_1(esk3_0,X1)) = k9_relat_1(esk3_0,k6_subset_1(k1_tarski(esk2_1(esk3_0)),X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) != k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( k9_relat_1(esk3_0,k6_subset_1(k1_tarski(esk2_1(esk3_0)),X1)) = k9_relat_1(esk3_0,k6_subset_1(k1_tarski(esk1_1(esk3_0)),X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_28]),c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( k6_subset_1(k9_relat_1(esk3_0,X1),k1_tarski(k1_funct_1(esk3_0,esk1_1(esk3_0)))) = k9_relat_1(esk3_0,k6_subset_1(X1,k1_tarski(esk2_1(esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_34,plain,
    ( X1 != X2
    | k6_subset_1(k1_tarski(X1),k1_tarski(X2)) != k1_tarski(X1) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( k6_subset_1(k1_tarski(k1_funct_1(esk3_0,esk1_1(esk3_0))),k9_relat_1(esk3_0,X1)) = k9_relat_1(esk3_0,k6_subset_1(k1_tarski(esk1_1(esk3_0)),X1)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( k9_relat_1(esk3_0,k6_subset_1(X1,k1_tarski(esk2_1(esk3_0)))) = k9_relat_1(esk3_0,k6_subset_1(X1,k1_tarski(esk1_1(esk3_0)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_28]),c_0_33])).

cnf(c_0_37,plain,
    ( X1 = X2
    | k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( k6_subset_1(k1_tarski(X1),k1_tarski(X1)) != k1_tarski(X1) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( k6_subset_1(k1_tarski(k1_funct_1(esk3_0,esk1_1(esk3_0))),k1_tarski(k1_funct_1(esk3_0,esk1_1(esk3_0)))) = k9_relat_1(esk3_0,k6_subset_1(k1_tarski(esk1_1(esk3_0)),k1_tarski(esk1_1(esk3_0)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_25]),c_0_36])).

cnf(c_0_40,plain,
    ( X1 = X2
    | k6_subset_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1) ),
    inference(rw,[status(thm)],[c_0_37,c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( k9_relat_1(esk3_0,k6_subset_1(k1_tarski(esk1_1(esk3_0)),k1_tarski(esk1_1(esk3_0)))) != k1_tarski(k1_funct_1(esk3_0,esk1_1(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( k9_relat_1(esk3_0,k6_subset_1(k1_tarski(esk1_1(esk3_0)),k1_tarski(X1))) = k1_tarski(k1_funct_1(esk3_0,esk1_1(esk3_0)))
    | esk2_1(esk3_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_40]),c_0_25])).

cnf(c_0_43,plain,
    ( v2_funct_1(X1)
    | esk1_1(X1) != esk2_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_44,negated_conjecture,
    ( esk2_1(esk3_0) = esk1_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_14]),c_0_11])]),c_0_17]),
    [proof]).

%------------------------------------------------------------------------------
