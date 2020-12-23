%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : wellord1__t32_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:13 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   39 (  55 expanded)
%              Number of clauses        :   22 (  22 expanded)
%              Number of leaves         :    8 (  15 expanded)
%              Depth                    :    9
%              Number of atoms          :  153 ( 316 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   22 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
      <=> ( v1_relat_2(X1)
          & v8_relat_2(X1)
          & v4_relat_2(X1)
          & v6_relat_2(X1)
          & v1_wellord1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t32_wellord1.p',d4_wellord1)).

fof(t31_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v1_wellord1(X2)
       => v1_wellord1(k2_wellord1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t32_wellord1.p',t31_wellord1)).

fof(dt_k2_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k2_wellord1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t32_wellord1.p',dt_k2_wellord1)).

fof(t23_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v6_relat_2(X2)
       => v6_relat_2(k2_wellord1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t32_wellord1.p',t23_wellord1)).

fof(t25_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_2(X2)
       => v4_relat_2(k2_wellord1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t32_wellord1.p',t25_wellord1)).

fof(t24_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v8_relat_2(X2)
       => v8_relat_2(k2_wellord1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t32_wellord1.p',t24_wellord1)).

fof(t22_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v1_relat_2(X2)
       => v1_relat_2(k2_wellord1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t32_wellord1.p',t22_wellord1)).

fof(t32_wellord1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v2_wellord1(X2)
       => v2_wellord1(k2_wellord1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t32_wellord1.p',t32_wellord1)).

fof(c_0_8,plain,(
    ! [X7] :
      ( ( v1_relat_2(X7)
        | ~ v2_wellord1(X7)
        | ~ v1_relat_1(X7) )
      & ( v8_relat_2(X7)
        | ~ v2_wellord1(X7)
        | ~ v1_relat_1(X7) )
      & ( v4_relat_2(X7)
        | ~ v2_wellord1(X7)
        | ~ v1_relat_1(X7) )
      & ( v6_relat_2(X7)
        | ~ v2_wellord1(X7)
        | ~ v1_relat_1(X7) )
      & ( v1_wellord1(X7)
        | ~ v2_wellord1(X7)
        | ~ v1_relat_1(X7) )
      & ( ~ v1_relat_2(X7)
        | ~ v8_relat_2(X7)
        | ~ v4_relat_2(X7)
        | ~ v6_relat_2(X7)
        | ~ v1_wellord1(X7)
        | v2_wellord1(X7)
        | ~ v1_relat_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).

fof(c_0_9,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X20)
      | ~ v1_wellord1(X20)
      | v1_wellord1(k2_wellord1(X20,X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_wellord1])])).

fof(c_0_10,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(X8)
      | v1_relat_1(k2_wellord1(X8,X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_wellord1])])).

cnf(c_0_11,plain,
    ( v2_wellord1(X1)
    | ~ v1_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ v4_relat_2(X1)
    | ~ v6_relat_2(X1)
    | ~ v1_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( v1_wellord1(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_wellord1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( v1_relat_1(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X14)
      | ~ v6_relat_2(X14)
      | v6_relat_2(k2_wellord1(X14,X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_wellord1])])).

cnf(c_0_15,plain,
    ( v2_wellord1(k2_wellord1(X1,X2))
    | ~ v1_wellord1(X1)
    | ~ v6_relat_2(k2_wellord1(X1,X2))
    | ~ v4_relat_2(k2_wellord1(X1,X2))
    | ~ v8_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])).

cnf(c_0_16,plain,
    ( v6_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v6_relat_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_17,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X18)
      | ~ v4_relat_2(X18)
      | v4_relat_2(k2_wellord1(X18,X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_wellord1])])).

cnf(c_0_18,plain,
    ( v2_wellord1(k2_wellord1(X1,X2))
    | ~ v1_wellord1(X1)
    | ~ v6_relat_2(X1)
    | ~ v4_relat_2(k2_wellord1(X1,X2))
    | ~ v8_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,plain,
    ( v4_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v4_relat_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_20,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X16)
      | ~ v8_relat_2(X16)
      | v8_relat_2(k2_wellord1(X16,X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_wellord1])])).

cnf(c_0_21,plain,
    ( v2_wellord1(k2_wellord1(X1,X2))
    | ~ v1_wellord1(X1)
    | ~ v6_relat_2(X1)
    | ~ v4_relat_2(X1)
    | ~ v8_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,plain,
    ( v8_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v8_relat_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_23,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X12)
      | ~ v1_relat_2(X12)
      | v1_relat_2(k2_wellord1(X12,X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_wellord1])])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( v2_wellord1(X2)
         => v2_wellord1(k2_wellord1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t32_wellord1])).

cnf(c_0_25,plain,
    ( v2_wellord1(k2_wellord1(X1,X2))
    | ~ v1_wellord1(X1)
    | ~ v6_relat_2(X1)
    | ~ v4_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ v1_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,plain,
    ( v1_relat_2(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_27,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v2_wellord1(esk2_0)
    & ~ v2_wellord1(k2_wellord1(esk2_0,esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

cnf(c_0_28,plain,
    ( v2_wellord1(k2_wellord1(X1,X2))
    | ~ v1_wellord1(X1)
    | ~ v6_relat_2(X1)
    | ~ v4_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ v1_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_29,plain,
    ( v1_wellord1(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_30,plain,
    ( v1_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_31,plain,
    ( v8_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_32,plain,
    ( v4_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_33,plain,
    ( v6_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_34,negated_conjecture,
    ( ~ v2_wellord1(k2_wellord1(esk2_0,esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( v2_wellord1(k2_wellord1(X1,X2))
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( v2_wellord1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37])]),
    [proof]).
%------------------------------------------------------------------------------
