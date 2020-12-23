%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : ordinal1__t37_ordinal1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:26 EDT 2019

% Result     : Theorem 1.08s
% Output     : CNFRefutation 1.08s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 329 expanded)
%              Number of clauses        :   41 ( 147 expanded)
%              Number of leaves         :   11 (  79 expanded)
%              Depth                    :   14
%              Number of atoms          :  186 (1031 expanded)
%              Number of equality atoms :   12 (  27 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t37_ordinal1,conjecture,(
    ! [X1] :
      ~ ! [X2] :
          ( r2_hidden(X2,X1)
        <=> v3_ordinal1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t37_ordinal1.p',t37_ordinal1)).

fof(t23_ordinal1,axiom,(
    ! [X1,X2] :
      ( v3_ordinal1(X2)
     => ( r2_hidden(X1,X2)
       => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t37_ordinal1.p',t23_ordinal1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t37_ordinal1.p',d3_tarski)).

fof(cc2_ordinal1,axiom,(
    ! [X1] :
      ( ( v1_ordinal1(X1)
        & v2_ordinal1(X1) )
     => v3_ordinal1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t37_ordinal1.p',cc2_ordinal1)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t37_ordinal1.p',antisymmetry_r2_hidden)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t37_ordinal1.p',t7_boole)).

fof(d2_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t37_ordinal1.p',d2_ordinal1)).

fof(d3_ordinal1,axiom,(
    ! [X1] :
      ( v2_ordinal1(X1)
    <=> ! [X2,X3] :
          ~ ( r2_hidden(X2,X1)
            & r2_hidden(X3,X1)
            & ~ r2_hidden(X2,X3)
            & X2 != X3
            & ~ r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t37_ordinal1.p',d3_ordinal1)).

fof(t24_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ~ ( ~ r2_hidden(X1,X2)
              & X1 != X2
              & ~ r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t37_ordinal1.p',t24_ordinal1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t37_ordinal1.p',t1_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t37_ordinal1.p',t2_subset)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ~ ! [X2] :
            ( r2_hidden(X2,X1)
          <=> v3_ordinal1(X2) ) ),
    inference(assume_negation,[status(cth)],[t37_ordinal1])).

fof(c_0_12,plain,(
    ! [X28,X29] :
      ( ~ v3_ordinal1(X29)
      | ~ r2_hidden(X28,X29)
      | v3_ordinal1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).

fof(c_0_13,plain,(
    ! [X18,X19,X20,X21,X22] :
      ( ( ~ r1_tarski(X18,X19)
        | ~ r2_hidden(X20,X18)
        | r2_hidden(X20,X19) )
      & ( r2_hidden(esk5_2(X21,X22),X21)
        | r1_tarski(X21,X22) )
      & ( ~ r2_hidden(esk5_2(X21,X22),X22)
        | r1_tarski(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_14,negated_conjecture,(
    ! [X5] :
      ( ( ~ r2_hidden(X5,esk1_0)
        | v3_ordinal1(X5) )
      & ( ~ v3_ordinal1(X5)
        | r2_hidden(X5,esk1_0) ) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_15,plain,(
    ! [X47] :
      ( ~ v1_ordinal1(X47)
      | ~ v2_ordinal1(X47)
      | v3_ordinal1(X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_ordinal1])])).

cnf(c_0_16,plain,
    ( v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r2_hidden(esk5_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,X7)
      | ~ r2_hidden(X7,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(X1,esk1_0)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( v3_ordinal1(X1)
    | ~ v1_ordinal1(X1)
    | ~ v2_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | v3_ordinal1(esk5_2(X1,X2))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(X1,esk1_0)
    | ~ v2_ordinal1(X1)
    | ~ v1_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_24,plain,(
    ! [X43,X44] :
      ( ~ r2_hidden(X43,X44)
      | ~ v1_xboole_0(X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_25,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v1_ordinal1(X8)
        | ~ r2_hidden(X9,X8)
        | r1_tarski(X9,X8) )
      & ( r2_hidden(esk2_1(X10),X10)
        | v1_ordinal1(X10) )
      & ( ~ r1_tarski(esk2_1(X10),X10)
        | v1_ordinal1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(X1,X2)
    | r2_hidden(esk5_2(X1,X2),esk1_0)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_ordinal1(X1)
    | ~ v1_ordinal1(X1)
    | ~ r2_hidden(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | v1_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_31,plain,(
    ! [X12,X13,X14,X15] :
      ( ( ~ v2_ordinal1(X12)
        | ~ r2_hidden(X13,X12)
        | ~ r2_hidden(X14,X12)
        | r2_hidden(X13,X14)
        | X13 = X14
        | r2_hidden(X14,X13) )
      & ( r2_hidden(esk3_1(X15),X15)
        | v2_ordinal1(X15) )
      & ( r2_hidden(esk4_1(X15),X15)
        | v2_ordinal1(X15) )
      & ( ~ r2_hidden(esk3_1(X15),esk4_1(X15))
        | v2_ordinal1(X15) )
      & ( esk3_1(X15) != esk4_1(X15)
        | v2_ordinal1(X15) )
      & ( ~ r2_hidden(esk4_1(X15),esk3_1(X15))
        | v2_ordinal1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_ordinal1])])])])])])])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk5_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(X1,X2)
    | r2_hidden(esk5_2(X1,X2),esk1_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_34,plain,(
    ! [X30,X31] :
      ( ~ v3_ordinal1(X30)
      | ~ v3_ordinal1(X31)
      | r2_hidden(X30,X31)
      | X30 = X31
      | r2_hidden(X31,X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).

cnf(c_0_35,negated_conjecture,
    ( ~ v2_ordinal1(esk1_0)
    | ~ v1_ordinal1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_23])).

cnf(c_0_36,plain,
    ( v1_ordinal1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | v2_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(X1,esk1_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( v1_ordinal1(X1)
    | ~ r1_tarski(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_40,plain,(
    ! [X26,X27] :
      ( ~ r2_hidden(X26,X27)
      | m1_subset_1(X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_42,plain,(
    ! [X32,X33] :
      ( ~ m1_subset_1(X32,X33)
      | v1_xboole_0(X33)
      | r2_hidden(X32,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_43,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    | ~ v2_ordinal1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_44,plain,
    ( v2_ordinal1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( v1_ordinal1(esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_30]),c_0_39])).

cnf(c_0_46,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( X1 = X2
    | r2_hidden(X1,X2)
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_27])).

cnf(c_0_48,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( ~ v2_ordinal1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_45])])).

cnf(c_0_51,plain,
    ( m1_subset_1(esk3_1(X1),X1)
    | v2_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_37])).

cnf(c_0_52,negated_conjecture,
    ( X1 = X2
    | r2_hidden(X2,X1)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,esk1_0)
    | ~ v3_ordinal1(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk3_1(esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( esk3_1(esk1_0) = X1
    | r2_hidden(esk3_1(esk1_0),X1)
    | r2_hidden(X1,esk3_1(esk1_0))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_55,plain,
    ( v2_ordinal1(X1)
    | esk3_1(X1) != esk4_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_56,negated_conjecture,
    ( esk3_1(esk1_0) = X1
    | r2_hidden(X1,esk3_1(esk1_0))
    | r2_hidden(esk3_1(esk1_0),X1)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_27])).

cnf(c_0_57,plain,
    ( r2_hidden(esk4_1(X1),X1)
    | v2_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_58,negated_conjecture,
    ( esk3_1(esk1_0) != esk4_1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_55])).

cnf(c_0_59,plain,
    ( v2_ordinal1(X1)
    | ~ r2_hidden(esk3_1(X1),esk4_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk3_1(esk1_0),esk4_1(esk1_0))
    | r2_hidden(esk4_1(esk1_0),esk3_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),c_0_50])).

cnf(c_0_61,plain,
    ( v2_ordinal1(X1)
    | ~ r2_hidden(esk4_1(X1),esk3_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk4_1(esk1_0),esk3_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_50])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_50]),
    [proof]).
%------------------------------------------------------------------------------
