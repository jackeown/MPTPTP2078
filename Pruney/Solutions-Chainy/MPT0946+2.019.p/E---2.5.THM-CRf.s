%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:44 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 523 expanded)
%              Number of clauses        :   37 ( 201 expanded)
%              Number of leaves         :   14 ( 137 expanded)
%              Depth                    :   13
%              Number of atoms          :  258 (1829 expanded)
%              Number of equality atoms :   48 ( 363 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   33 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_wellord2,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k1_wellord2(X1)
      <=> ( k3_relat_1(X2) = X1
          & ! [X3,X4] :
              ( ( r2_hidden(X3,X1)
                & r2_hidden(X4,X1) )
             => ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> r1_tarski(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(t57_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => ! [X2] :
            ~ ( r2_hidden(X2,k3_relat_1(X1))
              & r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).

fof(t10_wellord2,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,X2)
           => X1 = k1_wellord1(k1_wellord2(X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord2)).

fof(t7_wellord2,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v2_wellord1(k1_wellord2(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).

fof(t11_wellord2,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord2)).

fof(t8_wellord2,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_wellord1(k1_wellord2(X2),X1) = k1_wellord2(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

fof(t50_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r4_wellord1(X1,X2)
           => r4_wellord1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).

fof(t24_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ~ ( ~ r2_hidden(X1,X2)
              & X1 != X2
              & ~ r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(t26_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r1_ordinal1(X1,X2)
            | r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(t40_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v2_wellord1(X2)
       => k3_relat_1(k2_wellord1(X2,k1_wellord1(X2,X1))) = k1_wellord1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_wellord1)).

fof(t19_wellord1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k3_relat_1(k2_wellord1(X3,X2)))
       => ( r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_wellord1)).

fof(d1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k1_wellord1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ( X4 != X2
                & r2_hidden(k4_tarski(X4,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

fof(c_0_14,plain,(
    ! [X28,X29,X30,X31] :
      ( ( k3_relat_1(X29) = X28
        | X29 != k1_wellord2(X28)
        | ~ v1_relat_1(X29) )
      & ( ~ r2_hidden(k4_tarski(X30,X31),X29)
        | r1_tarski(X30,X31)
        | ~ r2_hidden(X30,X28)
        | ~ r2_hidden(X31,X28)
        | X29 != k1_wellord2(X28)
        | ~ v1_relat_1(X29) )
      & ( ~ r1_tarski(X30,X31)
        | r2_hidden(k4_tarski(X30,X31),X29)
        | ~ r2_hidden(X30,X28)
        | ~ r2_hidden(X31,X28)
        | X29 != k1_wellord2(X28)
        | ~ v1_relat_1(X29) )
      & ( r2_hidden(esk2_2(X28,X29),X28)
        | k3_relat_1(X29) != X28
        | X29 = k1_wellord2(X28)
        | ~ v1_relat_1(X29) )
      & ( r2_hidden(esk3_2(X28,X29),X28)
        | k3_relat_1(X29) != X28
        | X29 = k1_wellord2(X28)
        | ~ v1_relat_1(X29) )
      & ( ~ r2_hidden(k4_tarski(esk2_2(X28,X29),esk3_2(X28,X29)),X29)
        | ~ r1_tarski(esk2_2(X28,X29),esk3_2(X28,X29))
        | k3_relat_1(X29) != X28
        | X29 = k1_wellord2(X28)
        | ~ v1_relat_1(X29) )
      & ( r2_hidden(k4_tarski(esk2_2(X28,X29),esk3_2(X28,X29)),X29)
        | r1_tarski(esk2_2(X28,X29),esk3_2(X28,X29))
        | k3_relat_1(X29) != X28
        | X29 = k1_wellord2(X28)
        | ~ v1_relat_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).

fof(c_0_15,plain,(
    ! [X34] : v1_relat_1(k1_wellord2(X34)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_16,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X26)
      | ~ v2_wellord1(X26)
      | ~ r2_hidden(X27,k3_relat_1(X26))
      | ~ r4_wellord1(X26,k2_wellord1(X26,k1_wellord1(X26,X27))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_wellord1])])])).

fof(c_0_17,plain,(
    ! [X35,X36] :
      ( ~ v3_ordinal1(X35)
      | ~ v3_ordinal1(X36)
      | ~ r2_hidden(X35,X36)
      | X35 = k1_wellord1(k1_wellord2(X36),X35) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_wellord2])])])).

cnf(c_0_18,plain,
    ( k3_relat_1(X1) = X2
    | X1 != k1_wellord2(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X37] :
      ( ~ v3_ordinal1(X37)
      | v2_wellord1(k1_wellord2(X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_wellord2])])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))
             => X1 = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t11_wellord2])).

cnf(c_0_22,plain,
    ( ~ v1_relat_1(X1)
    | ~ v2_wellord1(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( X1 = k1_wellord1(k1_wellord2(X2),X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k3_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_18]),c_0_19])])).

cnf(c_0_25,plain,
    ( v2_wellord1(k1_wellord2(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X38,X39] :
      ( ~ r1_tarski(X38,X39)
      | k2_wellord1(k1_wellord2(X39),X38) = k1_wellord2(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_wellord2])])).

fof(c_0_27,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X24)
      | ~ v1_relat_1(X25)
      | ~ r4_wellord1(X24,X25)
      | r4_wellord1(X25,X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_wellord1])])])).

fof(c_0_28,negated_conjecture,
    ( v3_ordinal1(esk4_0)
    & v3_ordinal1(esk5_0)
    & r4_wellord1(k1_wellord2(esk4_0),k1_wellord2(esk5_0))
    & esk4_0 != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

cnf(c_0_29,plain,
    ( ~ r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),X2))
    | ~ r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_19]),c_0_24])]),c_0_25])).

cnf(c_0_30,plain,
    ( k2_wellord1(k1_wellord2(X2),X1) = k1_wellord2(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( r4_wellord1(X2,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r4_wellord1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk4_0),k1_wellord2(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_33,plain,(
    ! [X7,X8] :
      ( ~ v3_ordinal1(X7)
      | ~ v3_ordinal1(X8)
      | r2_hidden(X7,X8)
      | X7 = X8
      | r2_hidden(X8,X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).

cnf(c_0_34,plain,
    ( ~ r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))
    | ~ r2_hidden(X2,X1)
    | ~ r1_tarski(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk5_0),k1_wellord2(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_19]),c_0_19])])).

cnf(c_0_36,negated_conjecture,
    ( v3_ordinal1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( v3_ordinal1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( esk4_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_40,plain,(
    ! [X5,X6] :
      ( ( ~ r1_ordinal1(X5,X6)
        | r1_tarski(X5,X6)
        | ~ v3_ordinal1(X5)
        | ~ v3_ordinal1(X6) )
      & ( ~ r1_tarski(X5,X6)
        | r1_ordinal1(X5,X6)
        | ~ v3_ordinal1(X5)
        | ~ v3_ordinal1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

fof(c_0_41,plain,(
    ! [X9,X10] :
      ( ~ v3_ordinal1(X9)
      | ~ v3_ordinal1(X10)
      | r1_ordinal1(X9,X10)
      | r2_hidden(X10,X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).

fof(c_0_42,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X23)
      | ~ v2_wellord1(X23)
      | k3_relat_1(k2_wellord1(X23,k1_wellord1(X23,X22))) = k1_wellord1(X23,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t40_wellord1])])).

cnf(c_0_43,negated_conjecture,
    ( ~ r2_hidden(esk4_0,esk5_0)
    | ~ r1_tarski(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37])])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0)
    | r2_hidden(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_37])])]),c_0_36])])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,plain,
    ( r1_ordinal1(X1,X2)
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_47,plain,(
    ! [X19,X20,X21] :
      ( ( r2_hidden(X19,k3_relat_1(X21))
        | ~ r2_hidden(X19,k3_relat_1(k2_wellord1(X21,X20)))
        | ~ v1_relat_1(X21) )
      & ( r2_hidden(X19,X20)
        | ~ r2_hidden(X19,k3_relat_1(k2_wellord1(X21,X20)))
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_wellord1])])])).

cnf(c_0_48,plain,
    ( k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X2))) = k1_wellord1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v2_wellord1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0)
    | ~ r1_tarski(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X2)
    | r1_tarski(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

fof(c_0_51,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17] :
      ( ( X14 != X12
        | ~ r2_hidden(X14,X13)
        | X13 != k1_wellord1(X11,X12)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(k4_tarski(X14,X12),X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k1_wellord1(X11,X12)
        | ~ v1_relat_1(X11) )
      & ( X15 = X12
        | ~ r2_hidden(k4_tarski(X15,X12),X11)
        | r2_hidden(X15,X13)
        | X13 != k1_wellord1(X11,X12)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(esk1_3(X11,X16,X17),X17)
        | esk1_3(X11,X16,X17) = X16
        | ~ r2_hidden(k4_tarski(esk1_3(X11,X16,X17),X16),X11)
        | X17 = k1_wellord1(X11,X16)
        | ~ v1_relat_1(X11) )
      & ( esk1_3(X11,X16,X17) != X16
        | r2_hidden(esk1_3(X11,X16,X17),X17)
        | X17 = k1_wellord1(X11,X16)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(k4_tarski(esk1_3(X11,X16,X17),X16),X11)
        | r2_hidden(esk1_3(X11,X16,X17),X17)
        | X17 = k1_wellord1(X11,X16)
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(X1,k3_relat_1(k2_wellord1(X2,X3)))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_53,plain,
    ( k3_relat_1(k2_wellord1(k1_wellord2(X1),X2)) = X2
    | ~ r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_23]),c_0_19])]),c_0_25])).

cnf(c_0_54,negated_conjecture,
    ( ~ r2_hidden(esk5_0,esk4_0)
    | ~ r1_tarski(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_32]),c_0_37]),c_0_36])])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_36]),c_0_37])])).

cnf(c_0_56,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,X3)
    | X3 != k1_wellord1(X4,X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X3,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_24]),c_0_19])])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_tarski(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55])])).

cnf(c_0_59,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_wellord1(X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_56])])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk5_0,X1)
    | ~ r2_hidden(esk4_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_55]),c_0_37])])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_50]),c_0_37]),c_0_36])])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,X1)
    | ~ r2_hidden(X1,X2)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_23]),c_0_19])])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk5_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_36])])).

cnf(c_0_64,negated_conjecture,
    ( ~ r2_hidden(esk5_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_36])])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_63]),c_0_36])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:50:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.50  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 0.20/0.50  # and selection function PSelectUnlessUniqMaxPos.
% 0.20/0.50  #
% 0.20/0.50  # Preprocessing time       : 0.028 s
% 0.20/0.50  # Presaturation interreduction done
% 0.20/0.50  
% 0.20/0.50  # Proof found!
% 0.20/0.50  # SZS status Theorem
% 0.20/0.50  # SZS output start CNFRefutation
% 0.20/0.50  fof(d1_wellord2, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k1_wellord2(X1)<=>(k3_relat_1(X2)=X1&![X3, X4]:((r2_hidden(X3,X1)&r2_hidden(X4,X1))=>(r2_hidden(k4_tarski(X3,X4),X2)<=>r1_tarski(X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 0.20/0.50  fof(dt_k1_wellord2, axiom, ![X1]:v1_relat_1(k1_wellord2(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 0.20/0.50  fof(t57_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v2_wellord1(X1)=>![X2]:~((r2_hidden(X2,k3_relat_1(X1))&r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_wellord1)).
% 0.20/0.50  fof(t10_wellord2, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>X1=k1_wellord1(k1_wellord2(X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_wellord2)).
% 0.20/0.50  fof(t7_wellord2, axiom, ![X1]:(v3_ordinal1(X1)=>v2_wellord1(k1_wellord2(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_wellord2)).
% 0.20/0.50  fof(t11_wellord2, conjecture, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))=>X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_wellord2)).
% 0.20/0.50  fof(t8_wellord2, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_wellord1(k1_wellord2(X2),X1)=k1_wellord2(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_wellord2)).
% 0.20/0.50  fof(t50_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r4_wellord1(X1,X2)=>r4_wellord1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_wellord1)).
% 0.20/0.50  fof(t24_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>~(((~(r2_hidden(X1,X2))&X1!=X2)&~(r2_hidden(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 0.20/0.50  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 0.20/0.50  fof(t26_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r1_ordinal1(X1,X2)|r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 0.20/0.50  fof(t40_wellord1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v2_wellord1(X2)=>k3_relat_1(k2_wellord1(X2,k1_wellord1(X2,X1)))=k1_wellord1(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_wellord1)).
% 0.20/0.50  fof(t19_wellord1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k3_relat_1(k2_wellord1(X3,X2)))=>(r2_hidden(X1,k3_relat_1(X3))&r2_hidden(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_wellord1)).
% 0.20/0.50  fof(d1_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k1_wellord1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4!=X2&r2_hidden(k4_tarski(X4,X2),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord1)).
% 0.20/0.50  fof(c_0_14, plain, ![X28, X29, X30, X31]:(((k3_relat_1(X29)=X28|X29!=k1_wellord2(X28)|~v1_relat_1(X29))&((~r2_hidden(k4_tarski(X30,X31),X29)|r1_tarski(X30,X31)|(~r2_hidden(X30,X28)|~r2_hidden(X31,X28))|X29!=k1_wellord2(X28)|~v1_relat_1(X29))&(~r1_tarski(X30,X31)|r2_hidden(k4_tarski(X30,X31),X29)|(~r2_hidden(X30,X28)|~r2_hidden(X31,X28))|X29!=k1_wellord2(X28)|~v1_relat_1(X29))))&(((r2_hidden(esk2_2(X28,X29),X28)|k3_relat_1(X29)!=X28|X29=k1_wellord2(X28)|~v1_relat_1(X29))&(r2_hidden(esk3_2(X28,X29),X28)|k3_relat_1(X29)!=X28|X29=k1_wellord2(X28)|~v1_relat_1(X29)))&((~r2_hidden(k4_tarski(esk2_2(X28,X29),esk3_2(X28,X29)),X29)|~r1_tarski(esk2_2(X28,X29),esk3_2(X28,X29))|k3_relat_1(X29)!=X28|X29=k1_wellord2(X28)|~v1_relat_1(X29))&(r2_hidden(k4_tarski(esk2_2(X28,X29),esk3_2(X28,X29)),X29)|r1_tarski(esk2_2(X28,X29),esk3_2(X28,X29))|k3_relat_1(X29)!=X28|X29=k1_wellord2(X28)|~v1_relat_1(X29))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).
% 0.20/0.50  fof(c_0_15, plain, ![X34]:v1_relat_1(k1_wellord2(X34)), inference(variable_rename,[status(thm)],[dt_k1_wellord2])).
% 0.20/0.50  fof(c_0_16, plain, ![X26, X27]:(~v1_relat_1(X26)|(~v2_wellord1(X26)|(~r2_hidden(X27,k3_relat_1(X26))|~r4_wellord1(X26,k2_wellord1(X26,k1_wellord1(X26,X27)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_wellord1])])])).
% 0.20/0.50  fof(c_0_17, plain, ![X35, X36]:(~v3_ordinal1(X35)|(~v3_ordinal1(X36)|(~r2_hidden(X35,X36)|X35=k1_wellord1(k1_wellord2(X36),X35)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_wellord2])])])).
% 0.20/0.50  cnf(c_0_18, plain, (k3_relat_1(X1)=X2|X1!=k1_wellord2(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.50  cnf(c_0_19, plain, (v1_relat_1(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.50  fof(c_0_20, plain, ![X37]:(~v3_ordinal1(X37)|v2_wellord1(k1_wellord2(X37))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_wellord2])])).
% 0.20/0.50  fof(c_0_21, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))=>X1=X2)))), inference(assume_negation,[status(cth)],[t11_wellord2])).
% 0.20/0.50  cnf(c_0_22, plain, (~v1_relat_1(X1)|~v2_wellord1(X1)|~r2_hidden(X2,k3_relat_1(X1))|~r4_wellord1(X1,k2_wellord1(X1,k1_wellord1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.50  cnf(c_0_23, plain, (X1=k1_wellord1(k1_wellord2(X2),X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.50  cnf(c_0_24, plain, (k3_relat_1(k1_wellord2(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_18]), c_0_19])])).
% 0.20/0.50  cnf(c_0_25, plain, (v2_wellord1(k1_wellord2(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.50  fof(c_0_26, plain, ![X38, X39]:(~r1_tarski(X38,X39)|k2_wellord1(k1_wellord2(X39),X38)=k1_wellord2(X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_wellord2])])).
% 0.20/0.50  fof(c_0_27, plain, ![X24, X25]:(~v1_relat_1(X24)|(~v1_relat_1(X25)|(~r4_wellord1(X24,X25)|r4_wellord1(X25,X24)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_wellord1])])])).
% 0.20/0.50  fof(c_0_28, negated_conjecture, (v3_ordinal1(esk4_0)&(v3_ordinal1(esk5_0)&(r4_wellord1(k1_wellord2(esk4_0),k1_wellord2(esk5_0))&esk4_0!=esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.20/0.50  cnf(c_0_29, plain, (~r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),X2))|~r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_19]), c_0_24])]), c_0_25])).
% 0.20/0.50  cnf(c_0_30, plain, (k2_wellord1(k1_wellord2(X2),X1)=k1_wellord2(X1)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.50  cnf(c_0_31, plain, (r4_wellord1(X2,X1)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r4_wellord1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.50  cnf(c_0_32, negated_conjecture, (r4_wellord1(k1_wellord2(esk4_0),k1_wellord2(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.50  fof(c_0_33, plain, ![X7, X8]:(~v3_ordinal1(X7)|(~v3_ordinal1(X8)|(r2_hidden(X7,X8)|X7=X8|r2_hidden(X8,X7)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).
% 0.20/0.50  cnf(c_0_34, plain, (~r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))|~r2_hidden(X2,X1)|~r1_tarski(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.50  cnf(c_0_35, negated_conjecture, (r4_wellord1(k1_wellord2(esk5_0),k1_wellord2(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_19]), c_0_19])])).
% 0.20/0.50  cnf(c_0_36, negated_conjecture, (v3_ordinal1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.50  cnf(c_0_37, negated_conjecture, (v3_ordinal1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.50  cnf(c_0_38, negated_conjecture, (esk4_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.50  cnf(c_0_39, plain, (r2_hidden(X1,X2)|X1=X2|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.50  fof(c_0_40, plain, ![X5, X6]:((~r1_ordinal1(X5,X6)|r1_tarski(X5,X6)|(~v3_ordinal1(X5)|~v3_ordinal1(X6)))&(~r1_tarski(X5,X6)|r1_ordinal1(X5,X6)|(~v3_ordinal1(X5)|~v3_ordinal1(X6)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 0.20/0.50  fof(c_0_41, plain, ![X9, X10]:(~v3_ordinal1(X9)|(~v3_ordinal1(X10)|(r1_ordinal1(X9,X10)|r2_hidden(X10,X9)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).
% 0.20/0.50  fof(c_0_42, plain, ![X22, X23]:(~v1_relat_1(X23)|(~v2_wellord1(X23)|k3_relat_1(k2_wellord1(X23,k1_wellord1(X23,X22)))=k1_wellord1(X23,X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t40_wellord1])])).
% 0.20/0.50  cnf(c_0_43, negated_conjecture, (~r2_hidden(esk4_0,esk5_0)|~r1_tarski(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_37])])).
% 0.20/0.50  cnf(c_0_44, negated_conjecture, (r2_hidden(esk5_0,esk4_0)|r2_hidden(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_37])])]), c_0_36])])).
% 0.20/0.50  cnf(c_0_45, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.50  cnf(c_0_46, plain, (r1_ordinal1(X1,X2)|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.50  fof(c_0_47, plain, ![X19, X20, X21]:((r2_hidden(X19,k3_relat_1(X21))|~r2_hidden(X19,k3_relat_1(k2_wellord1(X21,X20)))|~v1_relat_1(X21))&(r2_hidden(X19,X20)|~r2_hidden(X19,k3_relat_1(k2_wellord1(X21,X20)))|~v1_relat_1(X21))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_wellord1])])])).
% 0.20/0.50  cnf(c_0_48, plain, (k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X2)))=k1_wellord1(X1,X2)|~v1_relat_1(X1)|~v2_wellord1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.50  cnf(c_0_49, negated_conjecture, (r2_hidden(esk5_0,esk4_0)|~r1_tarski(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.50  cnf(c_0_50, plain, (r2_hidden(X1,X2)|r1_tarski(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.50  fof(c_0_51, plain, ![X11, X12, X13, X14, X15, X16, X17]:((((X14!=X12|~r2_hidden(X14,X13)|X13!=k1_wellord1(X11,X12)|~v1_relat_1(X11))&(r2_hidden(k4_tarski(X14,X12),X11)|~r2_hidden(X14,X13)|X13!=k1_wellord1(X11,X12)|~v1_relat_1(X11)))&(X15=X12|~r2_hidden(k4_tarski(X15,X12),X11)|r2_hidden(X15,X13)|X13!=k1_wellord1(X11,X12)|~v1_relat_1(X11)))&((~r2_hidden(esk1_3(X11,X16,X17),X17)|(esk1_3(X11,X16,X17)=X16|~r2_hidden(k4_tarski(esk1_3(X11,X16,X17),X16),X11))|X17=k1_wellord1(X11,X16)|~v1_relat_1(X11))&((esk1_3(X11,X16,X17)!=X16|r2_hidden(esk1_3(X11,X16,X17),X17)|X17=k1_wellord1(X11,X16)|~v1_relat_1(X11))&(r2_hidden(k4_tarski(esk1_3(X11,X16,X17),X16),X11)|r2_hidden(esk1_3(X11,X16,X17),X17)|X17=k1_wellord1(X11,X16)|~v1_relat_1(X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).
% 0.20/0.50  cnf(c_0_52, plain, (r2_hidden(X1,k3_relat_1(X2))|~r2_hidden(X1,k3_relat_1(k2_wellord1(X2,X3)))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.50  cnf(c_0_53, plain, (k3_relat_1(k2_wellord1(k1_wellord2(X1),X2))=X2|~r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_23]), c_0_19])]), c_0_25])).
% 0.20/0.50  cnf(c_0_54, negated_conjecture, (~r2_hidden(esk5_0,esk4_0)|~r1_tarski(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_32]), c_0_37]), c_0_36])])).
% 0.20/0.50  cnf(c_0_55, negated_conjecture, (r2_hidden(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_36]), c_0_37])])).
% 0.20/0.50  cnf(c_0_56, plain, (X1!=X2|~r2_hidden(X1,X3)|X3!=k1_wellord1(X4,X2)|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.50  cnf(c_0_57, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r2_hidden(X3,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_24]), c_0_19])])).
% 0.20/0.50  cnf(c_0_58, negated_conjecture, (~r1_tarski(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55])])).
% 0.20/0.50  cnf(c_0_59, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k1_wellord1(X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_56])])).
% 0.20/0.50  cnf(c_0_60, negated_conjecture, (r2_hidden(esk5_0,X1)|~r2_hidden(esk4_0,X1)|~v3_ordinal1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_55]), c_0_37])])).
% 0.20/0.50  cnf(c_0_61, negated_conjecture, (r2_hidden(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_50]), c_0_37]), c_0_36])])).
% 0.20/0.50  cnf(c_0_62, plain, (~r2_hidden(X1,X1)|~r2_hidden(X1,X2)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_23]), c_0_19])])).
% 0.20/0.50  cnf(c_0_63, negated_conjecture, (r2_hidden(esk5_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_36])])).
% 0.20/0.50  cnf(c_0_64, negated_conjecture, (~r2_hidden(esk5_0,X1)|~v3_ordinal1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_36])])).
% 0.20/0.50  cnf(c_0_65, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_63]), c_0_36])]), ['proof']).
% 0.20/0.50  # SZS output end CNFRefutation
% 0.20/0.50  # Proof object total steps             : 66
% 0.20/0.50  # Proof object clause steps            : 37
% 0.20/0.50  # Proof object formula steps           : 29
% 0.20/0.50  # Proof object conjectures             : 19
% 0.20/0.50  # Proof object clause conjectures      : 16
% 0.20/0.50  # Proof object formula conjectures     : 3
% 0.20/0.50  # Proof object initial clauses used    : 17
% 0.20/0.50  # Proof object initial formulas used   : 14
% 0.20/0.50  # Proof object generating inferences   : 17
% 0.20/0.50  # Proof object simplifying inferences  : 47
% 0.20/0.50  # Training examples: 0 positive, 0 negative
% 0.20/0.50  # Parsed axioms                        : 14
% 0.20/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.50  # Initial clauses                      : 30
% 0.20/0.50  # Removed in clause preprocessing      : 0
% 0.20/0.50  # Initial clauses in saturation        : 30
% 0.20/0.50  # Processed clauses                    : 395
% 0.20/0.50  # ...of these trivial                  : 0
% 0.20/0.50  # ...subsumed                          : 165
% 0.20/0.50  # ...remaining for further processing  : 230
% 0.20/0.50  # Other redundant clauses eliminated   : 30
% 0.20/0.50  # Clauses deleted for lack of memory   : 0
% 0.20/0.50  # Backward-subsumed                    : 11
% 0.20/0.50  # Backward-rewritten                   : 8
% 0.20/0.50  # Generated clauses                    : 5228
% 0.20/0.50  # ...of the previous two non-trivial   : 5140
% 0.20/0.50  # Contextual simplify-reflections      : 2
% 0.20/0.50  # Paramodulations                      : 5139
% 0.20/0.50  # Factorizations                       : 60
% 0.20/0.50  # Equation resolutions                 : 30
% 0.20/0.50  # Propositional unsat checks           : 0
% 0.20/0.50  #    Propositional check models        : 0
% 0.20/0.50  #    Propositional check unsatisfiable : 0
% 0.20/0.50  #    Propositional clauses             : 0
% 0.20/0.50  #    Propositional clauses after purity: 0
% 0.20/0.50  #    Propositional unsat core size     : 0
% 0.20/0.50  #    Propositional preprocessing time  : 0.000
% 0.20/0.50  #    Propositional encoding time       : 0.000
% 0.20/0.50  #    Propositional solver time         : 0.000
% 0.20/0.50  #    Success case prop preproc time    : 0.000
% 0.20/0.50  #    Success case prop encoding time   : 0.000
% 0.20/0.50  #    Success case prop solver time     : 0.000
% 0.20/0.50  # Current number of processed clauses  : 171
% 0.20/0.50  #    Positive orientable unit clauses  : 9
% 0.20/0.50  #    Positive unorientable unit clauses: 0
% 0.20/0.50  #    Negative unit clauses             : 3
% 0.20/0.50  #    Non-unit-clauses                  : 159
% 0.20/0.50  # Current number of unprocessed clauses: 4779
% 0.20/0.50  # ...number of literals in the above   : 40481
% 0.20/0.50  # Current number of archived formulas  : 0
% 0.20/0.50  # Current number of archived clauses   : 49
% 0.20/0.50  # Clause-clause subsumption calls (NU) : 14404
% 0.20/0.50  # Rec. Clause-clause subsumption calls : 1865
% 0.20/0.50  # Non-unit clause-clause subsumptions  : 148
% 0.20/0.50  # Unit Clause-clause subsumption calls : 197
% 0.20/0.50  # Rewrite failures with RHS unbound    : 0
% 0.20/0.50  # BW rewrite match attempts            : 3
% 0.20/0.50  # BW rewrite match successes           : 3
% 0.20/0.50  # Condensation attempts                : 0
% 0.20/0.50  # Condensation successes               : 0
% 0.20/0.50  # Termbank termtop insertions          : 119666
% 0.20/0.50  
% 0.20/0.50  # -------------------------------------------------
% 0.20/0.50  # User time                : 0.153 s
% 0.20/0.50  # System time              : 0.006 s
% 0.20/0.50  # Total time               : 0.159 s
% 0.20/0.50  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
