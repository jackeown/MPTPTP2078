%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : wellord2__t4_wellord2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:17 EDT 2019

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 493 expanded)
%              Number of clauses        :   43 ( 213 expanded)
%              Number of leaves         :   10 ( 131 expanded)
%              Depth                    :   21
%              Number of atoms          :  214 (2109 expanded)
%              Number of equality atoms :   21 ( 440 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   33 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d6_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r6_relat_2(X1,X2)
        <=> ! [X3,X4] :
              ~ ( r2_hidden(X3,X2)
                & r2_hidden(X4,X2)
                & X3 != X4
                & ~ r2_hidden(k4_tarski(X3,X4),X1)
                & ~ r2_hidden(k4_tarski(X4,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t4_wellord2.p',d6_relat_2)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t4_wellord2.p',dt_k1_wellord2)).

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
    file('/export/starexec/sandbox2/benchmark/wellord2__t4_wellord2.p',d1_wellord2)).

fof(t4_wellord2,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v6_relat_2(k1_wellord2(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t4_wellord2.p',t4_wellord2)).

fof(d14_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v6_relat_2(X1)
      <=> r6_relat_2(X1,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t4_wellord2.p',d14_relat_2)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t4_wellord2.p',t1_subset)).

fof(cc5_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,X1)
         => v3_ordinal1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t4_wellord2.p',cc5_ordinal1)).

fof(connectedness_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
        | r1_ordinal1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t4_wellord2.p',connectedness_r1_ordinal1)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t4_wellord2.p',redefinition_r1_ordinal1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t4_wellord2.p',t3_subset)).

fof(c_0_10,plain,(
    ! [X19,X20,X21,X22,X23] :
      ( ( ~ r6_relat_2(X19,X20)
        | ~ r2_hidden(X21,X20)
        | ~ r2_hidden(X22,X20)
        | X21 = X22
        | r2_hidden(k4_tarski(X21,X22),X19)
        | r2_hidden(k4_tarski(X22,X21),X19)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(esk4_2(X19,X23),X23)
        | r6_relat_2(X19,X23)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(esk5_2(X19,X23),X23)
        | r6_relat_2(X19,X23)
        | ~ v1_relat_1(X19) )
      & ( esk4_2(X19,X23) != esk5_2(X19,X23)
        | r6_relat_2(X19,X23)
        | ~ v1_relat_1(X19) )
      & ( ~ r2_hidden(k4_tarski(esk4_2(X19,X23),esk5_2(X19,X23)),X19)
        | r6_relat_2(X19,X23)
        | ~ v1_relat_1(X19) )
      & ( ~ r2_hidden(k4_tarski(esk5_2(X19,X23),esk4_2(X19,X23)),X19)
        | r6_relat_2(X19,X23)
        | ~ v1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d6_relat_2])])])])])])])).

fof(c_0_11,plain,(
    ! [X26] : v1_relat_1(k1_wellord2(X26)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_12,plain,(
    ! [X13,X14,X15,X16] :
      ( ( k3_relat_1(X14) = X13
        | X14 != k1_wellord2(X13)
        | ~ v1_relat_1(X14) )
      & ( ~ r2_hidden(k4_tarski(X15,X16),X14)
        | r1_tarski(X15,X16)
        | ~ r2_hidden(X15,X13)
        | ~ r2_hidden(X16,X13)
        | X14 != k1_wellord2(X13)
        | ~ v1_relat_1(X14) )
      & ( ~ r1_tarski(X15,X16)
        | r2_hidden(k4_tarski(X15,X16),X14)
        | ~ r2_hidden(X15,X13)
        | ~ r2_hidden(X16,X13)
        | X14 != k1_wellord2(X13)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(esk2_2(X13,X14),X13)
        | k3_relat_1(X14) != X13
        | X14 = k1_wellord2(X13)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(esk3_2(X13,X14),X13)
        | k3_relat_1(X14) != X13
        | X14 = k1_wellord2(X13)
        | ~ v1_relat_1(X14) )
      & ( ~ r2_hidden(k4_tarski(esk2_2(X13,X14),esk3_2(X13,X14)),X14)
        | ~ r1_tarski(esk2_2(X13,X14),esk3_2(X13,X14))
        | k3_relat_1(X14) != X13
        | X14 = k1_wellord2(X13)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(k4_tarski(esk2_2(X13,X14),esk3_2(X13,X14)),X14)
        | r1_tarski(esk2_2(X13,X14),esk3_2(X13,X14))
        | k3_relat_1(X14) != X13
        | X14 = k1_wellord2(X13)
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => v6_relat_2(k1_wellord2(X1)) ) ),
    inference(assume_negation,[status(cth)],[t4_wellord2])).

fof(c_0_14,plain,(
    ! [X12] :
      ( ( ~ v6_relat_2(X12)
        | r6_relat_2(X12,k3_relat_1(X12))
        | ~ v1_relat_1(X12) )
      & ( ~ r6_relat_2(X12,k3_relat_1(X12))
        | v6_relat_2(X12)
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_2])])])).

cnf(c_0_15,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | r6_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k3_relat_1(X1) = X2
    | X1 != k1_wellord2(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,negated_conjecture,
    ( v3_ordinal1(esk1_0)
    & ~ v6_relat_2(k1_wellord2(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_19,plain,
    ( v6_relat_2(X1)
    | ~ r6_relat_2(X1,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( r6_relat_2(k1_wellord2(X1),X2)
    | r2_hidden(esk4_2(k1_wellord2(X1),X2),X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( k3_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_17]),c_0_16])])).

cnf(c_0_22,plain,
    ( r2_hidden(esk5_2(X1,X2),X2)
    | r6_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_23,plain,(
    ! [X35,X36] :
      ( ~ r2_hidden(X35,X36)
      | m1_subset_1(X35,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_24,negated_conjecture,
    ( ~ v6_relat_2(k1_wellord2(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( r2_hidden(esk4_2(k1_wellord2(X1),X1),X1)
    | v6_relat_2(k1_wellord2(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_21]),c_0_16])])).

cnf(c_0_26,plain,
    ( r6_relat_2(k1_wellord2(X1),X2)
    | r2_hidden(esk5_2(k1_wellord2(X1),X2),X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_16])).

fof(c_0_27,plain,(
    ! [X52,X53] :
      ( ~ v3_ordinal1(X52)
      | ~ m1_subset_1(X53,X52)
      | v3_ordinal1(X53) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc5_ordinal1])])])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk4_2(k1_wellord2(esk1_0),esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( r2_hidden(esk5_2(k1_wellord2(X1),X1),X1)
    | v6_relat_2(k1_wellord2(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_26]),c_0_21]),c_0_21]),c_0_16])])).

fof(c_0_31,plain,(
    ! [X10,X11] :
      ( ~ v3_ordinal1(X10)
      | ~ v3_ordinal1(X11)
      | r1_ordinal1(X10,X11)
      | r1_ordinal1(X11,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[connectedness_r1_ordinal1])])).

cnf(c_0_32,plain,
    ( v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk4_2(k1_wellord2(esk1_0),esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( v3_ordinal1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk5_2(k1_wellord2(esk1_0),esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_30])).

cnf(c_0_36,plain,
    ( r1_ordinal1(X1,X2)
    | r1_ordinal1(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( v3_ordinal1(esk4_2(k1_wellord2(esk1_0),esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk5_2(k1_wellord2(esk1_0),esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_35])).

fof(c_0_39,plain,(
    ! [X30,X31] :
      ( ( ~ r1_ordinal1(X30,X31)
        | r1_tarski(X30,X31)
        | ~ v3_ordinal1(X30)
        | ~ v3_ordinal1(X31) )
      & ( ~ r1_tarski(X30,X31)
        | r1_ordinal1(X30,X31)
        | ~ v3_ordinal1(X30)
        | ~ v3_ordinal1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_40,negated_conjecture,
    ( r1_ordinal1(X1,esk4_2(k1_wellord2(esk1_0),esk1_0))
    | r1_ordinal1(esk4_2(k1_wellord2(esk1_0),esk1_0),X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( v3_ordinal1(esk5_2(k1_wellord2(esk1_0),esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_38]),c_0_34])])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( r1_ordinal1(esk4_2(k1_wellord2(esk1_0),esk1_0),esk5_2(k1_wellord2(esk1_0),esk1_0))
    | r1_ordinal1(esk5_2(k1_wellord2(esk1_0),esk1_0),esk4_2(k1_wellord2(esk1_0),esk1_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_44,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X1,X4)
    | ~ r2_hidden(X2,X4)
    | X3 != k1_wellord2(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(esk5_2(k1_wellord2(esk1_0),esk1_0),esk4_2(k1_wellord2(esk1_0),esk1_0))
    | r1_ordinal1(esk4_2(k1_wellord2(esk1_0),esk1_0),esk5_2(k1_wellord2(esk1_0),esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_37]),c_0_41])])).

cnf(c_0_46,plain,
    ( r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_44]),c_0_16])])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(esk5_2(k1_wellord2(esk1_0),esk1_0),esk4_2(k1_wellord2(esk1_0),esk1_0))
    | r1_tarski(esk4_2(k1_wellord2(esk1_0),esk1_0),esk5_2(k1_wellord2(esk1_0),esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_45]),c_0_41]),c_0_37])])).

fof(c_0_48,plain,(
    ! [X39,X40] :
      ( ( ~ m1_subset_1(X39,k1_zfmisc_1(X40))
        | r1_tarski(X39,X40) )
      & ( ~ r1_tarski(X39,X40)
        | m1_subset_1(X39,k1_zfmisc_1(X40)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(esk4_2(k1_wellord2(esk1_0),esk1_0),esk5_2(k1_wellord2(esk1_0),esk1_0))
    | r2_hidden(k4_tarski(esk5_2(k1_wellord2(esk1_0),esk1_0),esk4_2(k1_wellord2(esk1_0),esk1_0)),k1_wellord2(X1))
    | ~ r2_hidden(esk4_2(k1_wellord2(esk1_0),esk1_0),X1)
    | ~ r2_hidden(esk5_2(k1_wellord2(esk1_0),esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_50,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk4_2(k1_wellord2(esk1_0),esk1_0),esk5_2(k1_wellord2(esk1_0),esk1_0))
    | r2_hidden(k4_tarski(esk5_2(k1_wellord2(esk1_0),esk1_0),esk4_2(k1_wellord2(esk1_0),esk1_0)),k1_wellord2(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_29]),c_0_35])])).

cnf(c_0_52,plain,
    ( r6_relat_2(X1,X2)
    | ~ r2_hidden(k4_tarski(esk5_2(X1,X2),esk4_2(X1,X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk4_2(k1_wellord2(esk1_0),esk1_0),k1_zfmisc_1(esk5_2(k1_wellord2(esk1_0),esk1_0)))
    | r2_hidden(k4_tarski(esk5_2(k1_wellord2(esk1_0),esk1_0),esk4_2(k1_wellord2(esk1_0),esk1_0)),k1_wellord2(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_54,plain,
    ( v6_relat_2(k1_wellord2(X1))
    | ~ r6_relat_2(k1_wellord2(X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_21]),c_0_16])])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk4_2(k1_wellord2(esk1_0),esk1_0),k1_zfmisc_1(esk5_2(k1_wellord2(esk1_0),esk1_0)))
    | r6_relat_2(k1_wellord2(esk1_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_16])])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk4_2(k1_wellord2(esk1_0),esk1_0),k1_zfmisc_1(esk5_2(k1_wellord2(esk1_0),esk1_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_24])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(esk4_2(k1_wellord2(esk1_0),esk1_0),esk5_2(k1_wellord2(esk1_0),esk1_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_2(k1_wellord2(esk1_0),esk1_0),esk5_2(k1_wellord2(esk1_0),esk1_0)),k1_wellord2(X1))
    | ~ r2_hidden(esk5_2(k1_wellord2(esk1_0),esk1_0),X1)
    | ~ r2_hidden(esk4_2(k1_wellord2(esk1_0),esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_58])).

cnf(c_0_60,plain,
    ( r6_relat_2(X1,X2)
    | ~ r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_2(k1_wellord2(esk1_0),esk1_0),esk5_2(k1_wellord2(esk1_0),esk1_0)),k1_wellord2(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_35]),c_0_29])])).

cnf(c_0_62,negated_conjecture,
    ( r6_relat_2(k1_wellord2(esk1_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_16])])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_62]),c_0_24]),
    [proof]).
%------------------------------------------------------------------------------
