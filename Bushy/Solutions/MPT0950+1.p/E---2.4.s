%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : wellord2__t17_wellord2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:16 EDT 2019

% Result     : Theorem 159.63s
% Output     : CNFRefutation 159.63s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 803 expanded)
%              Number of clauses        :   77 ( 336 expanded)
%              Number of leaves         :   20 ( 206 expanded)
%              Depth                    :   22
%              Number of atoms          :  361 (2369 expanded)
%              Number of equality atoms :   43 ( 245 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   33 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t17_wellord2,conjecture,(
    ! [X1,X2] :
      ( v3_ordinal1(X2)
     => ( r1_tarski(X1,X2)
       => r1_ordinal1(k2_wellord2(k1_wellord2(X1)),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t17_wellord2.p',t17_wellord2)).

fof(connectedness_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
        | r1_ordinal1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t17_wellord2.p',connectedness_r1_ordinal1)).

fof(dt_k2_wellord2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => v3_ordinal1(k2_wellord2(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t17_wellord2.p',dt_k2_wellord2)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t17_wellord2.p',dt_k1_wellord2)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t17_wellord2.p',redefinition_r1_ordinal1)).

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
    file('/export/starexec/sandbox2/benchmark/wellord2__t17_wellord2.p',d1_wellord2)).

fof(t9_wellord2,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( r1_tarski(X2,X1)
         => v2_wellord1(k1_wellord2(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t17_wellord2.p',t9_wellord2)).

fof(t64_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ~ ( r1_tarski(X1,k3_relat_1(X2))
          & v2_wellord1(X2)
          & ~ r4_wellord1(X2,k2_wellord1(X2,X1))
          & ! [X3] :
              ~ ( r2_hidden(X3,k3_relat_1(X2))
                & r4_wellord1(k2_wellord1(X2,k1_wellord1(X2,X3)),k2_wellord1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t17_wellord2.p',t64_wellord1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t17_wellord2.p',t7_boole)).

fof(t8_wellord2,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_wellord1(k1_wellord2(X2),X1) = k1_wellord2(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t17_wellord2.p',t8_wellord2)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t17_wellord2.p',t8_boole)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t17_wellord2.p',t3_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t17_wellord2.p',t2_subset)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t17_wellord2.p',t1_subset)).

fof(cc5_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,X1)
         => v3_ordinal1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t17_wellord2.p',cc5_ordinal1)).

fof(d2_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t17_wellord2.p',d2_ordinal1)).

fof(t10_wellord2,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,X2)
           => X1 = k1_wellord1(k1_wellord2(X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t17_wellord2.p',t10_wellord2)).

fof(cc1_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v1_ordinal1(X1)
        & v2_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t17_wellord2.p',cc1_ordinal1)).

fof(t50_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r4_wellord1(X1,X2)
           => r4_wellord1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t17_wellord2.p',t50_wellord1)).

fof(d2_wellord2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( X2 = k2_wellord2(X1)
            <=> r4_wellord1(X1,k1_wellord2(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t17_wellord2.p',d2_wellord2)).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v3_ordinal1(X2)
       => ( r1_tarski(X1,X2)
         => r1_ordinal1(k2_wellord2(k1_wellord2(X1)),X2) ) ) ),
    inference(assume_negation,[status(cth)],[t17_wellord2])).

fof(c_0_21,negated_conjecture,
    ( v3_ordinal1(esk2_0)
    & r1_tarski(esk1_0,esk2_0)
    & ~ r1_ordinal1(k2_wellord2(k1_wellord2(esk1_0)),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_22,plain,(
    ! [X13,X14] :
      ( ~ v3_ordinal1(X13)
      | ~ v3_ordinal1(X14)
      | r1_ordinal1(X13,X14)
      | r1_ordinal1(X14,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[connectedness_r1_ordinal1])])).

cnf(c_0_23,negated_conjecture,
    ( ~ r1_ordinal1(k2_wellord2(k1_wellord2(esk1_0)),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_24,plain,
    ( r1_ordinal1(X1,X2)
    | r1_ordinal1(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( v3_ordinal1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_26,plain,(
    ! [X30] :
      ( ~ v1_relat_1(X30)
      | v3_ordinal1(k2_wellord2(X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_wellord2])])).

fof(c_0_27,plain,(
    ! [X27] : v1_relat_1(k1_wellord2(X27)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_28,plain,(
    ! [X35,X36] :
      ( ( ~ r1_ordinal1(X35,X36)
        | r1_tarski(X35,X36)
        | ~ v3_ordinal1(X35)
        | ~ v3_ordinal1(X36) )
      & ( ~ r1_tarski(X35,X36)
        | r1_ordinal1(X35,X36)
        | ~ v3_ordinal1(X35)
        | ~ v3_ordinal1(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_29,negated_conjecture,
    ( r1_ordinal1(esk2_0,k2_wellord2(k1_wellord2(esk1_0)))
    | ~ v3_ordinal1(k2_wellord2(k1_wellord2(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_30,plain,
    ( v3_ordinal1(k2_wellord2(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( r1_ordinal1(esk2_0,k2_wellord2(k1_wellord2(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])])).

fof(c_0_34,plain,(
    ! [X15,X16,X17,X18] :
      ( ( k3_relat_1(X16) = X15
        | X16 != k1_wellord2(X15)
        | ~ v1_relat_1(X16) )
      & ( ~ r2_hidden(k4_tarski(X17,X18),X16)
        | r1_tarski(X17,X18)
        | ~ r2_hidden(X17,X15)
        | ~ r2_hidden(X18,X15)
        | X16 != k1_wellord2(X15)
        | ~ v1_relat_1(X16) )
      & ( ~ r1_tarski(X17,X18)
        | r2_hidden(k4_tarski(X17,X18),X16)
        | ~ r2_hidden(X17,X15)
        | ~ r2_hidden(X18,X15)
        | X16 != k1_wellord2(X15)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(esk3_2(X15,X16),X15)
        | k3_relat_1(X16) != X15
        | X16 = k1_wellord2(X15)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(esk4_2(X15,X16),X15)
        | k3_relat_1(X16) != X15
        | X16 = k1_wellord2(X15)
        | ~ v1_relat_1(X16) )
      & ( ~ r2_hidden(k4_tarski(esk3_2(X15,X16),esk4_2(X15,X16)),X16)
        | ~ r1_tarski(esk3_2(X15,X16),esk4_2(X15,X16))
        | k3_relat_1(X16) != X15
        | X16 = k1_wellord2(X15)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(k4_tarski(esk3_2(X15,X16),esk4_2(X15,X16)),X16)
        | r1_tarski(esk3_2(X15,X16),esk4_2(X15,X16))
        | k3_relat_1(X16) != X15
        | X16 = k1_wellord2(X15)
        | ~ v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).

fof(c_0_35,plain,(
    ! [X68,X69] :
      ( ~ v3_ordinal1(X68)
      | ~ r1_tarski(X69,X68)
      | v2_wellord1(k1_wellord2(X69)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_wellord2])])])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(esk2_0,k2_wellord2(k1_wellord2(esk1_0)))
    | ~ v3_ordinal1(k2_wellord2(k1_wellord2(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_25])])).

fof(c_0_37,plain,(
    ! [X57,X58] :
      ( ( r2_hidden(esk7_2(X57,X58),k3_relat_1(X58))
        | ~ r1_tarski(X57,k3_relat_1(X58))
        | ~ v2_wellord1(X58)
        | r4_wellord1(X58,k2_wellord1(X58,X57))
        | ~ v1_relat_1(X58) )
      & ( r4_wellord1(k2_wellord1(X58,k1_wellord1(X58,esk7_2(X57,X58))),k2_wellord1(X58,X57))
        | ~ r1_tarski(X57,k3_relat_1(X58))
        | ~ v2_wellord1(X58)
        | r4_wellord1(X58,k2_wellord1(X58,X57))
        | ~ v1_relat_1(X58) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t64_wellord1])])])])])).

cnf(c_0_38,plain,
    ( k3_relat_1(X1) = X2
    | X1 != k1_wellord2(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,plain,
    ( v2_wellord1(k1_wellord2(X2))
    | ~ v3_ordinal1(X1)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(esk2_0,k2_wellord2(k1_wellord2(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_30]),c_0_31])])).

fof(c_0_41,plain,(
    ! [X61,X62] :
      ( ~ r2_hidden(X61,X62)
      | ~ v1_xboole_0(X62) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_42,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | X2 = k1_wellord2(X1)
    | k3_relat_1(X2) != X1
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( r2_hidden(esk7_2(X1,X2),k3_relat_1(X2))
    | r4_wellord1(X2,k2_wellord1(X2,X1))
    | ~ r1_tarski(X1,k3_relat_1(X2))
    | ~ v2_wellord1(X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( k3_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_38]),c_0_31])])).

cnf(c_0_45,negated_conjecture,
    ( v2_wellord1(k1_wellord2(esk2_0))
    | ~ v3_ordinal1(k2_wellord2(k1_wellord2(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_46,plain,(
    ! [X66,X67] :
      ( ~ r1_tarski(X66,X67)
      | k2_wellord1(k1_wellord2(X67),X66) = k1_wellord2(X66) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_wellord2])])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,plain,
    ( k1_wellord2(k3_relat_1(X1)) = X1
    | r2_hidden(esk3_2(k3_relat_1(X1),X1),k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_42])).

fof(c_0_49,plain,(
    ! [X64,X65] :
      ( ~ v1_xboole_0(X64)
      | X64 = X65
      | ~ v1_xboole_0(X65) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

fof(c_0_50,plain,(
    ! [X47,X48] :
      ( ( ~ m1_subset_1(X47,k1_zfmisc_1(X48))
        | r1_tarski(X47,X48) )
      & ( ~ r1_tarski(X47,X48)
        | m1_subset_1(X47,k1_zfmisc_1(X48)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_51,plain,
    ( r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),X2))
    | r2_hidden(esk7_2(X2,k1_wellord2(X1)),X1)
    | ~ v2_wellord1(k1_wellord2(X1))
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_31])])).

cnf(c_0_52,negated_conjecture,
    ( v2_wellord1(k1_wellord2(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_30]),c_0_31])])).

cnf(c_0_53,plain,
    ( k2_wellord1(k1_wellord2(X2),X1) = k1_wellord2(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_55,plain,
    ( k1_wellord2(k3_relat_1(X1)) = X1
    | ~ v1_xboole_0(k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_56,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_57,plain,(
    ! [X45,X46] :
      ( ~ m1_subset_1(X45,X46)
      | v1_xboole_0(X46)
      | r2_hidden(X45,X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_58,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_59,plain,(
    ! [X42,X43] :
      ( ~ r2_hidden(X42,X43)
      | m1_subset_1(X42,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_60,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk2_0),k2_wellord1(k1_wellord2(esk2_0),X1))
    | r2_hidden(esk7_2(X1,k1_wellord2(esk2_0)),esk2_0)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( k2_wellord1(k1_wellord2(esk2_0),esk1_0) = k1_wellord2(esk1_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_62,plain,
    ( k1_wellord2(X1) = X2
    | ~ v1_xboole_0(k3_relat_1(X2))
    | ~ v1_xboole_0(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_63,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk1_0,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_54])).

cnf(c_0_65,plain,
    ( r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,esk7_2(X2,X1))),k2_wellord1(X1,X2))
    | r4_wellord1(X1,k2_wellord1(X1,X2))
    | ~ r1_tarski(X2,k3_relat_1(X1))
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_66,plain,(
    ! [X71,X72] :
      ( ~ v3_ordinal1(X71)
      | ~ m1_subset_1(X72,X71)
      | v3_ordinal1(X72) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc5_ordinal1])])])).

cnf(c_0_67,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_68,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk2_0),k1_wellord2(esk1_0))
    | r2_hidden(esk7_2(esk1_0,k1_wellord2(esk2_0)),esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_54]),c_0_61])).

fof(c_0_69,plain,(
    ! [X21,X22,X23] :
      ( ( ~ v1_ordinal1(X21)
        | ~ r2_hidden(X22,X21)
        | r1_tarski(X22,X21) )
      & ( r2_hidden(esk5_1(X23),X23)
        | v1_ordinal1(X23) )
      & ( ~ r1_tarski(esk5_1(X23),X23)
        | v1_ordinal1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).

cnf(c_0_70,plain,
    ( r1_ordinal1(X1,X1)
    | ~ v3_ordinal1(X1) ),
    inference(ef,[status(thm)],[c_0_24])).

cnf(c_0_71,plain,
    ( k1_wellord2(X1) = k1_wellord2(X2)
    | ~ v1_xboole_0(X2)
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_44]),c_0_31])])).

cnf(c_0_72,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(esk2_0))
    | r2_hidden(esk1_0,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_73,plain,
    ( r4_wellord1(k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),esk7_2(X2,k1_wellord2(X1)))),k2_wellord1(k1_wellord2(X1),X2))
    | r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),X2))
    | ~ v2_wellord1(k1_wellord2(X1))
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_44]),c_0_31])])).

fof(c_0_74,plain,(
    ! [X39,X40] :
      ( ~ v3_ordinal1(X39)
      | ~ v3_ordinal1(X40)
      | ~ r2_hidden(X39,X40)
      | X39 = k1_wellord1(k1_wellord2(X40),X39) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_wellord2])])])).

cnf(c_0_75,plain,
    ( v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(esk7_2(esk1_0,k1_wellord2(esk2_0)),esk2_0)
    | r4_wellord1(k1_wellord2(esk2_0),k1_wellord2(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_77,plain,
    ( r1_tarski(X2,X1)
    | ~ v1_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

fof(c_0_78,plain,(
    ! [X70] :
      ( ( v1_ordinal1(X70)
        | ~ v3_ordinal1(X70) )
      & ( v2_ordinal1(X70)
        | ~ v3_ordinal1(X70) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).

cnf(c_0_79,plain,
    ( r1_tarski(X1,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_70])).

cnf(c_0_80,negated_conjecture,
    ( k1_wellord2(k1_zfmisc_1(esk2_0)) = k1_wellord2(X1)
    | r2_hidden(esk1_0,k1_zfmisc_1(esk2_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_81,negated_conjecture,
    ( r4_wellord1(k2_wellord1(k1_wellord2(esk2_0),k1_wellord1(k1_wellord2(esk2_0),esk7_2(X1,k1_wellord2(esk2_0)))),k2_wellord1(k1_wellord2(esk2_0),X1))
    | r4_wellord1(k1_wellord2(esk2_0),k2_wellord1(k1_wellord2(esk2_0),X1))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_52])).

cnf(c_0_82,plain,
    ( X1 = k1_wellord1(k1_wellord2(X2),X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_83,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk2_0),k1_wellord2(esk1_0))
    | v3_ordinal1(esk7_2(esk1_0,k1_wellord2(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_25])])).

cnf(c_0_84,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk2_0),k1_wellord2(esk1_0))
    | r1_tarski(esk7_2(esk1_0,k1_wellord2(esk2_0)),esk2_0)
    | ~ v1_ordinal1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_68])).

cnf(c_0_85,plain,
    ( v1_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_86,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_79])).

cnf(c_0_87,negated_conjecture,
    ( k1_zfmisc_1(esk2_0) = X1
    | r2_hidden(esk1_0,k1_zfmisc_1(esk2_0))
    | ~ v1_xboole_0(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_80]),c_0_44])).

cnf(c_0_88,negated_conjecture,
    ( r4_wellord1(k2_wellord1(k1_wellord2(esk2_0),k1_wellord1(k1_wellord2(esk2_0),esk7_2(esk1_0,k1_wellord2(esk2_0)))),k1_wellord2(esk1_0))
    | r4_wellord1(k1_wellord2(esk2_0),k1_wellord2(esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_54]),c_0_61]),c_0_61])).

cnf(c_0_89,negated_conjecture,
    ( k1_wellord1(k1_wellord2(esk2_0),esk7_2(esk1_0,k1_wellord2(esk2_0))) = esk7_2(esk1_0,k1_wellord2(esk2_0))
    | r4_wellord1(k1_wellord2(esk2_0),k1_wellord2(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_68]),c_0_25])]),c_0_83])).

cnf(c_0_90,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk2_0),k1_wellord2(esk1_0))
    | r1_tarski(esk7_2(esk1_0,k1_wellord2(esk2_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_25])])).

cnf(c_0_91,negated_conjecture,
    ( m1_subset_1(esk2_0,X1)
    | r2_hidden(esk1_0,k1_zfmisc_1(esk2_0))
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_25])])).

fof(c_0_92,plain,(
    ! [X52,X53] :
      ( ~ v1_relat_1(X52)
      | ~ v1_relat_1(X53)
      | ~ r4_wellord1(X52,X53)
      | r4_wellord1(X53,X52) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_wellord1])])])).

cnf(c_0_93,negated_conjecture,
    ( r4_wellord1(k2_wellord1(k1_wellord2(esk2_0),esk7_2(esk1_0,k1_wellord2(esk2_0))),k1_wellord2(esk1_0))
    | r4_wellord1(k1_wellord2(esk2_0),k1_wellord2(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_94,negated_conjecture,
    ( k2_wellord1(k1_wellord2(esk2_0),esk7_2(esk1_0,k1_wellord2(esk2_0))) = k1_wellord2(esk7_2(esk1_0,k1_wellord2(esk2_0)))
    | r4_wellord1(k1_wellord2(esk2_0),k1_wellord2(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_90])).

cnf(c_0_95,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_96,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk2_0))
    | r2_hidden(esk1_0,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_72])).

cnf(c_0_97,plain,
    ( r1_ordinal1(X1,X2)
    | ~ r1_tarski(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_98,plain,(
    ! [X25,X26] :
      ( ( X26 != k2_wellord2(X25)
        | r4_wellord1(X25,k1_wellord2(X26))
        | ~ v3_ordinal1(X26)
        | ~ v2_wellord1(X25)
        | ~ v1_relat_1(X25) )
      & ( ~ r4_wellord1(X25,k1_wellord2(X26))
        | X26 = k2_wellord2(X25)
        | ~ v3_ordinal1(X26)
        | ~ v2_wellord1(X25)
        | ~ v1_relat_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_wellord2])])])])).

cnf(c_0_99,plain,
    ( r4_wellord1(X2,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r4_wellord1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_100,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk7_2(esk1_0,k1_wellord2(esk2_0))),k1_wellord2(esk1_0))
    | r4_wellord1(k1_wellord2(esk2_0),k1_wellord2(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_101,negated_conjecture,
    ( r2_hidden(esk1_0,k1_zfmisc_1(esk2_0))
    | r1_tarski(esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_102,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk2_0),k1_wellord2(esk1_0))
    | r1_ordinal1(esk7_2(esk1_0,k1_wellord2(esk2_0)),esk2_0)
    | ~ v3_ordinal1(esk7_2(esk1_0,k1_wellord2(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_90]),c_0_25])])).

cnf(c_0_103,plain,
    ( X2 = k2_wellord2(X1)
    | ~ r4_wellord1(X1,k1_wellord2(X2))
    | ~ v3_ordinal1(X2)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_104,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk1_0),k1_wellord2(esk7_2(esk1_0,k1_wellord2(esk2_0))))
    | r4_wellord1(k1_wellord2(esk2_0),k1_wellord2(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_31]),c_0_31])])).

cnf(c_0_105,negated_conjecture,
    ( v2_wellord1(k1_wellord2(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_54]),c_0_25])])).

cnf(c_0_106,negated_conjecture,
    ( r1_tarski(esk2_0,esk2_0)
    | ~ v1_xboole_0(k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_101])).

cnf(c_0_107,plain,
    ( v1_xboole_0(k1_zfmisc_1(X1))
    | r2_hidden(X1,k1_zfmisc_1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_86])).

cnf(c_0_108,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk2_0),k1_wellord2(esk1_0))
    | r1_ordinal1(esk7_2(esk1_0,k1_wellord2(esk2_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_102,c_0_83])).

cnf(c_0_109,negated_conjecture,
    ( esk7_2(esk1_0,k1_wellord2(esk2_0)) = k2_wellord2(k1_wellord2(esk1_0))
    | r4_wellord1(k1_wellord2(esk2_0),k1_wellord2(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_105]),c_0_31])]),c_0_83])).

cnf(c_0_110,negated_conjecture,
    ( r2_hidden(esk2_0,k1_zfmisc_1(esk2_0))
    | r1_tarski(esk2_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_25])])).

cnf(c_0_111,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk2_0),k1_wellord2(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_23])).

cnf(c_0_112,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_110]),c_0_58])).

cnf(c_0_113,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk1_0),k1_wellord2(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_111]),c_0_31]),c_0_31])])).

cnf(c_0_114,negated_conjecture,
    ( r1_tarski(esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_95,c_0_112])).

cnf(c_0_115,negated_conjecture,
    ( k2_wellord2(k1_wellord2(esk1_0)) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_113]),c_0_105]),c_0_31]),c_0_25])])).

cnf(c_0_116,negated_conjecture,
    ( r1_ordinal1(esk2_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_114]),c_0_25])])).

cnf(c_0_117,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_115]),c_0_116])]),
    [proof]).
%------------------------------------------------------------------------------
