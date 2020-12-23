%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relset_1__t33_relset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:09 EDT 2019

% Result     : Theorem 264.45s
% Output     : CNFRefutation 264.45s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 253 expanded)
%              Number of clauses        :   42 ( 110 expanded)
%              Number of leaves         :   14 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :  203 ( 645 expanded)
%              Number of equality atoms :   21 (  64 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t33_relset_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
     => m1_subset_1(k5_relset_1(X1,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t33_relset_1.p',t33_relset_1)).

fof(redefinition_k5_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k5_relset_1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t33_relset_1.p',redefinition_k5_relset_1)).

fof(dt_k5_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k5_relset_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t33_relset_1.p',dt_k5_relset_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t33_relset_1.p',t8_boole)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t33_relset_1.p',t3_subset)).

fof(d3_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_tarski(X1,X2)
        <=> ! [X3,X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
             => r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t33_relset_1.p',d3_relat_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t33_relset_1.p',cc1_relset_1)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t33_relset_1.p',dt_o_0_0_xboole_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t33_relset_1.p',t2_subset)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t33_relset_1.p',t4_subset)).

fof(d11_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( v1_relat_1(X3)
         => ( X3 = k7_relat_1(X1,X2)
          <=> ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X3)
              <=> ( r2_hidden(X4,X2)
                  & r2_hidden(k4_tarski(X4,X5),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t33_relset_1.p',d11_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t33_relset_1.p',dt_k7_relat_1)).

fof(t106_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t33_relset_1.p',t106_zfmisc_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t33_relset_1.p',t5_subset)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
       => m1_subset_1(k5_relset_1(X1,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(assume_negation,[status(cth)],[t33_relset_1])).

fof(c_0_15,plain,(
    ! [X36,X37,X38,X39] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | k5_relset_1(X36,X37,X38,X39) = k7_relat_1(X38,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_relset_1])])).

fof(c_0_16,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))
    & ~ m1_subset_1(k5_relset_1(esk1_0,esk3_0,esk4_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_17,plain,(
    ! [X28,X29,X30,X31] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | m1_subset_1(k5_relset_1(X28,X29,X30,X31),k1_zfmisc_1(k2_zfmisc_1(X28,X29))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relset_1])])).

cnf(c_0_18,plain,
    ( k5_relset_1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X59,X60] :
      ( ~ v1_xboole_0(X59)
      | X59 = X60
      | ~ v1_xboole_0(X60) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

fof(c_0_21,plain,(
    ! [X48,X49] :
      ( ( ~ m1_subset_1(X48,k1_zfmisc_1(X49))
        | r1_tarski(X48,X49) )
      & ( ~ r1_tarski(X48,X49)
        | m1_subset_1(X48,k1_zfmisc_1(X49)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_22,plain,(
    ! [X21,X22,X23,X24,X25] :
      ( ( ~ r1_tarski(X21,X22)
        | ~ r2_hidden(k4_tarski(X23,X24),X21)
        | r2_hidden(k4_tarski(X23,X24),X22)
        | ~ v1_relat_1(X21) )
      & ( r2_hidden(k4_tarski(esk7_2(X21,X25),esk8_2(X21,X25)),X21)
        | r1_tarski(X21,X25)
        | ~ v1_relat_1(X21) )
      & ( ~ r2_hidden(k4_tarski(esk7_2(X21,X25),esk8_2(X21,X25)),X25)
        | r1_tarski(X21,X25)
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).

fof(c_0_23,plain,(
    ! [X61,X62,X63] :
      ( ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X62)))
      | v1_relat_1(X63) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_24,plain,
    ( m1_subset_1(k5_relset_1(X2,X3,X1,X4),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( k5_relset_1(esk1_0,esk3_0,esk4_0,X1) = k7_relat_1(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

fof(c_0_28,plain,(
    ! [X46,X47] :
      ( ~ m1_subset_1(X46,X47)
      | v1_xboole_0(X47)
      | r2_hidden(X46,X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_29,plain,(
    ! [X50,X51,X52] :
      ( ~ r2_hidden(X50,X51)
      | ~ m1_subset_1(X51,k1_zfmisc_1(X52))
      | m1_subset_1(X50,X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_30,negated_conjecture,
    ( ~ m1_subset_1(k5_relset_1(esk1_0,esk3_0,esk4_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(esk7_2(X1,X2),esk8_2(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_19])])).

fof(c_0_35,plain,(
    ! [X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X15,X13)
        | ~ r2_hidden(k4_tarski(X15,X16),X14)
        | X14 != k7_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(k4_tarski(X15,X16),X12)
        | ~ r2_hidden(k4_tarski(X15,X16),X14)
        | X14 != k7_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X12) )
      & ( ~ r2_hidden(X17,X13)
        | ~ r2_hidden(k4_tarski(X17,X18),X12)
        | r2_hidden(k4_tarski(X17,X18),X14)
        | X14 != k7_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X12) )
      & ( ~ r2_hidden(k4_tarski(esk5_3(X12,X13,X14),esk6_3(X12,X13,X14)),X14)
        | ~ r2_hidden(esk5_3(X12,X13,X14),X13)
        | ~ r2_hidden(k4_tarski(esk5_3(X12,X13,X14),esk6_3(X12,X13,X14)),X12)
        | X14 = k7_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(esk5_3(X12,X13,X14),X13)
        | r2_hidden(k4_tarski(esk5_3(X12,X13,X14),esk6_3(X12,X13,X14)),X14)
        | X14 = k7_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(k4_tarski(esk5_3(X12,X13,X14),esk6_3(X12,X13,X14)),X12)
        | r2_hidden(k4_tarski(esk5_3(X12,X13,X14),esk6_3(X12,X13,X14)),X14)
        | X14 = k7_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_relat_1])])])])])])).

fof(c_0_36,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X32)
      | v1_relat_1(k7_relat_1(X32,X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_37,plain,
    ( r2_hidden(k4_tarski(esk7_2(X1,X2),esk8_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_38,plain,
    ( o_0_0_xboole_0 = X1
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_39,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,negated_conjecture,
    ( ~ m1_subset_1(k7_relat_1(esk4_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_30,c_0_25])).

cnf(c_0_42,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(esk7_2(X1,X2),esk8_2(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_44,plain,(
    ! [X40,X41,X42,X43] :
      ( ( r2_hidden(X40,X42)
        | ~ r2_hidden(k4_tarski(X40,X41),k2_zfmisc_1(X42,X43)) )
      & ( r2_hidden(X41,X43)
        | ~ r2_hidden(k4_tarski(X40,X41),k2_zfmisc_1(X42,X43)) )
      & ( ~ r2_hidden(X40,X42)
        | ~ r2_hidden(X41,X43)
        | r2_hidden(k4_tarski(X40,X41),k2_zfmisc_1(X42,X43)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | X4 != k7_relat_1(X5,X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X5) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( r2_hidden(k4_tarski(esk7_2(X1,X2),esk8_2(X1,X2)),X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_37])).

cnf(c_0_48,plain,
    ( o_0_0_xboole_0 = X1
    | r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(X1,k2_zfmisc_1(esk1_0,esk3_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_19])).

cnf(c_0_50,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X1,X2),X4)
    | X4 != k7_relat_1(X3,X5)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_51,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk7_2(k7_relat_1(esk4_0,esk2_0),k2_zfmisc_1(esk2_0,esk3_0)),esk8_2(k7_relat_1(esk4_0,esk2_0),k2_zfmisc_1(esk2_0,esk3_0))),k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])])).

cnf(c_0_52,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X1,X4),k7_relat_1(X3,X2)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_45]),c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_2(k7_relat_1(esk4_0,esk2_0),k2_zfmisc_1(esk2_0,esk3_0)),esk8_2(k7_relat_1(esk4_0,esk2_0),k2_zfmisc_1(esk2_0,esk3_0))),k7_relat_1(esk4_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_47]),c_0_43])])).

cnf(c_0_55,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_19])).

fof(c_0_56,plain,(
    ! [X53,X54,X55] :
      ( ~ r2_hidden(X53,X54)
      | ~ m1_subset_1(X54,k1_zfmisc_1(X55))
      | ~ v1_xboole_0(X55) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_58,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk3_0) = o_0_0_xboole_0
    | r2_hidden(X1,k2_zfmisc_1(esk1_0,esk3_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_59,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X1,X2),k7_relat_1(X3,X4)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_50]),c_0_46])).

cnf(c_0_60,negated_conjecture,
    ( ~ r2_hidden(esk8_2(k7_relat_1(esk4_0,esk2_0),k2_zfmisc_1(esk2_0,esk3_0)),esk3_0)
    | ~ r2_hidden(esk7_2(k7_relat_1(esk4_0,esk2_0),k2_zfmisc_1(esk2_0,esk3_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk7_2(k7_relat_1(esk4_0,esk2_0),k2_zfmisc_1(esk2_0,esk3_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk3_0) = o_0_0_xboole_0
    | r2_hidden(X1,esk3_0)
    | ~ r2_hidden(k4_tarski(X2,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_2(k7_relat_1(esk4_0,esk2_0),k2_zfmisc_1(esk2_0,esk3_0)),esk8_2(k7_relat_1(esk4_0,esk2_0),k2_zfmisc_1(esk2_0,esk3_0))),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_54]),c_0_55])])).

cnf(c_0_65,negated_conjecture,
    ( ~ r2_hidden(esk8_2(k7_relat_1(esk4_0,esk2_0),k2_zfmisc_1(esk2_0,esk3_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61])])).

cnf(c_0_66,negated_conjecture,
    ( ~ v1_xboole_0(k2_zfmisc_1(esk1_0,esk3_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_19])).

cnf(c_0_67,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk3_0) = o_0_0_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67]),c_0_27])])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_64,c_0_68]),
    [proof]).
%------------------------------------------------------------------------------
