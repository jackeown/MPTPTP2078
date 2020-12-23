%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : wellord1__t10_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:10 EDT 2019

% Result     : Theorem 161.64s
% Output     : CNFRefutation 161.64s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 368 expanded)
%              Number of clauses        :   45 ( 135 expanded)
%              Number of leaves         :   12 (  89 expanded)
%              Depth                    :   13
%              Number of atoms          :  295 (2118 expanded)
%              Number of equality atoms :   32 ( 235 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t10_wellord1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => ! [X2] :
            ~ ( r1_tarski(X2,k3_relat_1(X1))
              & X2 != k1_xboole_0
              & ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & ! [X4] :
                        ( r2_hidden(X4,X2)
                       => r2_hidden(k4_tarski(X3,X4),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t10_wellord1.p',t10_wellord1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t10_wellord1.p',t3_subset)).

fof(d2_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v1_wellord1(X1)
      <=> ! [X2] :
            ~ ( r1_tarski(X2,k3_relat_1(X1))
              & X2 != k1_xboole_0
              & ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r1_xboole_0(k1_wellord1(X1,X3),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t10_wellord1.p',d2_wellord1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t10_wellord1.p',t4_subset)).

fof(d4_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
      <=> ( v1_relat_2(X1)
          & v8_relat_2(X1)
          & v4_relat_2(X1)
          & v6_relat_2(X1)
          & v1_wellord1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t10_wellord1.p',d4_wellord1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t10_wellord1.p',t2_subset)).

fof(l4_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v6_relat_2(X1)
      <=> ! [X2,X3] :
            ~ ( r2_hidden(X2,k3_relat_1(X1))
              & r2_hidden(X3,k3_relat_1(X1))
              & X2 != X3
              & ~ r2_hidden(k4_tarski(X2,X3),X1)
              & ~ r2_hidden(k4_tarski(X3,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t10_wellord1.p',l4_wellord1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t10_wellord1.p',t7_boole)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t10_wellord1.p',t3_xboole_0)).

fof(d1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k1_wellord1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ( X4 != X2
                & r2_hidden(k4_tarski(X4,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t10_wellord1.p',d1_wellord1)).

fof(l1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v1_relat_2(X1)
      <=> ! [X2] :
            ( r2_hidden(X2,k3_relat_1(X1))
           => r2_hidden(k4_tarski(X2,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t10_wellord1.p',l1_wellord1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t10_wellord1.p',t5_subset)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( v2_wellord1(X1)
         => ! [X2] :
              ~ ( r1_tarski(X2,k3_relat_1(X1))
                & X2 != k1_xboole_0
                & ! [X3] :
                    ~ ( r2_hidden(X3,X2)
                      & ! [X4] :
                          ( r2_hidden(X4,X2)
                         => r2_hidden(k4_tarski(X3,X4),X1) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t10_wellord1])).

fof(c_0_13,plain,(
    ! [X45,X46] :
      ( ( ~ m1_subset_1(X45,k1_zfmisc_1(X46))
        | r1_tarski(X45,X46) )
      & ( ~ r1_tarski(X45,X46)
        | m1_subset_1(X45,k1_zfmisc_1(X46)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_14,negated_conjecture,(
    ! [X7] :
      ( v1_relat_1(esk1_0)
      & v2_wellord1(esk1_0)
      & r1_tarski(esk2_0,k3_relat_1(esk1_0))
      & esk2_0 != k1_xboole_0
      & ( r2_hidden(esk3_1(X7),esk2_0)
        | ~ r2_hidden(X7,esk2_0) )
      & ( ~ r2_hidden(k4_tarski(X7,esk3_1(X7)),esk1_0)
        | ~ r2_hidden(X7,esk2_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])])).

fof(c_0_15,plain,(
    ! [X21,X22,X25] :
      ( ( r2_hidden(esk5_2(X21,X22),X22)
        | ~ r1_tarski(X22,k3_relat_1(X21))
        | X22 = k1_xboole_0
        | ~ v1_wellord1(X21)
        | ~ v1_relat_1(X21) )
      & ( r1_xboole_0(k1_wellord1(X21,esk5_2(X21,X22)),X22)
        | ~ r1_tarski(X22,k3_relat_1(X21))
        | X22 = k1_xboole_0
        | ~ v1_wellord1(X21)
        | ~ v1_relat_1(X21) )
      & ( r1_tarski(esk6_1(X21),k3_relat_1(X21))
        | v1_wellord1(X21)
        | ~ v1_relat_1(X21) )
      & ( esk6_1(X21) != k1_xboole_0
        | v1_wellord1(X21)
        | ~ v1_relat_1(X21) )
      & ( ~ r2_hidden(X25,esk6_1(X21))
        | ~ r1_xboole_0(k1_wellord1(X21,X25),esk6_1(X21))
        | v1_wellord1(X21)
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_wellord1])])])])])).

fof(c_0_16,plain,(
    ! [X53,X54,X55] :
      ( ~ r2_hidden(X53,X54)
      | ~ m1_subset_1(X54,k1_zfmisc_1(X55))
      | m1_subset_1(X53,X55) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(esk2_0,k3_relat_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( r2_hidden(esk5_2(X1,X2),X2)
    | X2 = k1_xboole_0
    | ~ r1_tarski(X2,k3_relat_1(X1))
    | ~ v1_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_22,plain,(
    ! [X26] :
      ( ( v1_relat_2(X26)
        | ~ v2_wellord1(X26)
        | ~ v1_relat_1(X26) )
      & ( v8_relat_2(X26)
        | ~ v2_wellord1(X26)
        | ~ v1_relat_1(X26) )
      & ( v4_relat_2(X26)
        | ~ v2_wellord1(X26)
        | ~ v1_relat_1(X26) )
      & ( v6_relat_2(X26)
        | ~ v2_wellord1(X26)
        | ~ v1_relat_1(X26) )
      & ( v1_wellord1(X26)
        | ~ v2_wellord1(X26)
        | ~ v1_relat_1(X26) )
      & ( ~ v1_relat_2(X26)
        | ~ v8_relat_2(X26)
        | ~ v4_relat_2(X26)
        | ~ v6_relat_2(X26)
        | ~ v1_wellord1(X26)
        | v2_wellord1(X26)
        | ~ v1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k3_relat_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk5_2(esk1_0,esk2_0),esk2_0)
    | ~ v1_wellord1(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_18]),c_0_20])]),c_0_21])).

cnf(c_0_26,plain,
    ( v1_wellord1(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( v2_wellord1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_28,plain,(
    ! [X43,X44] :
      ( ~ m1_subset_1(X43,X44)
      | v1_xboole_0(X44)
      | r2_hidden(X43,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(X1,k3_relat_1(esk1_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk5_2(esk1_0,esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_20])])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk3_1(X1),esk2_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_32,plain,
    ( r1_xboole_0(k1_wellord1(X1,esk5_2(X1,X2)),X2)
    | X2 = k1_xboole_0
    | ~ r1_tarski(X2,k3_relat_1(X1))
    | ~ v1_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_33,plain,(
    ! [X33,X34,X35] :
      ( ( ~ v6_relat_2(X33)
        | ~ r2_hidden(X34,k3_relat_1(X33))
        | ~ r2_hidden(X35,k3_relat_1(X33))
        | X34 = X35
        | r2_hidden(k4_tarski(X34,X35),X33)
        | r2_hidden(k4_tarski(X35,X34),X33)
        | ~ v1_relat_1(X33) )
      & ( r2_hidden(esk9_1(X33),k3_relat_1(X33))
        | v6_relat_2(X33)
        | ~ v1_relat_1(X33) )
      & ( r2_hidden(esk10_1(X33),k3_relat_1(X33))
        | v6_relat_2(X33)
        | ~ v1_relat_1(X33) )
      & ( esk9_1(X33) != esk10_1(X33)
        | v6_relat_2(X33)
        | ~ v1_relat_1(X33) )
      & ( ~ r2_hidden(k4_tarski(esk9_1(X33),esk10_1(X33)),X33)
        | v6_relat_2(X33)
        | ~ v1_relat_1(X33) )
      & ( ~ r2_hidden(k4_tarski(esk10_1(X33),esk9_1(X33)),X33)
        | v6_relat_2(X33)
        | ~ v1_relat_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l4_wellord1])])])])])])).

cnf(c_0_34,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk5_2(esk1_0,esk2_0),k3_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
    ( v6_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_37,plain,(
    ! [X60,X61] :
      ( ~ r2_hidden(X60,X61)
      | ~ v1_xboole_0(X61) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk3_1(esk5_2(esk1_0,esk2_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_30])).

fof(c_0_39,plain,(
    ! [X47,X48,X50,X51,X52] :
      ( ( r2_hidden(esk11_2(X47,X48),X47)
        | r1_xboole_0(X47,X48) )
      & ( r2_hidden(esk11_2(X47,X48),X48)
        | r1_xboole_0(X47,X48) )
      & ( ~ r2_hidden(X52,X50)
        | ~ r2_hidden(X52,X51)
        | ~ r1_xboole_0(X50,X51) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_40,negated_conjecture,
    ( r1_xboole_0(k1_wellord1(esk1_0,esk5_2(esk1_0,esk2_0)),esk2_0)
    | ~ v1_wellord1(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_18]),c_0_20])]),c_0_21])).

fof(c_0_41,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19] :
      ( ( X16 != X14
        | ~ r2_hidden(X16,X15)
        | X15 != k1_wellord1(X13,X14)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(k4_tarski(X16,X14),X13)
        | ~ r2_hidden(X16,X15)
        | X15 != k1_wellord1(X13,X14)
        | ~ v1_relat_1(X13) )
      & ( X17 = X14
        | ~ r2_hidden(k4_tarski(X17,X14),X13)
        | r2_hidden(X17,X15)
        | X15 != k1_wellord1(X13,X14)
        | ~ v1_relat_1(X13) )
      & ( ~ r2_hidden(esk4_3(X13,X18,X19),X19)
        | esk4_3(X13,X18,X19) = X18
        | ~ r2_hidden(k4_tarski(esk4_3(X13,X18,X19),X18),X13)
        | X19 = k1_wellord1(X13,X18)
        | ~ v1_relat_1(X13) )
      & ( esk4_3(X13,X18,X19) != X18
        | r2_hidden(esk4_3(X13,X18,X19),X19)
        | X19 = k1_wellord1(X13,X18)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(k4_tarski(esk4_3(X13,X18,X19),X18),X13)
        | r2_hidden(esk4_3(X13,X18,X19),X19)
        | X19 = k1_wellord1(X13,X18)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).

cnf(c_0_42,plain,
    ( X2 = X3
    | r2_hidden(k4_tarski(X2,X3),X1)
    | r2_hidden(k4_tarski(X3,X2),X1)
    | ~ v6_relat_2(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r2_hidden(X3,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( v1_xboole_0(k3_relat_1(esk1_0))
    | r2_hidden(esk5_2(esk1_0,esk2_0),k3_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( v6_relat_2(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_27]),c_0_20])])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk3_1(esk5_2(esk1_0,esk2_0)),k3_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,esk3_1(X1)),esk1_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( r1_xboole_0(k1_wellord1(esk1_0,esk5_2(esk1_0,esk2_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_26]),c_0_27]),c_0_20])])).

fof(c_0_50,plain,(
    ! [X30,X31] :
      ( ( ~ v1_relat_2(X30)
        | ~ r2_hidden(X31,k3_relat_1(X30))
        | r2_hidden(k4_tarski(X31,X31),X30)
        | ~ v1_relat_1(X30) )
      & ( r2_hidden(esk8_1(X30),k3_relat_1(X30))
        | v1_relat_2(X30)
        | ~ v1_relat_1(X30) )
      & ( ~ r2_hidden(k4_tarski(esk8_1(X30),esk8_1(X30)),X30)
        | v1_relat_2(X30)
        | ~ v1_relat_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_wellord1])])])])])).

cnf(c_0_51,plain,
    ( X1 = X2
    | r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,negated_conjecture,
    ( X1 = esk5_2(esk1_0,esk2_0)
    | r2_hidden(k4_tarski(X1,esk5_2(esk1_0,esk2_0)),esk1_0)
    | r2_hidden(k4_tarski(esk5_2(esk1_0,esk2_0),X1),esk1_0)
    | ~ r2_hidden(X1,k3_relat_1(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_20])]),c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( v1_xboole_0(k3_relat_1(esk1_0))
    | r2_hidden(esk3_1(esk5_2(esk1_0,esk2_0)),k3_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk5_2(esk1_0,esk2_0),esk3_1(esk5_2(esk1_0,esk2_0))),esk1_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_30])).

cnf(c_0_55,negated_conjecture,
    ( ~ r2_hidden(X1,k1_wellord1(esk1_0,esk5_2(esk1_0,esk2_0)))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_56,plain,
    ( r2_hidden(k4_tarski(X2,X2),X1)
    | ~ v1_relat_2(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_57,plain,(
    ! [X56,X57,X58] :
      ( ~ r2_hidden(X56,X57)
      | ~ m1_subset_1(X57,k1_zfmisc_1(X58))
      | ~ v1_xboole_0(X58) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_58,plain,
    ( X1 = X2
    | r2_hidden(X1,k1_wellord1(X3,X2))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( esk3_1(esk5_2(esk1_0,esk2_0)) = esk5_2(esk1_0,esk2_0)
    | v1_xboole_0(k3_relat_1(esk1_0))
    | r2_hidden(k4_tarski(esk3_1(esk5_2(esk1_0,esk2_0)),esk5_2(esk1_0,esk2_0)),esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( ~ r2_hidden(esk3_1(esk5_2(esk1_0,esk2_0)),k1_wellord1(esk1_0,esk5_2(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_38])).

cnf(c_0_61,negated_conjecture,
    ( v1_xboole_0(k3_relat_1(esk1_0))
    | r2_hidden(k4_tarski(esk5_2(esk1_0,esk2_0),esk5_2(esk1_0,esk2_0)),esk1_0)
    | ~ v1_relat_2(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_43]),c_0_20])])).

cnf(c_0_62,plain,
    ( v1_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_63,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( esk3_1(esk5_2(esk1_0,esk2_0)) = esk5_2(esk1_0,esk2_0)
    | v1_xboole_0(k3_relat_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_20])]),c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( v1_xboole_0(k3_relat_1(esk1_0))
    | r2_hidden(k4_tarski(esk5_2(esk1_0,esk2_0),esk5_2(esk1_0,esk2_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_27]),c_0_20])])).

cnf(c_0_66,negated_conjecture,
    ( ~ v1_xboole_0(k3_relat_1(esk1_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_24])).

cnf(c_0_67,negated_conjecture,
    ( v1_xboole_0(k3_relat_1(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_64]),c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( ~ r2_hidden(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67])])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_30,c_0_68]),
    [proof]).
%------------------------------------------------------------------------------
