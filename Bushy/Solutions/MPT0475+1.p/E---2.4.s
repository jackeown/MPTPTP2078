%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t67_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:03 EDT 2019

% Result     : Theorem 265.55s
% Output     : CNFRefutation 265.55s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 146 expanded)
%              Number of clauses        :   42 (  67 expanded)
%              Number of leaves         :   13 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :  238 ( 518 expanded)
%              Number of equality atoms :   52 ( 114 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   38 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t67_relat_1.p',t7_boole)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t67_relat_1.p',d4_relat_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t67_relat_1.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t67_relat_1.p',existence_m1_subset_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t67_relat_1.p',t6_boole)).

fof(t56_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ! [X2,X3] : ~ r2_hidden(k4_tarski(X2,X3),X1)
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t67_relat_1.p',t56_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t67_relat_1.p',dt_k5_relat_1)).

fof(t67_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_xboole_0(k2_relat_1(X1),k1_relat_1(X2))
           => k5_relat_1(X1,X2) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t67_relat_1.p',t67_relat_1)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t67_relat_1.p',dt_o_0_0_xboole_0)).

fof(d8_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( X3 = k5_relat_1(X1,X2)
              <=> ! [X4,X5] :
                    ( r2_hidden(k4_tarski(X4,X5),X3)
                  <=> ? [X6] :
                        ( r2_hidden(k4_tarski(X4,X6),X1)
                        & r2_hidden(k4_tarski(X6,X5),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t67_relat_1.p',d8_relat_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t67_relat_1.p',d4_xboole_0)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t67_relat_1.p',d7_xboole_0)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t67_relat_1.p',d5_relat_1)).

fof(c_0_13,plain,(
    ! [X75,X76] :
      ( ~ r2_hidden(X75,X76)
      | ~ v1_xboole_0(X76) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_14,plain,(
    ! [X13,X14,X15,X17,X18,X19,X20,X22] :
      ( ( ~ r2_hidden(X15,X14)
        | r2_hidden(k4_tarski(X15,esk3_3(X13,X14,X15)),X13)
        | X14 != k1_relat_1(X13) )
      & ( ~ r2_hidden(k4_tarski(X17,X18),X13)
        | r2_hidden(X17,X14)
        | X14 != k1_relat_1(X13) )
      & ( ~ r2_hidden(esk4_2(X19,X20),X20)
        | ~ r2_hidden(k4_tarski(esk4_2(X19,X20),X22),X19)
        | X20 = k1_relat_1(X19) )
      & ( r2_hidden(esk4_2(X19,X20),X20)
        | r2_hidden(k4_tarski(esk4_2(X19,X20),esk5_2(X19,X20)),X19)
        | X20 = k1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_15,plain,(
    ! [X69,X70] :
      ( ~ m1_subset_1(X69,X70)
      | v1_xboole_0(X70)
      | r2_hidden(X69,X70) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_16,plain,(
    ! [X61] : m1_subset_1(esk14_1(X61),X61) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_tarski(X1,esk3_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X74] :
      ( ~ v1_xboole_0(X74)
      | X74 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_20,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( m1_subset_1(esk14_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X71] :
      ( ~ v1_relat_1(X71)
      | r2_hidden(k4_tarski(esk15_1(X71),esk16_1(X71)),X71)
      | X71 = k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_relat_1])])])])).

fof(c_0_23,plain,(
    ! [X59,X60] :
      ( ~ v1_relat_1(X59)
      | ~ v1_relat_1(X60)
      | v1_relat_1(k5_relat_1(X59,X60)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_xboole_0(k2_relat_1(X1),k1_relat_1(X2))
             => k5_relat_1(X1,X2) = k1_xboole_0 ) ) ) ),
    inference(assume_negation,[status(cth)],[t67_relat_1])).

cnf(c_0_25,plain,
    ( X1 != k1_relat_1(X2)
    | ~ v1_xboole_0(X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_26,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk14_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_29,plain,
    ( r2_hidden(k4_tarski(esk15_1(X1),esk16_1(X1)),X1)
    | X1 = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_31,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & r1_xboole_0(k2_relat_1(esk1_0),k1_relat_1(esk2_0))
    & k5_relat_1(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

cnf(c_0_32,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk14_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_28])).

fof(c_0_35,plain,(
    ! [X46,X47,X48,X49,X50,X52,X53,X54,X57] :
      ( ( r2_hidden(k4_tarski(X49,esk10_5(X46,X47,X48,X49,X50)),X46)
        | ~ r2_hidden(k4_tarski(X49,X50),X48)
        | X48 != k5_relat_1(X46,X47)
        | ~ v1_relat_1(X48)
        | ~ v1_relat_1(X47)
        | ~ v1_relat_1(X46) )
      & ( r2_hidden(k4_tarski(esk10_5(X46,X47,X48,X49,X50),X50),X47)
        | ~ r2_hidden(k4_tarski(X49,X50),X48)
        | X48 != k5_relat_1(X46,X47)
        | ~ v1_relat_1(X48)
        | ~ v1_relat_1(X47)
        | ~ v1_relat_1(X46) )
      & ( ~ r2_hidden(k4_tarski(X52,X54),X46)
        | ~ r2_hidden(k4_tarski(X54,X53),X47)
        | r2_hidden(k4_tarski(X52,X53),X48)
        | X48 != k5_relat_1(X46,X47)
        | ~ v1_relat_1(X48)
        | ~ v1_relat_1(X47)
        | ~ v1_relat_1(X46) )
      & ( ~ r2_hidden(k4_tarski(esk11_3(X46,X47,X48),esk12_3(X46,X47,X48)),X48)
        | ~ r2_hidden(k4_tarski(esk11_3(X46,X47,X48),X57),X46)
        | ~ r2_hidden(k4_tarski(X57,esk12_3(X46,X47,X48)),X47)
        | X48 = k5_relat_1(X46,X47)
        | ~ v1_relat_1(X48)
        | ~ v1_relat_1(X47)
        | ~ v1_relat_1(X46) )
      & ( r2_hidden(k4_tarski(esk11_3(X46,X47,X48),esk13_3(X46,X47,X48)),X46)
        | r2_hidden(k4_tarski(esk11_3(X46,X47,X48),esk12_3(X46,X47,X48)),X48)
        | X48 = k5_relat_1(X46,X47)
        | ~ v1_relat_1(X48)
        | ~ v1_relat_1(X47)
        | ~ v1_relat_1(X46) )
      & ( r2_hidden(k4_tarski(esk13_3(X46,X47,X48),esk12_3(X46,X47,X48)),X47)
        | r2_hidden(k4_tarski(esk11_3(X46,X47,X48),esk12_3(X46,X47,X48)),X48)
        | X48 = k5_relat_1(X46,X47)
        | ~ v1_relat_1(X48)
        | ~ v1_relat_1(X47)
        | ~ v1_relat_1(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

cnf(c_0_36,plain,
    ( k5_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(k4_tarski(esk15_1(k5_relat_1(X1,X2)),esk16_1(k5_relat_1(X1,X2))),k5_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_38,plain,(
    ! [X24,X25,X26,X27,X28,X29,X30,X31] :
      ( ( r2_hidden(X27,X24)
        | ~ r2_hidden(X27,X26)
        | X26 != k3_xboole_0(X24,X25) )
      & ( r2_hidden(X27,X25)
        | ~ r2_hidden(X27,X26)
        | X26 != k3_xboole_0(X24,X25) )
      & ( ~ r2_hidden(X28,X24)
        | ~ r2_hidden(X28,X25)
        | r2_hidden(X28,X26)
        | X26 != k3_xboole_0(X24,X25) )
      & ( ~ r2_hidden(esk6_3(X29,X30,X31),X31)
        | ~ r2_hidden(esk6_3(X29,X30,X31),X29)
        | ~ r2_hidden(esk6_3(X29,X30,X31),X30)
        | X31 = k3_xboole_0(X29,X30) )
      & ( r2_hidden(esk6_3(X29,X30,X31),X29)
        | r2_hidden(esk6_3(X29,X30,X31),X31)
        | X31 = k3_xboole_0(X29,X30) )
      & ( r2_hidden(esk6_3(X29,X30,X31),X30)
        | r2_hidden(esk6_3(X29,X30,X31),X31)
        | X31 = k3_xboole_0(X29,X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_39,plain,(
    ! [X44,X45] :
      ( ( ~ r1_xboole_0(X44,X45)
        | k3_xboole_0(X44,X45) = k1_xboole_0 )
      & ( k3_xboole_0(X44,X45) != k1_xboole_0
        | r1_xboole_0(X44,X45) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_40,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_41,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_28,c_0_34])).

cnf(c_0_42,plain,
    ( r2_hidden(k4_tarski(esk10_5(X1,X2,X3,X4,X5),X5),X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | X3 != k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( k5_relat_1(esk1_0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(esk15_1(k5_relat_1(esk1_0,X1)),esk16_1(k5_relat_1(esk1_0,X1))),k5_relat_1(esk1_0,X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_45,negated_conjecture,
    ( k5_relat_1(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_46,plain,(
    ! [X33,X34,X35,X37,X38,X39,X40,X42] :
      ( ( ~ r2_hidden(X35,X34)
        | r2_hidden(k4_tarski(esk7_3(X33,X34,X35),X35),X33)
        | X34 != k2_relat_1(X33) )
      & ( ~ r2_hidden(k4_tarski(X38,X37),X33)
        | r2_hidden(X37,X34)
        | X34 != k2_relat_1(X33) )
      & ( ~ r2_hidden(esk8_2(X39,X40),X40)
        | ~ r2_hidden(k4_tarski(X42,esk8_2(X39,X40)),X39)
        | X40 = k2_relat_1(X39) )
      & ( r2_hidden(esk8_2(X39,X40),X40)
        | r2_hidden(k4_tarski(esk9_2(X39,X40),esk8_2(X39,X40)),X39)
        | X40 = k2_relat_1(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_47,plain,
    ( r2_hidden(k4_tarski(X1,esk10_5(X2,X3,X4,X1,X5)),X2)
    | ~ r2_hidden(k4_tarski(X1,X5),X4)
    | X4 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(esk1_0),k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_51,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_53,plain,
    ( r2_hidden(k4_tarski(esk10_5(X1,X2,k5_relat_1(X1,X2),X3,X4),X4),X2)
    | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_42]),c_0_30])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(k4_tarski(esk15_1(k5_relat_1(esk1_0,esk2_0)),esk16_1(k5_relat_1(esk1_0,esk2_0))),k5_relat_1(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

cnf(c_0_55,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_56,plain,
    ( r2_hidden(k4_tarski(X1,esk10_5(X2,X3,k5_relat_1(X2,X3),X1,X4)),X2)
    | ~ r2_hidden(k4_tarski(X1,X4),k5_relat_1(X2,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_47]),c_0_30])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_58,negated_conjecture,
    ( k3_xboole_0(k2_relat_1(esk1_0),k1_relat_1(esk2_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_59,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_51]),c_0_41])])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(k4_tarski(esk10_5(esk1_0,esk2_0,k5_relat_1(esk1_0,esk2_0),esk15_1(k5_relat_1(esk1_0,esk2_0)),esk16_1(k5_relat_1(esk1_0,esk2_0))),esk16_1(k5_relat_1(esk1_0,esk2_0))),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_44]),c_0_37])])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(k4_tarski(esk15_1(k5_relat_1(esk1_0,esk2_0)),esk10_5(esk1_0,esk2_0,k5_relat_1(esk1_0,esk2_0),esk15_1(k5_relat_1(esk1_0,esk2_0)),esk16_1(k5_relat_1(esk1_0,esk2_0)))),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_54]),c_0_44]),c_0_37])])).

cnf(c_0_64,negated_conjecture,
    ( ~ r2_hidden(X1,k1_relat_1(esk2_0))
    | ~ r2_hidden(X1,k2_relat_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk10_5(esk1_0,esk2_0,k5_relat_1(esk1_0,esk2_0),esk15_1(k5_relat_1(esk1_0,esk2_0)),esk16_1(k5_relat_1(esk1_0,esk2_0))),k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk10_5(esk1_0,esk2_0,k5_relat_1(esk1_0,esk2_0),esk15_1(k5_relat_1(esk1_0,esk2_0)),esk16_1(k5_relat_1(esk1_0,esk2_0))),k2_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])]),
    [proof]).
%------------------------------------------------------------------------------
