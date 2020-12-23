%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_1__t159_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:17 EDT 2019

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 254 expanded)
%              Number of clauses        :   61 ( 115 expanded)
%              Number of leaves         :   16 (  63 expanded)
%              Depth                    :   12
%              Number of atoms          :  330 ( 946 expanded)
%              Number of equality atoms :   80 ( 190 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t159_funct_1.p',t5_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t159_funct_1.p',existence_m1_subset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t159_funct_1.p',t2_subset)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t159_funct_1.p',symmetry_r1_xboole_0)).

fof(t56_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t159_funct_1.p',t56_zfmisc_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t159_funct_1.p',t6_boole)).

fof(t159_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2] :
          ? [X3] : r1_tarski(k10_relat_1(X1,k1_tarski(X2)),k1_tarski(X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t159_funct_1.p',t159_funct_1)).

fof(t173_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k10_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t159_funct_1.p',t173_relat_1)).

fof(t39_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t159_funct_1.p',t39_zfmisc_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t159_funct_1.p',d1_tarski)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t159_funct_1.p',dt_o_0_0_xboole_0)).

fof(t144_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( ! [X2] :
            ~ ( r2_hidden(X2,k2_relat_1(X1))
              & ! [X3] : k10_relat_1(X1,k1_tarski(X2)) != k1_tarski(X3) )
      <=> v2_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t159_funct_1.p',t144_funct_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t159_funct_1.p',t2_xboole_1)).

fof(d13_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( X3 = k10_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ( r2_hidden(X4,k1_relat_1(X1))
                & r2_hidden(k1_funct_1(X1,X4),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t159_funct_1.p',d13_funct_1)).

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t159_funct_1.p',d5_funct_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t159_funct_1.p',t7_boole)).

fof(c_0_16,plain,(
    ! [X62,X63,X64] :
      ( ~ r2_hidden(X62,X63)
      | ~ m1_subset_1(X63,k1_zfmisc_1(X64))
      | ~ v1_xboole_0(X64) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_17,plain,(
    ! [X37] : m1_subset_1(esk9_1(X37),X37) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_18,plain,(
    ! [X50,X51] :
      ( ~ m1_subset_1(X50,X51)
      | v1_xboole_0(X51)
      | r2_hidden(X50,X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( m1_subset_1(esk9_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X39,X40] :
      ( ~ r1_xboole_0(X39,X40)
      | r1_xboole_0(X40,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_23,plain,(
    ! [X60,X61] :
      ( r2_hidden(X60,X61)
      | r1_xboole_0(k1_tarski(X60),X61) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_zfmisc_1])])])).

fof(c_0_24,plain,(
    ! [X65] :
      ( ~ v1_xboole_0(X65)
      | X65 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_25,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,esk9_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk9_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_20])).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
        <=> ! [X2] :
            ? [X3] : r1_tarski(k10_relat_1(X1,k1_tarski(X2)),k1_tarski(X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t159_funct_1])).

fof(c_0_28,plain,(
    ! [X46,X47] :
      ( ( k10_relat_1(X47,X46) != k1_xboole_0
        | r1_xboole_0(k2_relat_1(X47),X46)
        | ~ v1_relat_1(X47) )
      & ( ~ r1_xboole_0(k2_relat_1(X47),X46)
        | k10_relat_1(X47,X46) = k1_xboole_0
        | ~ v1_relat_1(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t173_relat_1])])])).

cnf(c_0_29,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( v1_xboole_0(esk9_1(k1_zfmisc_1(X1)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_33,plain,(
    ! [X53,X54] :
      ( ( ~ r1_tarski(X53,k1_tarski(X54))
        | X53 = k1_xboole_0
        | X53 = k1_tarski(X54) )
      & ( X53 != k1_xboole_0
        | r1_tarski(X53,k1_tarski(X54)) )
      & ( X53 != k1_tarski(X54)
        | r1_tarski(X53,k1_tarski(X54)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_zfmisc_1])])])).

fof(c_0_34,negated_conjecture,(
    ! [X7,X8] :
      ( v1_relat_1(esk1_0)
      & v1_funct_1(esk1_0)
      & ( ~ v2_funct_1(esk1_0)
        | ~ r1_tarski(k10_relat_1(esk1_0,k1_tarski(esk2_0)),k1_tarski(X7)) )
      & ( v2_funct_1(esk1_0)
        | r1_tarski(k10_relat_1(esk1_0,k1_tarski(X8)),k1_tarski(esk3_1(X8))) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])])).

cnf(c_0_35,plain,
    ( k10_relat_1(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( r1_xboole_0(X1,k1_tarski(X2))
    | r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( esk9_1(k1_zfmisc_1(X1)) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_38,plain,(
    ! [X20,X21,X22,X23,X24,X25] :
      ( ( ~ r2_hidden(X22,X21)
        | X22 = X20
        | X21 != k1_tarski(X20) )
      & ( X23 != X20
        | r2_hidden(X23,X21)
        | X21 != k1_tarski(X20) )
      & ( ~ r2_hidden(esk5_2(X24,X25),X25)
        | esk5_2(X24,X25) != X24
        | X25 = k1_tarski(X24) )
      & ( r2_hidden(esk5_2(X24,X25),X25)
        | esk5_2(X24,X25) = X24
        | X25 = k1_tarski(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_39,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

fof(c_0_40,plain,(
    ! [X41,X43,X44] :
      ( ( r2_hidden(esk10_1(X41),k2_relat_1(X41))
        | v2_funct_1(X41)
        | ~ v1_relat_1(X41)
        | ~ v1_funct_1(X41) )
      & ( k10_relat_1(X41,k1_tarski(esk10_1(X41))) != k1_tarski(X43)
        | v2_funct_1(X41)
        | ~ v1_relat_1(X41)
        | ~ v1_funct_1(X41) )
      & ( ~ v2_funct_1(X41)
        | ~ r2_hidden(X44,k2_relat_1(X41))
        | k10_relat_1(X41,k1_tarski(X44)) = k1_tarski(esk11_2(X41,X44))
        | ~ v1_relat_1(X41)
        | ~ v1_funct_1(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t144_funct_1])])])])])).

cnf(c_0_41,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( v2_funct_1(esk1_0)
    | r1_tarski(k10_relat_1(esk1_0,k1_tarski(X1)),k1_tarski(esk3_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,k1_tarski(X2))
    | X1 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,plain,
    ( k10_relat_1(X1,k1_tarski(X2)) = k1_xboole_0
    | r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_46,plain,(
    ! [X52] : r1_tarski(k1_xboole_0,X52) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_47,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_37])).

cnf(c_0_48,plain,
    ( r2_hidden(esk5_2(X1,X2),X2)
    | esk5_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_39])).

fof(c_0_50,plain,(
    ! [X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X15,k1_relat_1(X12))
        | ~ r2_hidden(X15,X14)
        | X14 != k10_relat_1(X12,X13)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( r2_hidden(k1_funct_1(X12,X15),X13)
        | ~ r2_hidden(X15,X14)
        | X14 != k10_relat_1(X12,X13)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( ~ r2_hidden(X16,k1_relat_1(X12))
        | ~ r2_hidden(k1_funct_1(X12,X16),X13)
        | r2_hidden(X16,X14)
        | X14 != k10_relat_1(X12,X13)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( ~ r2_hidden(esk4_3(X12,X17,X18),X18)
        | ~ r2_hidden(esk4_3(X12,X17,X18),k1_relat_1(X12))
        | ~ r2_hidden(k1_funct_1(X12,esk4_3(X12,X17,X18)),X17)
        | X18 = k10_relat_1(X12,X17)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( r2_hidden(esk4_3(X12,X17,X18),k1_relat_1(X12))
        | r2_hidden(esk4_3(X12,X17,X18),X18)
        | X18 = k10_relat_1(X12,X17)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( r2_hidden(k1_funct_1(X12,esk4_3(X12,X17,X18)),X17)
        | r2_hidden(esk4_3(X12,X17,X18),X18)
        | X18 = k10_relat_1(X12,X17)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_funct_1])])])])])])).

fof(c_0_51,plain,(
    ! [X27,X28,X29,X31,X32,X33,X35] :
      ( ( r2_hidden(esk6_3(X27,X28,X29),k1_relat_1(X27))
        | ~ r2_hidden(X29,X28)
        | X28 != k2_relat_1(X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( X29 = k1_funct_1(X27,esk6_3(X27,X28,X29))
        | ~ r2_hidden(X29,X28)
        | X28 != k2_relat_1(X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( ~ r2_hidden(X32,k1_relat_1(X27))
        | X31 != k1_funct_1(X27,X32)
        | r2_hidden(X31,X28)
        | X28 != k2_relat_1(X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( ~ r2_hidden(esk7_2(X27,X33),X33)
        | ~ r2_hidden(X35,k1_relat_1(X27))
        | esk7_2(X27,X33) != k1_funct_1(X27,X35)
        | X33 = k2_relat_1(X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( r2_hidden(esk8_2(X27,X33),k1_relat_1(X27))
        | r2_hidden(esk7_2(X27,X33),X33)
        | X33 = k2_relat_1(X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( esk7_2(X27,X33) = k1_funct_1(X27,esk8_2(X27,X33))
        | r2_hidden(esk7_2(X27,X33),X33)
        | X33 = k2_relat_1(X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_52,plain,
    ( v2_funct_1(X1)
    | k10_relat_1(X1,k1_tarski(esk10_1(X1))) != k1_tarski(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_53,negated_conjecture,
    ( k1_tarski(esk3_1(X1)) = k10_relat_1(esk1_0,k1_tarski(X1))
    | k10_relat_1(esk1_0,k1_tarski(X1)) = k1_xboole_0
    | v2_funct_1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_54,negated_conjecture,
    ( ~ v2_funct_1(esk1_0)
    | ~ r1_tarski(k10_relat_1(esk1_0,k1_tarski(esk2_0)),k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_55,plain,
    ( k10_relat_1(X1,k1_tarski(X2)) = k1_tarski(esk11_2(X1,X2))
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_56,plain,
    ( r1_tarski(k1_tarski(X1),k1_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_57,negated_conjecture,
    ( k10_relat_1(esk1_0,k1_tarski(X1)) = k1_xboole_0
    | r2_hidden(X1,k2_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_58,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_59,plain,(
    ! [X66,X67] :
      ( ~ r2_hidden(X66,X67)
      | ~ v1_xboole_0(X67) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_61,plain,
    ( esk5_2(X1,k1_xboole_0) = X1
    | k1_tarski(X1) = k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_62,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_39,c_0_49])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k1_funct_1(X2,X1),X3)
    | X4 != k10_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_64,plain,
    ( X1 = k1_funct_1(X2,esk6_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_65,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_66,negated_conjecture,
    ( k10_relat_1(esk1_0,k1_tarski(X1)) = k1_xboole_0
    | v2_funct_1(esk1_0)
    | v2_funct_1(X2)
    | k10_relat_1(X2,k1_tarski(esk10_1(X2))) != k10_relat_1(esk1_0,k1_tarski(X1))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_67,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_68,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ r1_tarski(k10_relat_1(esk1_0,k1_tarski(esk2_0)),k10_relat_1(X2,k1_tarski(X1)))
    | ~ v2_funct_1(esk1_0)
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_69,plain,
    ( r1_tarski(k10_relat_1(X1,k1_tarski(X2)),k10_relat_1(X1,k1_tarski(X2)))
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_55])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk2_0,k2_relat_1(esk1_0))
    | ~ v2_funct_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_57]),c_0_58])])).

cnf(c_0_71,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_72,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_60])])).

cnf(c_0_73,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk5_2(X1,X2),X2)
    | esk5_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_74,plain,
    ( esk5_2(X1,k1_xboole_0) = X1
    | k1_tarski(X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ r2_hidden(k1_funct_1(X2,X1),X3)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_63])).

cnf(c_0_76,plain,
    ( k1_funct_1(X1,esk6_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_64])).

cnf(c_0_77,plain,
    ( r2_hidden(esk6_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_65])).

cnf(c_0_78,negated_conjecture,
    ( k10_relat_1(esk1_0,k1_tarski(esk10_1(esk1_0))) = k1_xboole_0
    | v2_funct_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_66]),c_0_67]),c_0_45])])).

cnf(c_0_79,negated_conjecture,
    ( ~ v2_funct_1(esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_67]),c_0_45])]),c_0_70])).

cnf(c_0_80,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_81,plain,
    ( k1_tarski(X1) = k1_xboole_0
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_82,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_83,plain,
    ( r2_hidden(esk10_1(X1),k2_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_84,plain,
    ( r2_hidden(esk6_3(X1,k2_relat_1(X1),X2),k10_relat_1(X1,X3))
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ r2_hidden(X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77])).

cnf(c_0_85,negated_conjecture,
    ( k10_relat_1(esk1_0,k1_tarski(esk10_1(esk1_0))) = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_86,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_62])])).

cnf(c_0_87,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_82])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(esk10_1(esk1_0),k2_relat_1(esk1_0))
    | v2_funct_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_67]),c_0_45])])).

cnf(c_0_89,negated_conjecture,
    ( ~ r2_hidden(X1,k1_tarski(esk10_1(esk1_0)))
    | ~ r2_hidden(X1,k2_relat_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_67]),c_0_45])]),c_0_86])).

cnf(c_0_90,plain,
    ( esk9_1(k1_tarski(X1)) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_26]),c_0_80])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(esk10_1(esk1_0),k2_relat_1(esk1_0)) ),
    inference(sr,[status(thm)],[c_0_88,c_0_79])).

cnf(c_0_92,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_26]),c_0_90]),c_0_91])]),c_0_80]),
    [proof]).
%------------------------------------------------------------------------------
