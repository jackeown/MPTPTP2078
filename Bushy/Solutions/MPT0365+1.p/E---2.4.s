%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : subset_1__t46_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:23 EDT 2019

% Result     : Theorem 197.49s
% Output     : CNFRefutation 197.49s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 607 expanded)
%              Number of clauses        :  106 ( 306 expanded)
%              Number of leaves         :   15 ( 142 expanded)
%              Depth                    :   20
%              Number of atoms          :  314 (2287 expanded)
%              Number of equality atoms :   60 ( 428 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t46_subset_1.p',d5_xboole_0)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/subset_1__t46_subset_1.p',t4_boole)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t46_subset_1.p',d1_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t46_subset_1.p',d10_xboole_0)).

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
    file('/export/starexec/sandbox/benchmark/subset_1__t46_subset_1.p',t3_xboole_0)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t46_subset_1.p',symmetry_r1_xboole_0)).

fof(t46_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ( r1_xboole_0(X2,X3)
              & r1_xboole_0(k3_subset_1(X1,X2),k3_subset_1(X1,X3)) )
           => X2 = k3_subset_1(X1,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t46_subset_1.p',t46_subset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t46_subset_1.p',d3_tarski)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t46_subset_1.p',d2_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t46_subset_1.p',fc1_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t46_subset_1.p',dt_k3_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t46_subset_1.p',d5_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t46_subset_1.p',involutiveness_k3_subset_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t46_subset_1.p',t7_boole)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/subset_1__t46_subset_1.p',t3_boole)).

fof(c_0_15,plain,(
    ! [X29,X30,X31,X32,X33,X34,X35,X36] :
      ( ( r2_hidden(X32,X29)
        | ~ r2_hidden(X32,X31)
        | X31 != k4_xboole_0(X29,X30) )
      & ( ~ r2_hidden(X32,X30)
        | ~ r2_hidden(X32,X31)
        | X31 != k4_xboole_0(X29,X30) )
      & ( ~ r2_hidden(X33,X29)
        | r2_hidden(X33,X30)
        | r2_hidden(X33,X31)
        | X31 != k4_xboole_0(X29,X30) )
      & ( ~ r2_hidden(esk6_3(X34,X35,X36),X36)
        | ~ r2_hidden(esk6_3(X34,X35,X36),X34)
        | r2_hidden(esk6_3(X34,X35,X36),X35)
        | X36 = k4_xboole_0(X34,X35) )
      & ( r2_hidden(esk6_3(X34,X35,X36),X34)
        | r2_hidden(esk6_3(X34,X35,X36),X36)
        | X36 = k4_xboole_0(X34,X35) )
      & ( ~ r2_hidden(esk6_3(X34,X35,X36),X35)
        | r2_hidden(esk6_3(X34,X35,X36),X36)
        | X36 = k4_xboole_0(X34,X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_17,plain,(
    ! [X53] : k4_xboole_0(k1_xboole_0,X53) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_18,plain,(
    ! [X12,X13,X14,X15,X16,X17] :
      ( ( ~ r2_hidden(X14,X13)
        | r1_tarski(X14,X12)
        | X13 != k1_zfmisc_1(X12) )
      & ( ~ r1_tarski(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k1_zfmisc_1(X12) )
      & ( ~ r2_hidden(esk4_2(X16,X17),X17)
        | ~ r1_tarski(esk4_2(X16,X17),X16)
        | X17 = k1_zfmisc_1(X16) )
      & ( r2_hidden(esk4_2(X16,X17),X17)
        | r1_tarski(esk4_2(X16,X17),X16)
        | X17 = k1_zfmisc_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_19,plain,(
    ! [X10,X11] :
      ( ( r1_tarski(X10,X11)
        | X10 != X11 )
      & ( r1_tarski(X11,X10)
        | X10 != X11 )
      & ( ~ r1_tarski(X10,X11)
        | ~ r1_tarski(X11,X10)
        | X10 = X11 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X47,X48,X50,X51,X52] :
      ( ( r2_hidden(esk8_2(X47,X48),X47)
        | r1_xboole_0(X47,X48) )
      & ( r2_hidden(esk8_2(X47,X48),X48)
        | r1_xboole_0(X47,X48) )
      & ( ~ r2_hidden(X52,X50)
        | ~ r2_hidden(X52,X51)
        | ~ r1_xboole_0(X50,X51) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( r2_hidden(esk8_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_24])).

fof(c_0_29,plain,(
    ! [X44,X45] :
      ( ~ r1_xboole_0(X44,X45)
      | r1_xboole_0(X45,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_30,plain,
    ( r1_xboole_0(X1,k1_xboole_0)
    | ~ r2_hidden(esk8_2(X1,k1_xboole_0),X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_32,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( ( r1_xboole_0(X2,X3)
                & r1_xboole_0(k3_subset_1(X1,X2),k3_subset_1(X1,X3)) )
             => X2 = k3_subset_1(X1,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t46_subset_1])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_37,plain,(
    ! [X21,X22,X23,X24,X25] :
      ( ( ~ r1_tarski(X21,X22)
        | ~ r2_hidden(X23,X21)
        | r2_hidden(X23,X22) )
      & ( r2_hidden(esk5_2(X24,X25),X24)
        | r1_tarski(X24,X25) )
      & ( ~ r2_hidden(esk5_2(X24,X25),X25)
        | r1_tarski(X24,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_38,plain,(
    ! [X19,X20] :
      ( ( ~ m1_subset_1(X20,X19)
        | r2_hidden(X20,X19)
        | v1_xboole_0(X19) )
      & ( ~ r2_hidden(X20,X19)
        | m1_subset_1(X20,X19)
        | v1_xboole_0(X19) )
      & ( ~ m1_subset_1(X20,X19)
        | v1_xboole_0(X20)
        | ~ v1_xboole_0(X19) )
      & ( ~ v1_xboole_0(X20)
        | m1_subset_1(X20,X19)
        | ~ v1_xboole_0(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_39,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))
    & r1_xboole_0(esk2_0,esk3_0)
    & r1_xboole_0(k3_subset_1(esk1_0,esk2_0),k3_subset_1(esk1_0,esk3_0))
    & esk2_0 != k3_subset_1(esk1_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).

fof(c_0_40,plain,(
    ! [X59] : ~ v1_xboole_0(k1_zfmisc_1(X59)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_31])).

cnf(c_0_42,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_43,plain,(
    ! [X38,X39] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(X38))
      | m1_subset_1(k3_subset_1(X38,X39),k1_zfmisc_1(X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_44,plain,(
    ! [X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(X27))
      | k3_subset_1(X27,X28) = k4_xboole_0(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_45,plain,(
    ! [X42,X43] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(X42))
      | k3_subset_1(X42,k3_subset_1(X42,X43)) = X43 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( r2_hidden(esk5_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_51,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_52,plain,(
    ! [X55,X56] :
      ( ~ r2_hidden(X55,X56)
      | ~ v1_xboole_0(X56) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_53,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_54,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_55,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_56,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk5_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,X2)
    | r2_hidden(esk5_2(X1,X2),k4_xboole_0(X1,X3))
    | r2_hidden(esk5_2(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_62,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_63,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_64,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_47])).

cnf(c_0_65,plain,
    ( r2_hidden(esk8_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk1_0,esk3_0),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_50])).

cnf(c_0_67,negated_conjecture,
    ( k3_subset_1(esk1_0,esk3_0) = k4_xboole_0(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_50])).

cnf(c_0_68,negated_conjecture,
    ( k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk3_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_50])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk5_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_47])).

cnf(c_0_70,plain,
    ( r1_tarski(X1,k4_xboole_0(X1,X2))
    | r2_hidden(esk5_2(X1,k4_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_71,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_72,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_74,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_75,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_64])).

fof(c_0_76,plain,(
    ! [X46] : k4_xboole_0(X46,k1_xboole_0) = X46 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_77,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X3)
    | ~ r2_hidden(esk8_2(k4_xboole_0(X1,X2),X3),X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_65])).

cnf(c_0_78,plain,
    ( r2_hidden(esk8_2(X1,X2),k4_xboole_0(X2,X3))
    | r2_hidden(esk8_2(X1,X2),X3)
    | r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_26])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(k4_xboole_0(esk1_0,esk3_0),k1_zfmisc_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_80,negated_conjecture,
    ( k3_subset_1(esk1_0,k4_xboole_0(esk1_0,esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_68,c_0_67])).

cnf(c_0_81,plain,
    ( r1_tarski(X1,k4_xboole_0(X1,X2))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_82,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_83,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | r2_hidden(esk5_2(k4_xboole_0(X1,X2),X3),X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_47])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(X1,esk1_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_85,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_86,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_87,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_31])).

cnf(c_0_88,plain,
    ( r2_hidden(esk8_2(k4_xboole_0(X1,X2),X3),X1)
    | r1_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_71,c_0_65])).

cnf(c_0_89,plain,
    ( r2_hidden(esk8_2(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X2),X3)
    | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_90,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_79]),c_0_80])).

cnf(c_0_91,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(esk1_0,esk2_0),k3_subset_1(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_92,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_93,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_94,negated_conjecture,
    ( r1_tarski(esk3_0,k4_xboole_0(esk3_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_95,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_83])).

cnf(c_0_96,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | r2_hidden(esk5_2(esk3_0,X1),esk1_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_47])).

cnf(c_0_97,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_85]),c_0_86])).

cnf(c_0_98,plain,
    ( k3_subset_1(X1,X1) = k4_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_87])).

cnf(c_0_99,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X3)
    | ~ r2_hidden(esk8_2(k4_xboole_0(X1,X2),X3),X4)
    | ~ r1_xboole_0(X4,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_88])).

cnf(c_0_100,negated_conjecture,
    ( r2_hidden(esk8_2(k4_xboole_0(X1,esk3_0),esk1_0),k4_xboole_0(esk1_0,esk3_0))
    | r1_xboole_0(k4_xboole_0(X1,esk3_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_101,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(esk1_0,esk3_0),k3_subset_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_91])).

cnf(c_0_102,negated_conjecture,
    ( k3_subset_1(esk1_0,esk2_0) = k4_xboole_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_92])).

cnf(c_0_103,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r2_hidden(esk5_2(k4_xboole_0(X1,X2),X3),X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_47])).

cnf(c_0_104,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk2_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_95])])).

cnf(c_0_105,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | r2_hidden(esk5_2(esk3_0,X1),k4_xboole_0(esk1_0,X2))
    | r2_hidden(esk5_2(esk3_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_96])).

cnf(c_0_106,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk6_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_107,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X1)
    | r2_hidden(esk6_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_108,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_85]),c_0_97]),c_0_98])).

cnf(c_0_109,plain,
    ( r2_hidden(esk8_2(X1,k4_xboole_0(X2,X3)),X2)
    | r1_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_26])).

cnf(c_0_110,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(X1,esk3_0),esk1_0)
    | ~ r1_xboole_0(k4_xboole_0(esk1_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_111,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk1_0,esk3_0),k4_xboole_0(esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_67]),c_0_102])).

cnf(c_0_112,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | ~ r2_hidden(esk5_2(esk3_0,X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_113,negated_conjecture,
    ( r1_tarski(esk3_0,k4_xboole_0(esk1_0,X1))
    | r2_hidden(esk5_2(esk3_0,k4_xboole_0(esk1_0,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_105])).

cnf(c_0_114,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk6_3(X2,X2,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_108])).

cnf(c_0_115,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk8_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_26])).

cnf(c_0_116,plain,
    ( r2_hidden(esk8_2(X1,k4_xboole_0(k4_xboole_0(X2,X3),X4)),X2)
    | r1_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X3),X4)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_109])).

cnf(c_0_117,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(esk1_0,esk2_0),esk3_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_110,c_0_111])).

cnf(c_0_118,negated_conjecture,
    ( r1_tarski(esk3_0,k4_xboole_0(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_119,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(esk6_3(X2,X2,X1),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_114])).

cnf(c_0_120,plain,
    ( r1_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X3),X4))
    | ~ r1_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,X3),X4)) ),
    inference(spm,[status(thm)],[c_0_115,c_0_116])).

cnf(c_0_121,negated_conjecture,
    ( r1_xboole_0(esk1_0,k4_xboole_0(k4_xboole_0(esk1_0,esk2_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_117])).

cnf(c_0_122,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(k4_xboole_0(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_118])).

cnf(c_0_123,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(k1_zfmisc_1(esk6_3(X2,X2,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_119,c_0_31])).

cnf(c_0_124,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(k4_xboole_0(esk1_0,esk2_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_120,c_0_121])).

cnf(c_0_125,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk1_0,esk2_0),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_92])).

cnf(c_0_126,negated_conjecture,
    ( k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk2_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_92])).

cnf(c_0_127,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k4_xboole_0(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_122])).

cnf(c_0_128,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk1_0,esk2_0),esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_123,c_0_124])).

cnf(c_0_129,negated_conjecture,
    ( m1_subset_1(k4_xboole_0(esk1_0,esk2_0),k1_zfmisc_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_125,c_0_102])).

cnf(c_0_130,negated_conjecture,
    ( k3_subset_1(esk1_0,k4_xboole_0(esk1_0,esk2_0)) = esk2_0 ),
    inference(rw,[status(thm)],[c_0_126,c_0_102])).

cnf(c_0_131,negated_conjecture,
    ( k3_subset_1(k4_xboole_0(esk1_0,esk2_0),esk3_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_127]),c_0_128])).

cnf(c_0_132,negated_conjecture,
    ( esk2_0 != k3_subset_1(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_133,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_129]),c_0_130])).

cnf(c_0_134,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk2_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_127]),c_0_131]),c_0_97])).

cnf(c_0_135,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk3_0) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_132,c_0_67])).

cnf(c_0_136,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_133,c_0_134]),c_0_135]),
    [proof]).
%------------------------------------------------------------------------------
