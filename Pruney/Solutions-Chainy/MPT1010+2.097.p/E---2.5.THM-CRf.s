%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:05:25 EST 2020

% Result     : Theorem 6.62s
% Output     : CNFRefutation 6.62s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 179 expanded)
%              Number of clauses        :   46 (  80 expanded)
%              Number of leaves         :   15 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  280 ( 665 expanded)
%              Number of equality atoms :  109 ( 218 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   26 (   2 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(l44_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_tarski(X2)
        & X1 != k1_xboole_0
        & ! [X3] :
            ~ ( r2_hidden(X3,X1)
              & X3 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t65_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,k1_tarski(X2))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
     => ( r2_hidden(X3,X1)
       => k1_funct_1(X4,X3) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

fof(s3_funct_1__e15_31__wellord2,axiom,(
    ! [X1] :
    ? [X2] :
      ( v1_relat_1(X2)
      & v1_funct_1(X2)
      & k1_relat_1(X2) = X1
      & ! [X3] :
          ( r2_hidden(X3,X1)
         => k1_funct_1(X2,X3) = k1_tarski(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e15_31__wellord2)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(d1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => ( v1_funct_2(X3,X1,X2)
          <=> X1 = k1_relset_1(X1,X2,X3) ) )
        & ( X2 = k1_xboole_0
         => ( X1 = k1_xboole_0
            | ( v1_funct_2(X3,X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(t172_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k1_relat_1(X2))
         => r2_hidden(k1_funct_1(X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(c_0_15,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k4_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_17,plain,(
    ! [X40,X41,X42,X44] :
      ( ( r2_hidden(esk5_3(X40,X41,X42),k1_relat_1(X42))
        | ~ r2_hidden(X40,k9_relat_1(X42,X41))
        | ~ v1_relat_1(X42) )
      & ( r2_hidden(k4_tarski(esk5_3(X40,X41,X42),X40),X42)
        | ~ r2_hidden(X40,k9_relat_1(X42,X41))
        | ~ v1_relat_1(X42) )
      & ( r2_hidden(esk5_3(X40,X41,X42),X41)
        | ~ r2_hidden(X40,k9_relat_1(X42,X41))
        | ~ v1_relat_1(X42) )
      & ( ~ r2_hidden(X44,k1_relat_1(X42))
        | ~ r2_hidden(k4_tarski(X44,X40),X42)
        | ~ r2_hidden(X44,X41)
        | r2_hidden(X40,k9_relat_1(X42,X41))
        | ~ v1_relat_1(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

fof(c_0_18,plain,(
    ! [X21,X22,X23,X24,X25,X26,X27,X28] :
      ( ( ~ r2_hidden(X24,X23)
        | X24 = X21
        | X24 = X22
        | X23 != k2_tarski(X21,X22) )
      & ( X25 != X21
        | r2_hidden(X25,X23)
        | X23 != k2_tarski(X21,X22) )
      & ( X25 != X22
        | r2_hidden(X25,X23)
        | X23 != k2_tarski(X21,X22) )
      & ( esk3_3(X26,X27,X28) != X26
        | ~ r2_hidden(esk3_3(X26,X27,X28),X28)
        | X28 = k2_tarski(X26,X27) )
      & ( esk3_3(X26,X27,X28) != X27
        | ~ r2_hidden(esk3_3(X26,X27,X28),X28)
        | X28 = k2_tarski(X26,X27) )
      & ( r2_hidden(esk3_3(X26,X27,X28),X28)
        | esk3_3(X26,X27,X28) = X26
        | esk3_3(X26,X27,X28) = X27
        | X28 = k2_tarski(X26,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_19,plain,(
    ! [X31,X32] : k1_enumset1(X31,X31,X32) = k2_tarski(X31,X32) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_24,plain,(
    ! [X33,X34] :
      ( ( r2_hidden(esk4_2(X33,X34),X33)
        | X33 = k1_tarski(X34)
        | X33 = k1_xboole_0 )
      & ( esk4_2(X33,X34) != X34
        | X33 = k1_tarski(X34)
        | X33 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_zfmisc_1])])])])).

fof(c_0_25,plain,(
    ! [X30] : k2_tarski(X30,X30) = k1_tarski(X30) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,k1_tarski(X2))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
       => ( r2_hidden(X3,X1)
         => k1_funct_1(X4,X3) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t65_funct_2])).

cnf(c_0_27,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(esk5_3(X2,k4_xboole_0(X3,X4),X1),X4)
    | ~ r2_hidden(X2,k9_relat_1(X1,k4_xboole_0(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),k1_relat_1(X3))
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_29,plain,(
    ! [X54,X56] :
      ( v1_relat_1(esk6_1(X54))
      & v1_funct_1(esk6_1(X54))
      & k1_relat_1(esk6_1(X54)) = X54
      & ( ~ r2_hidden(X56,X54)
        | k1_funct_1(esk6_1(X54),X56) = k1_tarski(X56) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e15_31__wellord2])])])])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X4,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | X1 = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_33,plain,(
    ! [X14,X15,X16,X17,X18,X19] :
      ( ( ~ r2_hidden(X16,X15)
        | X16 = X14
        | X15 != k1_tarski(X14) )
      & ( X17 != X14
        | r2_hidden(X17,X15)
        | X15 != k1_tarski(X14) )
      & ( ~ r2_hidden(esk2_2(X18,X19),X19)
        | esk2_2(X18,X19) != X18
        | X19 = k1_tarski(X18) )
      & ( r2_hidden(esk2_2(X18,X19),X19)
        | esk2_2(X18,X19) = X18
        | X19 = k1_tarski(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_34,plain,(
    ! [X51,X52,X53] :
      ( ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
      | k1_relset_1(X51,X52,X53) = k1_relat_1(X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_35,plain,(
    ! [X57,X58,X59] :
      ( ( ~ v1_funct_2(X59,X57,X58)
        | X57 = k1_relset_1(X57,X58,X59)
        | X58 = k1_xboole_0
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58))) )
      & ( X57 != k1_relset_1(X57,X58,X59)
        | v1_funct_2(X59,X57,X58)
        | X58 = k1_xboole_0
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58))) )
      & ( ~ v1_funct_2(X59,X57,X58)
        | X57 = k1_relset_1(X57,X58,X59)
        | X57 != k1_xboole_0
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58))) )
      & ( X57 != k1_relset_1(X57,X58,X59)
        | v1_funct_2(X59,X57,X58)
        | X57 != k1_xboole_0
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58))) )
      & ( ~ v1_funct_2(X59,X57,X58)
        | X59 = k1_xboole_0
        | X57 = k1_xboole_0
        | X58 != k1_xboole_0
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58))) )
      & ( X59 != k1_xboole_0
        | v1_funct_2(X59,X57,X58)
        | X57 = k1_xboole_0
        | X58 != k1_xboole_0
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_36,negated_conjecture,
    ( v1_funct_1(esk10_0)
    & v1_funct_2(esk10_0,esk7_0,k1_tarski(esk8_0))
    & m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k1_tarski(esk8_0))))
    & r2_hidden(esk9_0,esk7_0)
    & k1_funct_1(esk10_0,esk9_0) != esk8_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).

cnf(c_0_37,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,k4_xboole_0(X3,k1_relat_1(X1)))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_38,plain,
    ( k1_relat_1(esk6_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( v1_relat_1(esk6_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_30])])).

cnf(c_0_41,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_enumset1(X2,X2,X2)
    | r2_hidden(esk4_2(X1,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_23])).

cnf(c_0_42,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_44,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k1_tarski(esk8_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_2(esk10_0,esk7_0,k1_tarski(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(X1,k9_relat_1(esk6_1(X2),k4_xboole_0(X3,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk4_2(X1,X2),X1)
    | r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_50,plain,
    ( X1 = X3
    | X2 != k1_enumset1(X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_32]),c_0_23])).

fof(c_0_51,plain,(
    ! [X45,X46,X47] :
      ( ~ v1_relat_1(X46)
      | ~ v5_relat_1(X46,X45)
      | ~ v1_funct_1(X46)
      | ~ r2_hidden(X47,k1_relat_1(X46))
      | r2_hidden(k1_funct_1(X46,X47),X45) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t172_funct_1])])])).

fof(c_0_52,plain,(
    ! [X48,X49,X50] :
      ( ( v4_relat_1(X50,X48)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) )
      & ( v5_relat_1(X50,X49)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_53,plain,(
    ! [X36,X37] :
      ( ~ v1_relat_1(X36)
      | ~ m1_subset_1(X37,k1_zfmisc_1(X36))
      | v1_relat_1(X37) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_54,plain,(
    ! [X38,X39] : v1_relat_1(k2_zfmisc_1(X38,X39)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X2,X4) ),
    inference(rw,[status(thm)],[c_0_43,c_0_23])).

cnf(c_0_56,plain,
    ( X1 = k1_relat_1(X2)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k1_enumset1(esk8_0,esk8_0,esk8_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_32]),c_0_23])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_2(esk10_0,esk7_0,k1_enumset1(esk8_0,esk8_0,esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_32]),c_0_23])).

cnf(c_0_59,plain,
    ( k9_relat_1(esk6_1(X1),k4_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_48])).

cnf(c_0_60,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_enumset1(X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_61,plain,
    ( r2_hidden(k1_funct_1(X1,X3),X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_62,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_63,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_64,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_55])])).

cnf(c_0_66,negated_conjecture,
    ( k1_enumset1(esk8_0,esk8_0,esk8_0) = k1_xboole_0
    | k1_relat_1(esk10_0) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])])).

cnf(c_0_67,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_48,c_0_59])).

cnf(c_0_68,plain,
    ( k1_funct_1(X1,X2) = X3
    | ~ v1_funct_1(X1)
    | ~ v5_relat_1(X1,k1_enumset1(X3,X3,X3))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( v5_relat_1(esk10_0,k1_enumset1(esk8_0,esk8_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_57])).

cnf(c_0_70,negated_conjecture,
    ( v1_funct_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_71,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_57]),c_0_64])])).

cnf(c_0_72,negated_conjecture,
    ( k1_relat_1(esk10_0) = esk7_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( k1_funct_1(esk10_0,esk9_0) != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_74,negated_conjecture,
    ( k1_funct_1(esk10_0,X1) = esk8_0
    | ~ r2_hidden(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),c_0_71]),c_0_72])])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk9_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:22:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 6.62/6.80  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 6.62/6.80  # and selection function SelectMaxLComplexAvoidPosPred.
% 6.62/6.80  #
% 6.62/6.80  # Preprocessing time       : 0.047 s
% 6.62/6.80  
% 6.62/6.80  # Proof found!
% 6.62/6.80  # SZS status Theorem
% 6.62/6.80  # SZS output start CNFRefutation
% 6.62/6.80  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 6.62/6.80  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 6.62/6.80  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 6.62/6.80  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 6.62/6.80  fof(l44_zfmisc_1, axiom, ![X1, X2]:~(((X1!=k1_tarski(X2)&X1!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X1)&X3!=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 6.62/6.80  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.62/6.80  fof(t65_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 6.62/6.80  fof(s3_funct_1__e15_31__wellord2, axiom, ![X1]:?[X2]:(((v1_relat_1(X2)&v1_funct_1(X2))&k1_relat_1(X2)=X1)&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=k1_tarski(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e15_31__wellord2)).
% 6.62/6.80  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 6.62/6.80  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.62/6.80  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 6.62/6.80  fof(t172_funct_1, axiom, ![X1, X2]:(((v1_relat_1(X2)&v5_relat_1(X2,X1))&v1_funct_1(X2))=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 6.62/6.80  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.62/6.80  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.62/6.80  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.62/6.80  fof(c_0_15, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 6.62/6.80  cnf(c_0_16, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 6.62/6.80  fof(c_0_17, plain, ![X40, X41, X42, X44]:((((r2_hidden(esk5_3(X40,X41,X42),k1_relat_1(X42))|~r2_hidden(X40,k9_relat_1(X42,X41))|~v1_relat_1(X42))&(r2_hidden(k4_tarski(esk5_3(X40,X41,X42),X40),X42)|~r2_hidden(X40,k9_relat_1(X42,X41))|~v1_relat_1(X42)))&(r2_hidden(esk5_3(X40,X41,X42),X41)|~r2_hidden(X40,k9_relat_1(X42,X41))|~v1_relat_1(X42)))&(~r2_hidden(X44,k1_relat_1(X42))|~r2_hidden(k4_tarski(X44,X40),X42)|~r2_hidden(X44,X41)|r2_hidden(X40,k9_relat_1(X42,X41))|~v1_relat_1(X42))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 6.62/6.80  fof(c_0_18, plain, ![X21, X22, X23, X24, X25, X26, X27, X28]:(((~r2_hidden(X24,X23)|(X24=X21|X24=X22)|X23!=k2_tarski(X21,X22))&((X25!=X21|r2_hidden(X25,X23)|X23!=k2_tarski(X21,X22))&(X25!=X22|r2_hidden(X25,X23)|X23!=k2_tarski(X21,X22))))&(((esk3_3(X26,X27,X28)!=X26|~r2_hidden(esk3_3(X26,X27,X28),X28)|X28=k2_tarski(X26,X27))&(esk3_3(X26,X27,X28)!=X27|~r2_hidden(esk3_3(X26,X27,X28),X28)|X28=k2_tarski(X26,X27)))&(r2_hidden(esk3_3(X26,X27,X28),X28)|(esk3_3(X26,X27,X28)=X26|esk3_3(X26,X27,X28)=X27)|X28=k2_tarski(X26,X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 6.62/6.80  fof(c_0_19, plain, ![X31, X32]:k1_enumset1(X31,X31,X32)=k2_tarski(X31,X32), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 6.62/6.80  cnf(c_0_20, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_16])).
% 6.62/6.80  cnf(c_0_21, plain, (r2_hidden(esk5_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 6.62/6.80  cnf(c_0_22, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 6.62/6.80  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 6.62/6.80  fof(c_0_24, plain, ![X33, X34]:((r2_hidden(esk4_2(X33,X34),X33)|(X33=k1_tarski(X34)|X33=k1_xboole_0))&(esk4_2(X33,X34)!=X34|(X33=k1_tarski(X34)|X33=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_zfmisc_1])])])])).
% 6.62/6.80  fof(c_0_25, plain, ![X30]:k2_tarski(X30,X30)=k1_tarski(X30), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 6.62/6.80  fof(c_0_26, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2))), inference(assume_negation,[status(cth)],[t65_funct_2])).
% 6.62/6.80  cnf(c_0_27, plain, (~v1_relat_1(X1)|~r2_hidden(esk5_3(X2,k4_xboole_0(X3,X4),X1),X4)|~r2_hidden(X2,k9_relat_1(X1,k4_xboole_0(X3,X4)))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 6.62/6.80  cnf(c_0_28, plain, (r2_hidden(esk5_3(X1,X2,X3),k1_relat_1(X3))|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 6.62/6.80  fof(c_0_29, plain, ![X54, X56]:(((v1_relat_1(esk6_1(X54))&v1_funct_1(esk6_1(X54)))&k1_relat_1(esk6_1(X54))=X54)&(~r2_hidden(X56,X54)|k1_funct_1(esk6_1(X54),X56)=k1_tarski(X56))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e15_31__wellord2])])])])).
% 6.62/6.80  cnf(c_0_30, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X4,X2)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 6.62/6.80  cnf(c_0_31, plain, (r2_hidden(esk4_2(X1,X2),X1)|X1=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 6.62/6.80  cnf(c_0_32, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 6.62/6.80  fof(c_0_33, plain, ![X14, X15, X16, X17, X18, X19]:(((~r2_hidden(X16,X15)|X16=X14|X15!=k1_tarski(X14))&(X17!=X14|r2_hidden(X17,X15)|X15!=k1_tarski(X14)))&((~r2_hidden(esk2_2(X18,X19),X19)|esk2_2(X18,X19)!=X18|X19=k1_tarski(X18))&(r2_hidden(esk2_2(X18,X19),X19)|esk2_2(X18,X19)=X18|X19=k1_tarski(X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 6.62/6.80  fof(c_0_34, plain, ![X51, X52, X53]:(~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))|k1_relset_1(X51,X52,X53)=k1_relat_1(X53)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 6.62/6.80  fof(c_0_35, plain, ![X57, X58, X59]:((((~v1_funct_2(X59,X57,X58)|X57=k1_relset_1(X57,X58,X59)|X58=k1_xboole_0|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58))))&(X57!=k1_relset_1(X57,X58,X59)|v1_funct_2(X59,X57,X58)|X58=k1_xboole_0|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58)))))&((~v1_funct_2(X59,X57,X58)|X57=k1_relset_1(X57,X58,X59)|X57!=k1_xboole_0|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58))))&(X57!=k1_relset_1(X57,X58,X59)|v1_funct_2(X59,X57,X58)|X57!=k1_xboole_0|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58))))))&((~v1_funct_2(X59,X57,X58)|X59=k1_xboole_0|X57=k1_xboole_0|X58!=k1_xboole_0|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58))))&(X59!=k1_xboole_0|v1_funct_2(X59,X57,X58)|X57=k1_xboole_0|X58!=k1_xboole_0|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 6.62/6.80  fof(c_0_36, negated_conjecture, (((v1_funct_1(esk10_0)&v1_funct_2(esk10_0,esk7_0,k1_tarski(esk8_0)))&m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k1_tarski(esk8_0)))))&(r2_hidden(esk9_0,esk7_0)&k1_funct_1(esk10_0,esk9_0)!=esk8_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).
% 6.62/6.80  cnf(c_0_37, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,k4_xboole_0(X3,k1_relat_1(X1))))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 6.62/6.80  cnf(c_0_38, plain, (k1_relat_1(esk6_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_29])).
% 6.62/6.80  cnf(c_0_39, plain, (v1_relat_1(esk6_1(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 6.62/6.80  cnf(c_0_40, plain, (r2_hidden(X1,k1_enumset1(X2,X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_30])])).
% 6.62/6.80  cnf(c_0_41, plain, (X1=k1_xboole_0|X1=k1_enumset1(X2,X2,X2)|r2_hidden(esk4_2(X1,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_23])).
% 6.62/6.80  cnf(c_0_42, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 6.62/6.80  cnf(c_0_43, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 6.62/6.80  cnf(c_0_44, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 6.62/6.80  cnf(c_0_45, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 6.62/6.80  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k1_tarski(esk8_0))))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 6.62/6.80  cnf(c_0_47, negated_conjecture, (v1_funct_2(esk10_0,esk7_0,k1_tarski(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 6.62/6.80  cnf(c_0_48, plain, (~r2_hidden(X1,k9_relat_1(esk6_1(X2),k4_xboole_0(X3,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])])).
% 6.62/6.80  cnf(c_0_49, plain, (X1=k1_xboole_0|r2_hidden(esk4_2(X1,X2),X1)|r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 6.62/6.80  cnf(c_0_50, plain, (X1=X3|X2!=k1_enumset1(X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_32]), c_0_23])).
% 6.62/6.80  fof(c_0_51, plain, ![X45, X46, X47]:(~v1_relat_1(X46)|~v5_relat_1(X46,X45)|~v1_funct_1(X46)|(~r2_hidden(X47,k1_relat_1(X46))|r2_hidden(k1_funct_1(X46,X47),X45))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t172_funct_1])])])).
% 6.62/6.80  fof(c_0_52, plain, ![X48, X49, X50]:((v4_relat_1(X50,X48)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))))&(v5_relat_1(X50,X49)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 6.62/6.80  fof(c_0_53, plain, ![X36, X37]:(~v1_relat_1(X36)|(~m1_subset_1(X37,k1_zfmisc_1(X36))|v1_relat_1(X37))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 6.62/6.80  fof(c_0_54, plain, ![X38, X39]:v1_relat_1(k2_zfmisc_1(X38,X39)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 6.62/6.80  cnf(c_0_55, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X2,X4)), inference(rw,[status(thm)],[c_0_43, c_0_23])).
% 6.62/6.80  cnf(c_0_56, plain, (X1=k1_relat_1(X2)|X3=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 6.62/6.80  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk10_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,k1_enumset1(esk8_0,esk8_0,esk8_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_32]), c_0_23])).
% 6.62/6.80  cnf(c_0_58, negated_conjecture, (v1_funct_2(esk10_0,esk7_0,k1_enumset1(esk8_0,esk8_0,esk8_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_32]), c_0_23])).
% 6.62/6.80  cnf(c_0_59, plain, (k9_relat_1(esk6_1(X1),k4_xboole_0(X2,X1))=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_48])).
% 6.62/6.80  cnf(c_0_60, plain, (X1=X2|~r2_hidden(X1,k1_enumset1(X2,X2,X2))), inference(er,[status(thm)],[c_0_50])).
% 6.62/6.80  cnf(c_0_61, plain, (r2_hidden(k1_funct_1(X1,X3),X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 6.62/6.80  cnf(c_0_62, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 6.62/6.80  cnf(c_0_63, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 6.62/6.80  cnf(c_0_64, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 6.62/6.80  cnf(c_0_65, plain, (r2_hidden(X1,k1_enumset1(X1,X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_55])])).
% 6.62/6.80  cnf(c_0_66, negated_conjecture, (k1_enumset1(esk8_0,esk8_0,esk8_0)=k1_xboole_0|k1_relat_1(esk10_0)=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])])).
% 6.62/6.80  cnf(c_0_67, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_48, c_0_59])).
% 6.62/6.80  cnf(c_0_68, plain, (k1_funct_1(X1,X2)=X3|~v1_funct_1(X1)|~v5_relat_1(X1,k1_enumset1(X3,X3,X3))|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 6.62/6.80  cnf(c_0_69, negated_conjecture, (v5_relat_1(esk10_0,k1_enumset1(esk8_0,esk8_0,esk8_0))), inference(spm,[status(thm)],[c_0_62, c_0_57])).
% 6.62/6.80  cnf(c_0_70, negated_conjecture, (v1_funct_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 6.62/6.80  cnf(c_0_71, negated_conjecture, (v1_relat_1(esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_57]), c_0_64])])).
% 6.62/6.80  cnf(c_0_72, negated_conjecture, (k1_relat_1(esk10_0)=esk7_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])).
% 6.62/6.80  cnf(c_0_73, negated_conjecture, (k1_funct_1(esk10_0,esk9_0)!=esk8_0), inference(split_conjunct,[status(thm)],[c_0_36])).
% 6.62/6.80  cnf(c_0_74, negated_conjecture, (k1_funct_1(esk10_0,X1)=esk8_0|~r2_hidden(X1,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), c_0_71]), c_0_72])])).
% 6.62/6.80  cnf(c_0_75, negated_conjecture, (r2_hidden(esk9_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 6.62/6.80  cnf(c_0_76, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75])]), ['proof']).
% 6.62/6.80  # SZS output end CNFRefutation
% 6.62/6.80  # Proof object total steps             : 77
% 6.62/6.80  # Proof object clause steps            : 46
% 6.62/6.80  # Proof object formula steps           : 31
% 6.62/6.80  # Proof object conjectures             : 16
% 6.62/6.80  # Proof object clause conjectures      : 13
% 6.62/6.80  # Proof object formula conjectures     : 3
% 6.62/6.80  # Proof object initial clauses used    : 22
% 6.62/6.80  # Proof object initial formulas used   : 15
% 6.62/6.80  # Proof object generating inferences   : 13
% 6.62/6.80  # Proof object simplifying inferences  : 31
% 6.62/6.80  # Training examples: 0 positive, 0 negative
% 6.62/6.80  # Parsed axioms                        : 15
% 6.62/6.80  # Removed by relevancy pruning/SinE    : 0
% 6.62/6.80  # Initial clauses                      : 45
% 6.62/6.80  # Removed in clause preprocessing      : 2
% 6.62/6.80  # Initial clauses in saturation        : 43
% 6.62/6.80  # Processed clauses                    : 5298
% 6.62/6.80  # ...of these trivial                  : 16
% 6.62/6.80  # ...subsumed                          : 4027
% 6.62/6.80  # ...remaining for further processing  : 1255
% 6.62/6.80  # Other redundant clauses eliminated   : 979
% 6.62/6.80  # Clauses deleted for lack of memory   : 0
% 6.62/6.80  # Backward-subsumed                    : 75
% 6.62/6.80  # Backward-rewritten                   : 34
% 6.62/6.80  # Generated clauses                    : 492688
% 6.62/6.80  # ...of the previous two non-trivial   : 484955
% 6.62/6.80  # Contextual simplify-reflections      : 24
% 6.62/6.80  # Paramodulations                      : 491519
% 6.62/6.80  # Factorizations                       : 194
% 6.62/6.80  # Equation resolutions                 : 979
% 6.62/6.80  # Propositional unsat checks           : 0
% 6.62/6.80  #    Propositional check models        : 0
% 6.62/6.80  #    Propositional check unsatisfiable : 0
% 6.62/6.80  #    Propositional clauses             : 0
% 6.62/6.80  #    Propositional clauses after purity: 0
% 6.62/6.80  #    Propositional unsat core size     : 0
% 6.62/6.80  #    Propositional preprocessing time  : 0.000
% 6.62/6.80  #    Propositional encoding time       : 0.000
% 6.62/6.80  #    Propositional solver time         : 0.000
% 6.62/6.80  #    Success case prop preproc time    : 0.000
% 6.62/6.80  #    Success case prop encoding time   : 0.000
% 6.62/6.80  #    Success case prop solver time     : 0.000
% 6.62/6.80  # Current number of processed clauses  : 1134
% 6.62/6.80  #    Positive orientable unit clauses  : 25
% 6.62/6.80  #    Positive unorientable unit clauses: 0
% 6.62/6.80  #    Negative unit clauses             : 2
% 6.62/6.80  #    Non-unit-clauses                  : 1107
% 6.62/6.80  # Current number of unprocessed clauses: 478820
% 6.62/6.80  # ...number of literals in the above   : 3303133
% 6.62/6.80  # Current number of archived formulas  : 0
% 6.62/6.80  # Current number of archived clauses   : 111
% 6.62/6.80  # Clause-clause subsumption calls (NU) : 265954
% 6.62/6.80  # Rec. Clause-clause subsumption calls : 38703
% 6.62/6.80  # Non-unit clause-clause subsumptions  : 3672
% 6.62/6.80  # Unit Clause-clause subsumption calls : 811
% 6.62/6.80  # Rewrite failures with RHS unbound    : 0
% 6.62/6.80  # BW rewrite match attempts            : 44
% 6.62/6.80  # BW rewrite match successes           : 15
% 6.62/6.80  # Condensation attempts                : 0
% 6.62/6.80  # Condensation successes               : 0
% 6.62/6.80  # Termbank termtop insertions          : 11966047
% 6.62/6.82  
% 6.62/6.82  # -------------------------------------------------
% 6.62/6.82  # User time                : 6.254 s
% 6.62/6.82  # System time              : 0.219 s
% 6.62/6.82  # Total time               : 6.473 s
% 6.62/6.82  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
