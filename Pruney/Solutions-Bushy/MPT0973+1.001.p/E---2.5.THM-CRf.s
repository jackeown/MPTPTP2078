%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0973+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:30 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  130 (7835 expanded)
%              Number of clauses        :   94 (3731 expanded)
%              Number of leaves         :   18 (1994 expanded)
%              Depth                    :   28
%              Number of atoms          :  300 (26636 expanded)
%              Number of equality atoms :  102 (8250 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(rc1_funct_2,axiom,(
    ! [X1,X2] :
    ? [X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_relat_1(X3)
      & v4_relat_1(X3,X1)
      & v5_relat_1(X3,X2)
      & v1_funct_1(X3)
      & v1_funct_2(X3,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(dt_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(t19_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X5] :
          ( ( v1_funct_2(X5,X2,X3)
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
         => ( ~ ( X2 = k1_xboole_0
                & X3 != k1_xboole_0
                & X1 != k1_xboole_0 )
           => v1_funct_2(k4_relset_1(X1,X2,X2,X3,X4,X5),X1,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_funct_2)).

fof(redefinition_k4_relset_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k4_relset_1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

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

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(dt_k4_relset_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => m1_subset_1(k4_relset_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

fof(t46_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
           => k1_relat_1(k5_relat_1(X1,X2)) = k1_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(dt_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(c_0_18,plain,(
    ! [X10,X11,X12] :
      ( ~ v1_xboole_0(X10)
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X11,X10)))
      | v1_xboole_0(X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

fof(c_0_19,plain,(
    ! [X30,X31] :
      ( m1_subset_1(esk2_2(X30,X31),k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      & v1_relat_1(esk2_2(X30,X31))
      & v4_relat_1(esk2_2(X30,X31),X30)
      & v5_relat_1(esk2_2(X30,X31),X31)
      & v1_funct_1(esk2_2(X30,X31))
      & v1_funct_2(esk2_2(X30,X31),X30,X31) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_funct_2])])).

fof(c_0_20,plain,(
    ! [X54] :
      ( ~ v1_xboole_0(X54)
      | X54 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_21,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_25,plain,
    ( v1_xboole_0(esk2_2(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,plain,
    ( esk2_2(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_25])).

cnf(c_0_28,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_24,c_0_26])).

fof(c_0_29,plain,(
    ! [X16,X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
      | m1_subset_1(k1_relset_1(X16,X17,X18),k1_zfmisc_1(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).

cnf(c_0_30,plain,
    ( esk2_2(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_31,plain,(
    ! [X33,X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | k1_relset_1(X33,X34,X35) = k1_relat_1(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_32,plain,
    ( m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_30])).

cnf(c_0_34,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_35,plain,(
    ! [X51,X52,X53] :
      ( ~ r2_hidden(X51,X52)
      | ~ m1_subset_1(X52,k1_zfmisc_1(X53))
      | ~ v1_xboole_0(X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_36,plain,
    ( m1_subset_1(k1_relset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,plain,
    ( k1_relset_1(X1,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_33])).

fof(c_0_38,plain,(
    ! [X45,X46] :
      ( ~ m1_subset_1(X45,X46)
      | v1_xboole_0(X46)
      | r2_hidden(X45,X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_39,plain,(
    ! [X28] : m1_subset_1(esk1_1(X28),X28) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_40,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X5] :
            ( ( v1_funct_2(X5,X2,X3)
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
           => ( ~ ( X2 = k1_xboole_0
                  & X3 != k1_xboole_0
                  & X1 != k1_xboole_0 )
             => v1_funct_2(k4_relset_1(X1,X2,X2,X3,X4,X5),X1,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t19_funct_2])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,plain,
    ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,plain,
    ( m1_subset_1(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_45,plain,(
    ! [X39,X40,X41,X42,X43,X44] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
      | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
      | k4_relset_1(X39,X40,X41,X42,X43,X44) = k5_relat_1(X43,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_relset_1])])).

fof(c_0_46,negated_conjecture,
    ( v1_funct_2(esk6_0,esk3_0,esk4_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    & v1_funct_2(esk7_0,esk4_0,esk5_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
    & ( esk4_0 != k1_xboole_0
      | esk5_0 = k1_xboole_0
      | esk3_0 = k1_xboole_0 )
    & ~ v1_funct_2(k4_relset_1(esk3_0,esk4_0,esk4_0,esk5_0,esk6_0,esk7_0),esk3_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_40])])])).

fof(c_0_47,plain,(
    ! [X13,X14,X15] :
      ( ( ~ v1_funct_2(X15,X13,X14)
        | X13 = k1_relset_1(X13,X14,X15)
        | X14 = k1_xboole_0
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( X13 != k1_relset_1(X13,X14,X15)
        | v1_funct_2(X15,X13,X14)
        | X14 = k1_xboole_0
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( ~ v1_funct_2(X15,X13,X14)
        | X13 = k1_relset_1(X13,X14,X15)
        | X13 != k1_xboole_0
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( X13 != k1_relset_1(X13,X14,X15)
        | v1_funct_2(X15,X13,X14)
        | X13 != k1_xboole_0
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( ~ v1_funct_2(X15,X13,X14)
        | X15 = k1_xboole_0
        | X13 = k1_xboole_0
        | X14 != k1_xboole_0
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( X15 != k1_xboole_0
        | v1_funct_2(X15,X13,X14)
        | X13 = k1_xboole_0
        | X14 != k1_xboole_0
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(X1,k1_relat_1(k1_xboole_0))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

fof(c_0_50,plain,(
    ! [X7,X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | v1_relat_1(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_51,plain,(
    ! [X36,X37,X38] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | k2_relset_1(X36,X37,X38) = k2_relat_1(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_52,plain,(
    ! [X22,X23,X24,X25,X26,X27] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | m1_subset_1(k4_relset_1(X22,X23,X24,X25,X26,X27),k1_zfmisc_1(k2_zfmisc_1(X22,X25))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relset_1])])).

cnf(c_0_53,plain,
    ( k4_relset_1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_55,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,plain,
    ( v1_funct_2(esk2_2(X1,X2),X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_57,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

fof(c_0_58,plain,(
    ! [X49,X50] :
      ( ~ v1_relat_1(X49)
      | ~ v1_relat_1(X50)
      | ~ r1_tarski(k2_relat_1(X49),k1_relat_1(X50))
      | k1_relat_1(k5_relat_1(X49,X50)) = k1_relat_1(X49) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_relat_1])])])).

cnf(c_0_59,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_60,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | m1_subset_1(k2_relset_1(X19,X20,X21),k1_zfmisc_1(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).

cnf(c_0_61,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_63,plain,
    ( m1_subset_1(k4_relset_1(X2,X3,X5,X6,X1,X4),k1_zfmisc_1(k2_zfmisc_1(X2,X6)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_64,negated_conjecture,
    ( k4_relset_1(X1,X2,esk4_0,esk5_0,X3,esk7_0) = k5_relat_1(X3,esk7_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_65,plain,
    ( m1_subset_1(k1_relset_1(X1,X2,esk2_2(X1,X2)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_22])).

cnf(c_0_66,plain,
    ( k1_relset_1(X1,X2,esk2_2(X1,X2)) = X1
    | X2 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_22])])).

cnf(c_0_67,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_57])).

cnf(c_0_68,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_69,negated_conjecture,
    ( k1_relat_1(esk7_0) = k1_relset_1(esk4_0,esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_54])).

cnf(c_0_70,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_54])).

cnf(c_0_71,negated_conjecture,
    ( v1_funct_2(esk7_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_72,plain,(
    ! [X47,X48] :
      ( ( ~ m1_subset_1(X47,k1_zfmisc_1(X48))
        | r1_tarski(X47,X48) )
      & ( ~ r1_tarski(X47,X48)
        | m1_subset_1(X47,k1_zfmisc_1(X48)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_73,plain,
    ( m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_74,negated_conjecture,
    ( k2_relset_1(esk3_0,esk4_0,esk6_0) = k2_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(k4_relset_1(X1,X2,esk4_0,esk5_0,X3,esk7_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk5_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_54])).

cnf(c_0_76,negated_conjecture,
    ( k4_relset_1(esk3_0,esk4_0,esk4_0,esk5_0,esk6_0,esk7_0) = k5_relat_1(esk6_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_62])).

cnf(c_0_77,plain,
    ( X1 = k1_xboole_0
    | m1_subset_1(X2,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_78,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_67,c_0_28])).

cnf(c_0_79,negated_conjecture,
    ( k1_relat_1(k5_relat_1(X1,esk7_0)) = k1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),k1_relset_1(esk4_0,esk5_0,esk7_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])])).

cnf(c_0_80,negated_conjecture,
    ( k1_relset_1(esk4_0,esk5_0,esk7_0) = esk4_0
    | esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_71]),c_0_54])])).

cnf(c_0_81,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(k2_relat_1(esk6_0),k1_zfmisc_1(esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_62]),c_0_74])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(k5_relat_1(esk6_0,esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk5_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_62]),c_0_76])).

cnf(c_0_84,plain,
    ( X1 = k1_xboole_0
    | v1_xboole_0(k2_zfmisc_1(X2,X3))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_21,c_0_77])).

cnf(c_0_85,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_42,c_0_78])).

cnf(c_0_86,negated_conjecture,
    ( k1_relat_1(k5_relat_1(X1,esk7_0)) = k1_relat_1(X1)
    | esk5_0 = k1_xboole_0
    | ~ r1_tarski(k2_relat_1(X1),esk4_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk6_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_88,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk6_0,esk7_0)) = k1_relset_1(esk3_0,esk5_0,k5_relat_1(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_83])).

cnf(c_0_89,negated_conjecture,
    ( k1_relat_1(esk6_0) = k1_relset_1(esk3_0,esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_62])).

cnf(c_0_90,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_62])).

cnf(c_0_91,negated_conjecture,
    ( ~ v1_funct_2(k4_relset_1(esk3_0,esk4_0,esk4_0,esk5_0,esk6_0,esk7_0),esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_92,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_84])).

cnf(c_0_93,plain,
    ( k4_relset_1(X1,X2,X3,X4,X5,k1_xboole_0) = k5_relat_1(X5,k1_xboole_0)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_85])).

cnf(c_0_94,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_95,negated_conjecture,
    ( k1_relset_1(esk3_0,esk5_0,k5_relat_1(esk6_0,esk7_0)) = k1_relset_1(esk3_0,esk4_0,esk6_0)
    | esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88]),c_0_89]),c_0_90])])).

cnf(c_0_96,negated_conjecture,
    ( ~ v1_funct_2(k5_relat_1(esk6_0,esk7_0),esk3_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_91,c_0_76])).

cnf(c_0_97,negated_conjecture,
    ( v1_funct_2(esk6_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_98,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0
    | X2 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_92,c_0_28])).

cnf(c_0_99,plain,
    ( m1_subset_1(k4_relset_1(X1,X2,X3,X4,X5,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_85])).

cnf(c_0_100,negated_conjecture,
    ( k4_relset_1(esk3_0,esk4_0,X1,X2,esk6_0,k1_xboole_0) = k5_relat_1(esk6_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_93,c_0_62])).

cnf(c_0_101,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | k1_relset_1(esk3_0,esk4_0,esk6_0) != esk3_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_83])]),c_0_96])).

cnf(c_0_102,negated_conjecture,
    ( k1_relset_1(esk3_0,esk4_0,esk6_0) = esk3_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_97]),c_0_62])])).

cnf(c_0_103,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_98])).

cnf(c_0_104,negated_conjecture,
    ( m1_subset_1(k5_relat_1(esk6_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_62]),c_0_100])).

cnf(c_0_105,negated_conjecture,
    ( v1_xboole_0(esk7_0)
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_54])).

cnf(c_0_106,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_107,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_103]),c_0_28])])).

cnf(c_0_108,negated_conjecture,
    ( m1_subset_1(k5_relat_1(esk6_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_103])).

cnf(c_0_109,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | v1_xboole_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_28])])).

cnf(c_0_110,negated_conjecture,
    ( v1_xboole_0(k5_relat_1(esk6_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_107,c_0_108])).

cnf(c_0_111,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_109])).

cnf(c_0_112,negated_conjecture,
    ( k5_relat_1(esk6_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_110])).

cnf(c_0_113,negated_conjecture,
    ( ~ r2_hidden(X1,esk6_0)
    | ~ v1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_62])).

cnf(c_0_114,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | ~ v1_funct_2(k1_xboole_0,esk3_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_111]),c_0_112])).

cnf(c_0_115,plain,
    ( v1_funct_2(k1_xboole_0,X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_30])).

cnf(c_0_116,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | ~ v1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_113,c_0_49])).

cnf(c_0_117,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_106]),c_0_115])])).

cnf(c_0_118,negated_conjecture,
    ( v1_xboole_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_116,c_0_117]),c_0_103]),c_0_28])])).

cnf(c_0_119,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_120,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | k1_relset_1(esk3_0,k1_xboole_0,esk6_0) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_101,c_0_117])).

cnf(c_0_121,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_118])).

cnf(c_0_122,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_85]),c_0_78])).

cnf(c_0_123,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_119,c_0_117])])).

cnf(c_0_124,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_120,c_0_121]),c_0_122]),c_0_123])).

cnf(c_0_125,negated_conjecture,
    ( v1_xboole_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_105,c_0_124]),c_0_28])])).

cnf(c_0_126,negated_conjecture,
    ( esk7_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_125])).

cnf(c_0_127,negated_conjecture,
    ( ~ v1_funct_2(k5_relat_1(k1_xboole_0,k1_xboole_0),esk3_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_121]),c_0_126]),c_0_124])).

cnf(c_0_128,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_112,c_0_121])).

cnf(c_0_129,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_127,c_0_128]),c_0_115])]),
    [proof]).

%------------------------------------------------------------------------------
