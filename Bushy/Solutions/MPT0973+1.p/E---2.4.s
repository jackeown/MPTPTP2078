%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_2__t19_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:41 EDT 2019

% Result     : Theorem 152.44s
% Output     : CNFRefutation 152.44s
% Verified   : 
% Statistics : Number of formulae       :  126 (1675 expanded)
%              Number of clauses        :   88 ( 736 expanded)
%              Number of leaves         :   19 ( 410 expanded)
%              Depth                    :   16
%              Number of atoms          :  314 (6908 expanded)
%              Number of equality atoms :  105 (2310 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/funct_2__t19_funct_2.p',t19_funct_2)).

fof(redefinition_k4_relset_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k4_relset_1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t19_funct_2.p',redefinition_k4_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/funct_2__t19_funct_2.p',d1_funct_2)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t19_funct_2.p',cc4_relset_1)).

fof(rc1_funct_2,axiom,(
    ! [X1,X2] :
    ? [X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_relat_1(X3)
      & v4_relat_1(X3,X1)
      & v5_relat_1(X3,X2)
      & v1_funct_1(X3)
      & v1_funct_2(X3,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t19_funct_2.p',rc1_funct_2)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t19_funct_2.p',t6_boole)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t19_funct_2.p',redefinition_k1_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t19_funct_2.p',cc1_relset_1)).

fof(dt_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t19_funct_2.p',dt_k2_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t19_funct_2.p',redefinition_k2_relset_1)).

fof(dt_k4_relset_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => m1_subset_1(k4_relset_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t19_funct_2.p',dt_k4_relset_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t19_funct_2.p',t8_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t19_funct_2.p',dt_o_0_0_xboole_0)).

fof(t46_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
           => k1_relat_1(k5_relat_1(X1,X2)) = k1_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t19_funct_2.p',t46_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t19_funct_2.p',t3_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t19_funct_2.p',t5_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t19_funct_2.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t19_funct_2.p',existence_m1_subset_1)).

fof(dt_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t19_funct_2.p',dt_k1_relset_1)).

fof(c_0_19,negated_conjecture,(
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

fof(c_0_20,plain,(
    ! [X39,X40,X41,X42,X43,X44] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
      | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
      | k4_relset_1(X39,X40,X41,X42,X43,X44) = k5_relat_1(X43,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_relset_1])])).

fof(c_0_21,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,esk2_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & v1_funct_2(esk5_0,esk2_0,esk3_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    & ( esk2_0 != k1_xboole_0
      | esk3_0 = k1_xboole_0
      | esk1_0 = k1_xboole_0 )
    & ~ v1_funct_2(k4_relset_1(esk1_0,esk2_0,esk2_0,esk3_0,esk4_0,esk5_0),esk1_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_22,plain,(
    ! [X14,X15,X16] :
      ( ( ~ v1_funct_2(X16,X14,X15)
        | X14 = k1_relset_1(X14,X15,X16)
        | X15 = k1_xboole_0
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) )
      & ( X14 != k1_relset_1(X14,X15,X16)
        | v1_funct_2(X16,X14,X15)
        | X15 = k1_xboole_0
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) )
      & ( ~ v1_funct_2(X16,X14,X15)
        | X14 = k1_relset_1(X14,X15,X16)
        | X14 != k1_xboole_0
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) )
      & ( X14 != k1_relset_1(X14,X15,X16)
        | v1_funct_2(X16,X14,X15)
        | X14 != k1_xboole_0
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) )
      & ( ~ v1_funct_2(X16,X14,X15)
        | X16 = k1_xboole_0
        | X14 = k1_xboole_0
        | X15 != k1_xboole_0
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) )
      & ( X16 != k1_xboole_0
        | v1_funct_2(X16,X14,X15)
        | X14 = k1_xboole_0
        | X15 != k1_xboole_0
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_23,plain,(
    ! [X67,X68,X69] :
      ( ~ v1_xboole_0(X67)
      | ~ m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(X68,X67)))
      | v1_xboole_0(X69) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

fof(c_0_24,plain,(
    ! [X70,X71] :
      ( m1_subset_1(esk7_2(X70,X71),k1_zfmisc_1(k2_zfmisc_1(X70,X71)))
      & v1_relat_1(esk7_2(X70,X71))
      & v4_relat_1(esk7_2(X70,X71),X70)
      & v5_relat_1(esk7_2(X70,X71),X71)
      & v1_funct_1(esk7_2(X70,X71))
      & v1_funct_2(esk7_2(X70,X71),X70,X71) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_funct_2])])).

fof(c_0_25,plain,(
    ! [X59] :
      ( ~ v1_xboole_0(X59)
      | X59 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

fof(c_0_26,plain,(
    ! [X33,X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | k1_relset_1(X33,X34,X35) = k1_relat_1(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_27,plain,(
    ! [X64,X65,X66] :
      ( ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65)))
      | v1_relat_1(X66) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_28,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | m1_subset_1(k2_relset_1(X20,X21,X22),k1_zfmisc_1(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).

fof(c_0_29,plain,(
    ! [X36,X37,X38] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | k2_relset_1(X36,X37,X38) = k2_relat_1(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_30,plain,(
    ! [X23,X24,X25,X26,X27,X28] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | m1_subset_1(k4_relset_1(X23,X24,X25,X26,X27,X28),k1_zfmisc_1(k2_zfmisc_1(X23,X26))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relset_1])])).

cnf(c_0_31,plain,
    ( k4_relset_1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_34,plain,(
    ! [X62,X63] :
      ( ~ v1_xboole_0(X62)
      | X62 = X63
      | ~ v1_xboole_0(X63) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_35,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( m1_subset_1(esk7_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

fof(c_0_39,plain,(
    ! [X51,X52] :
      ( ~ v1_relat_1(X51)
      | ~ v1_relat_1(X52)
      | ~ r1_tarski(k2_relat_1(X51),k1_relat_1(X52))
      | k1_relat_1(k5_relat_1(X51,X52)) = k1_relat_1(X51) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_relat_1])])])).

cnf(c_0_40,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_42,plain,
    ( m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_44,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_45,plain,
    ( m1_subset_1(k4_relset_1(X2,X3,X5,X6,X1,X4),k1_zfmisc_1(k2_zfmisc_1(X2,X6)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_46,negated_conjecture,
    ( k4_relset_1(X1,X2,esk2_0,esk3_0,X3,esk5_0) = k5_relat_1(X3,esk5_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_47,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | ~ v1_funct_2(X2,X1,k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_48,plain,
    ( v1_funct_2(esk7_2(X1,X2),X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_49,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_50,plain,
    ( v1_xboole_0(esk7_2(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_51,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_52,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_53,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_relset_1(esk2_0,esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_32])).

cnf(c_0_54,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_32])).

cnf(c_0_55,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_56,negated_conjecture,
    ( v1_funct_2(esk5_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_57,plain,(
    ! [X49,X50] :
      ( ( ~ m1_subset_1(X49,k1_zfmisc_1(X50))
        | r1_tarski(X49,X50) )
      & ( ~ r1_tarski(X49,X50)
        | m1_subset_1(X49,k1_zfmisc_1(X50)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(k2_relset_1(esk1_0,esk2_0,esk4_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_59,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk4_0) = k2_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_43])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(k4_relset_1(X1,X2,esk2_0,esk3_0,X3,esk5_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_32])).

cnf(c_0_61,negated_conjecture,
    ( k4_relset_1(esk1_0,esk2_0,esk2_0,esk3_0,esk4_0,esk5_0) = k5_relat_1(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_43])).

cnf(c_0_62,plain,
    ( esk7_2(X1,k1_xboole_0) = k1_xboole_0
    | X1 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_36])])).

cnf(c_0_63,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_xboole_0(esk7_2(X2,X3))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_64,plain,
    ( esk7_2(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_50])).

cnf(c_0_65,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_38,c_0_51])).

cnf(c_0_66,negated_conjecture,
    ( k1_relat_1(k5_relat_1(X1,esk5_0)) = k1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),k1_relset_1(esk2_0,esk3_0,esk5_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])])).

cnf(c_0_67,negated_conjecture,
    ( k1_relset_1(esk2_0,esk3_0,esk5_0) = esk2_0
    | esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_32]),c_0_56])])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(k2_relat_1(esk4_0),k1_zfmisc_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(k5_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_43]),c_0_61])).

cnf(c_0_71,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_72,plain,(
    ! [X56,X57,X58] :
      ( ~ r2_hidden(X56,X57)
      | ~ m1_subset_1(X57,k1_zfmisc_1(X58))
      | ~ v1_xboole_0(X58) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_73,plain,
    ( X1 = k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_62])).

fof(c_0_74,plain,(
    ! [X47,X48] :
      ( ~ m1_subset_1(X47,X48)
      | v1_xboole_0(X48)
      | r2_hidden(X47,X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_75,plain,(
    ! [X31] : m1_subset_1(esk6_1(X31),X31) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_76,negated_conjecture,
    ( ~ v1_funct_2(k4_relset_1(esk1_0,esk2_0,esk2_0,esk3_0,esk4_0,esk5_0),esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_77,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])])).

cnf(c_0_78,negated_conjecture,
    ( k1_relat_1(k5_relat_1(X1,esk5_0)) = k1_relat_1(X1)
    | esk3_0 = k1_xboole_0
    | ~ r1_tarski(k2_relat_1(X1),esk2_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_80,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk4_0,esk5_0)) = k1_relset_1(esk1_0,esk3_0,k5_relat_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_70])).

cnf(c_0_81,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_relset_1(esk1_0,esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_43])).

cnf(c_0_82,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_43])).

cnf(c_0_83,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_2(X2,k1_xboole_0,X1) ),
    inference(er,[status(thm)],[c_0_71])).

cnf(c_0_84,plain,
    ( v1_funct_2(k1_xboole_0,X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_64])).

cnf(c_0_85,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_64])).

cnf(c_0_86,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_87,plain,
    ( X1 = k1_xboole_0
    | m1_subset_1(k2_relset_1(X1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_73])).

cnf(c_0_88,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_89,plain,
    ( m1_subset_1(esk6_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_90,negated_conjecture,
    ( ~ v1_xboole_0(k4_relset_1(esk1_0,esk2_0,esk2_0,esk3_0,esk4_0,esk5_0))
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_91,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_92,negated_conjecture,
    ( k1_relset_1(esk1_0,esk3_0,k5_relat_1(esk4_0,esk5_0)) = k1_relset_1(esk1_0,esk2_0,esk4_0)
    | esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80]),c_0_81]),c_0_82])])).

cnf(c_0_93,negated_conjecture,
    ( ~ v1_funct_2(k5_relat_1(esk4_0,esk5_0),esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_76,c_0_61])).

cnf(c_0_94,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_95,plain,(
    ! [X17,X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
      | m1_subset_1(k1_relset_1(X17,X18,X19),k1_zfmisc_1(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).

cnf(c_0_96,plain,
    ( k1_relset_1(k1_xboole_0,X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85])).

cnf(c_0_97,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_85])).

cnf(c_0_98,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(X2,k2_relset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_65])])).

cnf(c_0_99,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk6_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_100,negated_conjecture,
    ( ~ v1_xboole_0(k5_relat_1(esk4_0,esk5_0))
    | ~ v1_xboole_0(esk3_0) ),
    inference(rw,[status(thm)],[c_0_90,c_0_61])).

cnf(c_0_101,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | k1_relset_1(esk1_0,esk2_0,esk4_0) != esk1_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_70])]),c_0_93])).

cnf(c_0_102,negated_conjecture,
    ( k1_relset_1(esk1_0,esk2_0,esk4_0) = esk1_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_43]),c_0_94])])).

cnf(c_0_103,plain,
    ( m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_104,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_105,plain,
    ( X1 = k1_xboole_0
    | v1_xboole_0(k2_relset_1(X1,k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_106,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_70]),c_0_100])).

cnf(c_0_107,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_108,plain,
    ( m1_subset_1(k1_relset_1(X1,X2,esk7_2(X1,X2)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_103,c_0_36])).

cnf(c_0_109,plain,
    ( k1_relset_1(X1,X2,esk7_2(X1,X2)) = k1_relat_1(esk7_2(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_36])).

cnf(c_0_110,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | X1 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_111,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_112,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_65])])).

cnf(c_0_113,plain,
    ( m1_subset_1(k1_relat_1(esk7_2(X1,X2)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_114,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_110])).

cnf(c_0_115,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_111,c_0_112])])).

cnf(c_0_116,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_43])).

cnf(c_0_117,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_64]),c_0_114])).

cnf(c_0_118,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_115]),c_0_65])])).

cnf(c_0_119,negated_conjecture,
    ( v1_xboole_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_116,c_0_112]),c_0_65])])).

cnf(c_0_120,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_117,c_0_65])).

cnf(c_0_121,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | k1_relset_1(k1_xboole_0,k1_xboole_0,esk4_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_112]),c_0_118]),c_0_118])).

cnf(c_0_122,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_119])).

cnf(c_0_123,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_120]),c_0_114])).

cnf(c_0_124,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_121,c_0_122]),c_0_123])])).

cnf(c_0_125,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106,c_0_124]),c_0_65])]),
    [proof]).
%------------------------------------------------------------------------------
