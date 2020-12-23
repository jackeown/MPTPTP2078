%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_2__t170_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:36 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 638 expanded)
%              Number of clauses        :   47 ( 253 expanded)
%              Number of leaves         :   10 ( 168 expanded)
%              Depth                    :   12
%              Number of atoms          :  245 (2348 expanded)
%              Number of equality atoms :   45 ( 526 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   36 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_hidden(X3,X1)
       => ( X2 = k1_xboole_0
          | r2_hidden(k1_funct_1(X4,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t170_funct_2.p',t7_funct_2)).

fof(redefinition_k9_setfam_1,axiom,(
    ! [X1] : k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t170_funct_2.p',redefinition_k9_setfam_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t170_funct_2.p',t6_boole)).

fof(t170_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,k9_setfam_1(X1))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k9_setfam_1(X1)))) )
     => ? [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
          & ! [X4] :
              ( r2_hidden(X4,X1)
             => k11_relat_1(X3,X4) = k1_funct_1(X2,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t170_funct_2.p',t170_funct_2)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t170_funct_2.p',dt_o_0_0_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t170_funct_2.p',t3_subset)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t170_funct_2.p',t1_subset)).

fof(s3_relset_1__e2_192__funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,k9_setfam_1(X1))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k9_setfam_1(X1)))) )
     => ( ! [X3] :
            ( m1_subset_1(X3,X1)
           => ( r2_hidden(X3,k2_subset_1(X1))
             => r1_tarski(k1_funct_1(X2,X3),k2_subset_1(X1)) ) )
       => ? [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X1),k2_subset_1(X1))))
            & ! [X4] :
                ( m1_subset_1(X4,X1)
               => ( r2_hidden(X4,k2_subset_1(X1))
                 => k11_relat_1(X3,X4) = k1_funct_1(X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t170_funct_2.p',s3_relset_1__e2_192__funct_2)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/funct_2__t170_funct_2.p',d4_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t170_funct_2.p',fc1_subset_1)).

fof(c_0_10,plain,(
    ! [X37,X38,X39,X40] :
      ( ~ v1_funct_1(X40)
      | ~ v1_funct_2(X40,X37,X38)
      | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
      | ~ r2_hidden(X39,X37)
      | X38 = k1_xboole_0
      | r2_hidden(k1_funct_1(X40,X39),X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).

fof(c_0_11,plain,(
    ! [X16] : k9_setfam_1(X16) = k1_zfmisc_1(X16) ),
    inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).

fof(c_0_12,plain,(
    ! [X34] :
      ( ~ v1_xboole_0(X34)
      | X34 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,k9_setfam_1(X1))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k9_setfam_1(X1)))) )
       => ? [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
            & ! [X4] :
                ( r2_hidden(X4,X1)
               => k11_relat_1(X3,X4) = k1_funct_1(X2,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t170_funct_2])).

cnf(c_0_14,plain,
    ( X3 = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X4),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

fof(c_0_18,negated_conjecture,(
    ! [X7] :
      ( v1_funct_1(esk2_0)
      & v1_funct_2(esk2_0,esk1_0,k9_setfam_1(esk1_0))
      & m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k9_setfam_1(esk1_0))))
      & ( r2_hidden(esk3_1(X7),esk1_0)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) )
      & ( k11_relat_1(X7,esk3_1(X7)) != k1_funct_1(esk2_0,esk3_1(X7))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])])).

cnf(c_0_19,plain,
    ( X3 = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X4),X3)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X4,X2)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k9_setfam_1(k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k9_setfam_1(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X26,X27] :
      ( ( ~ m1_subset_1(X26,k1_zfmisc_1(X27))
        | r1_tarski(X26,X27) )
      & ( ~ r1_tarski(X26,X27)
        | m1_subset_1(X26,k1_zfmisc_1(X27)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_23,plain,(
    ! [X22,X23] :
      ( ~ r2_hidden(X22,X23)
      | m1_subset_1(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_24,plain,
    ( X1 = o_0_0_xboole_0
    | r2_hidden(k1_funct_1(X2,X3),X1)
    | ~ r2_hidden(X3,X4)
    | ~ m1_subset_1(X2,k9_setfam_1(k2_zfmisc_1(X4,X1)))
    | ~ v1_funct_2(X2,X4,X1)
    | ~ v1_funct_1(X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk2_0,k9_setfam_1(k2_zfmisc_1(esk1_0,k9_setfam_1(esk1_0)))) ),
    inference(rw,[status(thm)],[c_0_21,c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_2(esk2_0,esk1_0,k9_setfam_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_28,plain,(
    ! [X17,X18,X21] :
      ( ( m1_subset_1(esk6_2(X17,X18),k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X17),k2_subset_1(X17))))
        | m1_subset_1(esk5_2(X17,X18),X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X17,k9_setfam_1(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X17,k9_setfam_1(X17)))) )
      & ( ~ m1_subset_1(X21,X17)
        | ~ r2_hidden(X21,k2_subset_1(X17))
        | k11_relat_1(esk6_2(X17,X18),X21) = k1_funct_1(X18,X21)
        | m1_subset_1(esk5_2(X17,X18),X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X17,k9_setfam_1(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X17,k9_setfam_1(X17)))) )
      & ( m1_subset_1(esk6_2(X17,X18),k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X17),k2_subset_1(X17))))
        | r2_hidden(esk5_2(X17,X18),k2_subset_1(X17))
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X17,k9_setfam_1(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X17,k9_setfam_1(X17)))) )
      & ( ~ m1_subset_1(X21,X17)
        | ~ r2_hidden(X21,k2_subset_1(X17))
        | k11_relat_1(esk6_2(X17,X18),X21) = k1_funct_1(X18,X21)
        | r2_hidden(esk5_2(X17,X18),k2_subset_1(X17))
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X17,k9_setfam_1(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X17,k9_setfam_1(X17)))) )
      & ( m1_subset_1(esk6_2(X17,X18),k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X17),k2_subset_1(X17))))
        | ~ r1_tarski(k1_funct_1(X18,esk5_2(X17,X18)),k2_subset_1(X17))
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X17,k9_setfam_1(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X17,k9_setfam_1(X17)))) )
      & ( ~ m1_subset_1(X21,X17)
        | ~ r2_hidden(X21,k2_subset_1(X17))
        | k11_relat_1(esk6_2(X17,X18),X21) = k1_funct_1(X18,X21)
        | ~ r1_tarski(k1_funct_1(X18,esk5_2(X17,X18)),k2_subset_1(X17))
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X17,k9_setfam_1(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X17,k9_setfam_1(X17)))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_relset_1__e2_192__funct_2])])])])])).

fof(c_0_29,plain,(
    ! [X11] : k2_subset_1(X11) = X11 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( k9_setfam_1(esk1_0) = o_0_0_xboole_0
    | r2_hidden(k1_funct_1(esk2_0,X1),k9_setfam_1(esk1_0))
    | ~ r2_hidden(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27])])).

cnf(c_0_33,plain,
    ( k11_relat_1(esk6_2(X2,X3),X1) = k1_funct_1(X3,X1)
    | r2_hidden(esk5_2(X2,X3),k2_subset_1(X2))
    | ~ m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,k2_subset_1(X2))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X2,k9_setfam_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,k9_setfam_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk3_1(X1),esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_36,plain,
    ( m1_subset_1(esk6_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X1),k2_subset_1(X1))))
    | r2_hidden(esk5_2(X1,X2),k2_subset_1(X1))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,k9_setfam_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k9_setfam_1(X1)))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( m1_subset_1(esk6_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_subset_1(X1),k2_subset_1(X1))))
    | ~ r1_tarski(k1_funct_1(X2,esk5_2(X1,X2)),k2_subset_1(X1))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,k9_setfam_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k9_setfam_1(X1)))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k9_setfam_1(X2)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_15])).

cnf(c_0_39,negated_conjecture,
    ( k9_setfam_1(esk1_0) = o_0_0_xboole_0
    | m1_subset_1(k1_funct_1(esk2_0,X1),k9_setfam_1(esk1_0))
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( k11_relat_1(X1,esk3_1(X1)) != k1_funct_1(esk2_0,esk3_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_41,plain,
    ( k11_relat_1(esk6_2(X2,X3),X1) = k1_funct_1(X3,X1)
    | r2_hidden(esk5_2(X2,X3),X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2)
    | ~ v1_funct_2(X3,X2,k9_setfam_1(X2))
    | ~ m1_subset_1(X3,k9_setfam_1(k2_zfmisc_1(X2,k9_setfam_1(X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_34]),c_0_15])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk3_1(X1),esk1_0)
    | ~ m1_subset_1(X1,k9_setfam_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(rw,[status(thm)],[c_0_35,c_0_15])).

cnf(c_0_43,plain,
    ( r2_hidden(esk5_2(X1,X2),X1)
    | m1_subset_1(esk6_2(X1,X2),k9_setfam_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,k9_setfam_1(X1))
    | ~ m1_subset_1(X2,k9_setfam_1(k2_zfmisc_1(X1,k9_setfam_1(X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_34]),c_0_34]),c_0_34]),c_0_15]),c_0_15])).

cnf(c_0_44,plain,
    ( m1_subset_1(esk6_2(X1,X2),k9_setfam_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,k9_setfam_1(X1))
    | ~ r1_tarski(k1_funct_1(X2,esk5_2(X1,X2)),X1)
    | ~ m1_subset_1(X2,k9_setfam_1(k2_zfmisc_1(X1,k9_setfam_1(X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_34]),c_0_34]),c_0_34]),c_0_15]),c_0_15])).

cnf(c_0_45,negated_conjecture,
    ( k9_setfam_1(esk1_0) = o_0_0_xboole_0
    | r1_tarski(k1_funct_1(esk2_0,X1),esk1_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( k11_relat_1(X1,esk3_1(X1)) != k1_funct_1(esk2_0,esk3_1(X1))
    | ~ m1_subset_1(X1,k9_setfam_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(rw,[status(thm)],[c_0_40,c_0_15])).

cnf(c_0_47,plain,
    ( k11_relat_1(esk6_2(X1,X2),X3) = k1_funct_1(X2,X3)
    | r2_hidden(esk5_2(X1,X2),X1)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X2,k9_setfam_1(k2_zfmisc_1(X1,k9_setfam_1(X1))))
    | ~ v1_funct_2(X2,X1,k9_setfam_1(X1))
    | ~ v1_funct_1(X2) ),
    inference(csr,[status(thm)],[c_0_41,c_0_31])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk3_1(esk6_2(esk1_0,X1)),esk1_0)
    | r2_hidden(esk5_2(esk1_0,X1),esk1_0)
    | ~ m1_subset_1(X1,k9_setfam_1(k2_zfmisc_1(esk1_0,k9_setfam_1(esk1_0))))
    | ~ v1_funct_2(X1,esk1_0,k9_setfam_1(esk1_0))
    | ~ v1_funct_1(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,plain,
    ( k11_relat_1(esk6_2(X2,X3),X1) = k1_funct_1(X3,X1)
    | ~ m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,k2_subset_1(X2))
    | ~ r1_tarski(k1_funct_1(X3,esk5_2(X2,X3)),k2_subset_1(X2))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X2,k9_setfam_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,k9_setfam_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_50,negated_conjecture,
    ( k9_setfam_1(esk1_0) = o_0_0_xboole_0
    | m1_subset_1(esk6_2(esk1_0,esk2_0),k9_setfam_1(k2_zfmisc_1(esk1_0,esk1_0)))
    | ~ r2_hidden(esk5_2(esk1_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_25]),c_0_26]),c_0_27])])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk5_2(esk1_0,X1),esk1_0)
    | k11_relat_1(esk6_2(esk1_0,X1),esk3_1(esk6_2(esk1_0,X1))) != k1_funct_1(esk2_0,esk3_1(esk6_2(esk1_0,X1)))
    | ~ m1_subset_1(X1,k9_setfam_1(k2_zfmisc_1(esk1_0,k9_setfam_1(esk1_0))))
    | ~ v1_funct_2(X1,esk1_0,k9_setfam_1(esk1_0))
    | ~ v1_funct_1(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( k11_relat_1(esk6_2(esk1_0,esk2_0),X1) = k1_funct_1(esk2_0,X1)
    | r2_hidden(esk5_2(esk1_0,esk2_0),esk1_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_25]),c_0_26]),c_0_27])])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk3_1(esk6_2(esk1_0,esk2_0)),esk1_0)
    | r2_hidden(esk5_2(esk1_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_25]),c_0_26]),c_0_27])])).

cnf(c_0_54,plain,
    ( k11_relat_1(esk6_2(X2,X3),X1) = k1_funct_1(X3,X1)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2)
    | ~ v1_funct_2(X3,X2,k9_setfam_1(X2))
    | ~ r1_tarski(k1_funct_1(X3,esk5_2(X2,X3)),X2)
    | ~ m1_subset_1(X3,k9_setfam_1(k2_zfmisc_1(X2,k9_setfam_1(X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_34]),c_0_34]),c_0_15])).

fof(c_0_55,plain,(
    ! [X46] : ~ v1_xboole_0(k1_zfmisc_1(X46)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_56,negated_conjecture,
    ( k9_setfam_1(esk1_0) = o_0_0_xboole_0
    | k11_relat_1(esk6_2(esk1_0,esk2_0),esk3_1(esk6_2(esk1_0,esk2_0))) != k1_funct_1(esk2_0,esk3_1(esk6_2(esk1_0,esk2_0)))
    | ~ r2_hidden(esk5_2(esk1_0,esk2_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk5_2(esk1_0,esk2_0),esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_25]),c_0_26]),c_0_27])]),c_0_53])).

cnf(c_0_58,plain,
    ( k11_relat_1(esk6_2(X1,X2),X3) = k1_funct_1(X2,X3)
    | ~ r1_tarski(k1_funct_1(X2,esk5_2(X1,X2)),X1)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X2,k9_setfam_1(k2_zfmisc_1(X1,k9_setfam_1(X1))))
    | ~ v1_funct_2(X2,X1,k9_setfam_1(X1))
    | ~ v1_funct_1(X2) ),
    inference(csr,[status(thm)],[c_0_54,c_0_31])).

cnf(c_0_59,negated_conjecture,
    ( k9_setfam_1(esk1_0) = o_0_0_xboole_0
    | r2_hidden(esk3_1(esk6_2(esk1_0,esk2_0)),esk1_0)
    | ~ r2_hidden(esk5_2(esk1_0,esk2_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_50])).

cnf(c_0_60,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( k9_setfam_1(esk1_0) = o_0_0_xboole_0
    | k11_relat_1(esk6_2(esk1_0,esk2_0),esk3_1(esk6_2(esk1_0,esk2_0))) != k1_funct_1(esk2_0,esk3_1(esk6_2(esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57])])).

cnf(c_0_62,negated_conjecture,
    ( k11_relat_1(esk6_2(esk1_0,esk2_0),X1) = k1_funct_1(esk2_0,X1)
    | k9_setfam_1(esk1_0) = o_0_0_xboole_0
    | ~ r2_hidden(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_45]),c_0_25]),c_0_26]),c_0_27])]),c_0_57])])).

cnf(c_0_63,negated_conjecture,
    ( k9_setfam_1(esk1_0) = o_0_0_xboole_0
    | r2_hidden(esk3_1(esk6_2(esk1_0,esk2_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_57])])).

cnf(c_0_64,plain,
    ( ~ v1_xboole_0(k9_setfam_1(X1)) ),
    inference(rw,[status(thm)],[c_0_60,c_0_15])).

cnf(c_0_65,negated_conjecture,
    ( k9_setfam_1(esk1_0) = o_0_0_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_17])]),
    [proof]).
%------------------------------------------------------------------------------
