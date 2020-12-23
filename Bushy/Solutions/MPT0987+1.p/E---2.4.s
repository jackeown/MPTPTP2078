%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_2__t33_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:43 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 212 expanded)
%              Number of clauses        :   37 (  79 expanded)
%              Number of leaves         :   10 (  51 expanded)
%              Depth                    :    8
%              Number of atoms          :  171 (1320 expanded)
%              Number of equality atoms :   21 (  38 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   11 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t33_funct_2,conjecture,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ~ v1_xboole_0(X3)
         => ! [X4] :
              ( ( v1_funct_1(X4)
                & v1_funct_2(X4,X1,X2)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
             => ! [X5] :
                  ( ( v1_funct_1(X5)
                    & v1_funct_2(X5,X2,X3)
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
                 => ( ( v2_funct_2(X4,X2)
                      & v2_funct_2(X5,X3) )
                   => v2_funct_2(k1_partfun1(X1,X2,X2,X3,X4,X5),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t33_funct_2.p',t33_funct_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t33_funct_2.p',cc1_relset_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t33_funct_2.p',cc2_relset_1)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t33_funct_2.p',redefinition_k1_partfun1)).

fof(d3_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1) )
     => ( v2_funct_2(X2,X1)
      <=> k2_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t33_funct_2.p',d3_funct_2)).

fof(dt_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t33_funct_2.p',dt_k1_relset_1)).

fof(dt_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
        & m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t33_funct_2.p',dt_k1_partfun1)).

fof(t47_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k1_relat_1(X1),k2_relat_1(X2))
           => k2_relat_1(k5_relat_1(X2,X1)) = k2_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t33_funct_2.p',t47_relat_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t33_funct_2.p',redefinition_k1_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t33_funct_2.p',t3_subset)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ! [X3] :
            ( ~ v1_xboole_0(X3)
           => ! [X4] :
                ( ( v1_funct_1(X4)
                  & v1_funct_2(X4,X1,X2)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
               => ! [X5] :
                    ( ( v1_funct_1(X5)
                      & v1_funct_2(X5,X2,X3)
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
                   => ( ( v2_funct_2(X4,X2)
                        & v2_funct_2(X5,X3) )
                     => v2_funct_2(k1_partfun1(X1,X2,X2,X3,X4,X5),X3) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t33_funct_2])).

fof(c_0_11,plain,(
    ! [X66,X67,X68] :
      ( ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67)))
      | v1_relat_1(X68) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_12,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    & ~ v1_xboole_0(esk3_0)
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk1_0,esk2_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk2_0,esk3_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    & v2_funct_2(esk4_0,esk2_0)
    & v2_funct_2(esk5_0,esk3_0)
    & ~ v2_funct_2(k1_partfun1(esk1_0,esk2_0,esk2_0,esk3_0,esk4_0,esk5_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_13,plain,(
    ! [X69,X70,X71] :
      ( ( v4_relat_1(X71,X69)
        | ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X69,X70))) )
      & ( v5_relat_1(X71,X70)
        | ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X69,X70))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_14,plain,(
    ! [X35,X36,X37,X38,X39,X40] :
      ( ~ v1_funct_1(X39)
      | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | ~ v1_funct_1(X40)
      | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
      | k1_partfun1(X35,X36,X37,X38,X39,X40) = k5_relat_1(X39,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

fof(c_0_15,plain,(
    ! [X17,X18] :
      ( ( ~ v2_funct_2(X18,X17)
        | k2_relat_1(X18) = X17
        | ~ v1_relat_1(X18)
        | ~ v5_relat_1(X18,X17) )
      & ( k2_relat_1(X18) != X17
        | v2_funct_2(X18,X17)
        | ~ v1_relat_1(X18)
        | ~ v5_relat_1(X18,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).

cnf(c_0_16,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X25,X26,X27] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | m1_subset_1(k1_relset_1(X25,X26,X27),k1_zfmisc_1(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).

fof(c_0_20,plain,(
    ! [X19,X20,X21,X22,X23,X24] :
      ( ( v1_funct_1(k1_partfun1(X19,X20,X21,X22,X23,X24))
        | ~ v1_funct_1(X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | ~ v1_funct_1(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) )
      & ( m1_subset_1(k1_partfun1(X19,X20,X21,X22,X23,X24),k1_zfmisc_1(k2_zfmisc_1(X19,X22)))
        | ~ v1_funct_1(X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | ~ v1_funct_1(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

cnf(c_0_21,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_24,plain,(
    ! [X53,X54] :
      ( ~ v1_relat_1(X53)
      | ~ v1_relat_1(X54)
      | ~ r1_tarski(k1_relat_1(X53),k2_relat_1(X54))
      | k2_relat_1(k5_relat_1(X54,X53)) = k2_relat_1(X53) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_relat_1])])])).

cnf(c_0_25,plain,
    ( k2_relat_1(X1) = X2
    | ~ v2_funct_2(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( v2_funct_2(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( v5_relat_1(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_17])).

fof(c_0_29,plain,(
    ! [X41,X42,X43] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
      | k1_relset_1(X41,X42,X43) = k1_relat_1(X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_30,plain,(
    ! [X51,X52] :
      ( ( ~ m1_subset_1(X51,k1_zfmisc_1(X52))
        | r1_tarski(X51,X52) )
      & ( ~ r1_tarski(X51,X52)
        | m1_subset_1(X51,k1_zfmisc_1(X52)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_31,plain,
    ( m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,negated_conjecture,
    ( k1_partfun1(X1,X2,esk2_0,esk3_0,X3,esk5_0) = k5_relat_1(X3,esk5_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_35,plain,
    ( k2_relat_1(k5_relat_1(X2,X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k1_relat_1(X1),k2_relat_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,negated_conjecture,
    ( k2_relat_1(esk4_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])]),c_0_28])])).

cnf(c_0_37,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( v2_funct_2(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_39,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_22])).

cnf(c_0_40,negated_conjecture,
    ( v5_relat_1(esk5_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_22])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(k1_relset_1(esk2_0,esk3_0,esk5_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_22])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(k1_partfun1(X1,X2,esk2_0,esk3_0,X3,esk5_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_22]),c_0_23])])).

cnf(c_0_44,negated_conjecture,
    ( k1_partfun1(esk1_0,esk2_0,esk2_0,esk3_0,esk4_0,esk5_0) = k5_relat_1(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_17]),c_0_34])])).

cnf(c_0_45,plain,
    ( v2_funct_2(X1,X2)
    | k2_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_46,negated_conjecture,
    ( k2_relat_1(k5_relat_1(esk4_0,X1)) = k2_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),esk2_0)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_27])])).

cnf(c_0_47,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_relset_1(esk2_0,esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_22])).

cnf(c_0_48,negated_conjecture,
    ( k2_relat_1(esk5_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_38]),c_0_39])]),c_0_40])])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k1_relset_1(esk2_0,esk3_0,esk5_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(k5_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_17]),c_0_44]),c_0_34])])).

cnf(c_0_51,negated_conjecture,
    ( ~ v2_funct_2(k1_partfun1(esk1_0,esk2_0,esk2_0,esk3_0,esk4_0,esk5_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_52,plain,
    ( v2_funct_2(X1,k2_relat_1(X1))
    | ~ v5_relat_1(X1,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( k2_relat_1(k5_relat_1(esk4_0,esk5_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_49]),c_0_39])])).

cnf(c_0_54,negated_conjecture,
    ( v5_relat_1(k5_relat_1(esk4_0,esk5_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( v1_relat_1(k5_relat_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( ~ v2_funct_2(k5_relat_1(esk4_0,esk5_0),esk3_0) ),
    inference(rw,[status(thm)],[c_0_51,c_0_44])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_55])]),c_0_56]),
    [proof]).
%------------------------------------------------------------------------------
