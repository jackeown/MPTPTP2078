%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:08:12 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 221 expanded)
%              Number of clauses        :   41 (  94 expanded)
%              Number of leaves         :   11 (  53 expanded)
%              Depth                    :   18
%              Number of atoms          :  208 ( 958 expanded)
%              Number of equality atoms :   21 (  40 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   30 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t191_funct_2,conjecture,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ~ v1_xboole_0(X3)
         => ! [X4] :
              ( ( v1_funct_1(X4)
                & v1_funct_2(X4,X2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
             => ( ! [X5] :
                    ( m1_subset_1(X5,X2)
                   => r2_hidden(k3_funct_2(X2,X3,X4,X5),X1) )
               => r1_tarski(k2_relset_1(X2,X3,X4),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t5_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( k1_relat_1(X3) = X1
          & ! [X4] :
              ( r2_hidden(X4,X1)
             => r2_hidden(k1_funct_1(X3,X4),X2) ) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ! [X3] :
            ( ~ v1_xboole_0(X3)
           => ! [X4] :
                ( ( v1_funct_1(X4)
                  & v1_funct_2(X4,X2,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
               => ( ! [X5] :
                      ( m1_subset_1(X5,X2)
                     => r2_hidden(k3_funct_2(X2,X3,X4,X5),X1) )
                 => r1_tarski(k2_relset_1(X2,X3,X4),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t191_funct_2])).

fof(c_0_12,plain,(
    ! [X19,X20,X21] :
      ( ( v4_relat_1(X21,X19)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( v5_relat_1(X21,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_13,negated_conjecture,(
    ! [X37] :
      ( ~ v1_xboole_0(esk3_0)
      & ~ v1_xboole_0(esk4_0)
      & v1_funct_1(esk5_0)
      & v1_funct_2(esk5_0,esk3_0,esk4_0)
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
      & ( ~ m1_subset_1(X37,esk3_0)
        | r2_hidden(k3_funct_2(esk3_0,esk4_0,esk5_0,X37),esk2_0) )
      & ~ r1_tarski(k2_relset_1(esk3_0,esk4_0,esk5_0),esk2_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])).

fof(c_0_14,plain,(
    ! [X13,X14] :
      ( ( ~ v4_relat_1(X14,X13)
        | r1_tarski(k1_relat_1(X14),X13)
        | ~ v1_relat_1(X14) )
      & ( ~ r1_tarski(k1_relat_1(X14),X13)
        | v4_relat_1(X14,X13)
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_15,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( v4_relat_1(esk5_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_19,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | v1_relat_1(X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk5_0),esk3_0)
    | ~ v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_22,plain,(
    ! [X17,X18] : v1_relat_1(k2_zfmisc_1(X17,X18)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_23,plain,(
    ! [X6,X7] :
      ( ( ~ m1_subset_1(X6,k1_zfmisc_1(X7))
        | r1_tarski(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | m1_subset_1(X6,k1_zfmisc_1(X7)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk5_0),esk3_0)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_26,plain,(
    ! [X8,X9,X10] :
      ( ~ r2_hidden(X8,X9)
      | ~ m1_subset_1(X9,k1_zfmisc_1(X10))
      | m1_subset_1(X8,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk5_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_16]),c_0_25])])).

fof(c_0_29,plain,(
    ! [X29,X30,X31] :
      ( ( v1_funct_1(X31)
        | r2_hidden(esk1_3(X29,X30,X31),X29)
        | k1_relat_1(X31) != X29
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) )
      & ( v1_funct_2(X31,X29,X30)
        | r2_hidden(esk1_3(X29,X30,X31),X29)
        | k1_relat_1(X31) != X29
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) )
      & ( m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
        | r2_hidden(esk1_3(X29,X30,X31),X29)
        | k1_relat_1(X31) != X29
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) )
      & ( v1_funct_1(X31)
        | ~ r2_hidden(k1_funct_1(X31,esk1_3(X29,X30,X31)),X30)
        | k1_relat_1(X31) != X29
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) )
      & ( v1_funct_2(X31,X29,X30)
        | ~ r2_hidden(k1_funct_1(X31,esk1_3(X29,X30,X31)),X30)
        | k1_relat_1(X31) != X29
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) )
      & ( m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
        | ~ r2_hidden(k1_funct_1(X31,esk1_3(X29,X30,X31)),X30)
        | k1_relat_1(X31) != X29
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_funct_2])])])])).

fof(c_0_30,plain,(
    ! [X25,X26,X27,X28] :
      ( v1_xboole_0(X25)
      | ~ v1_funct_1(X27)
      | ~ v1_funct_2(X27,X25,X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | ~ m1_subset_1(X28,X25)
      | k3_funct_2(X25,X26,X27,X28) = k1_funct_1(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(k1_relat_1(esk5_0),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | r2_hidden(esk1_3(X2,X3,X1),X2)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_25])).

cnf(c_0_35,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_2(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_38,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(X1,esk3_0)
    | ~ r2_hidden(X1,k1_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,plain,
    ( r2_hidden(esk1_3(k1_relat_1(X1),X2,X1),k1_relat_1(X1))
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_16])).

fof(c_0_42,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | k2_relset_1(X22,X23,X24) = k2_relat_1(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_43,negated_conjecture,
    ( k3_funct_2(esk3_0,esk4_0,esk5_0,X1) = k1_funct_1(esk5_0,X1)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_16])]),c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk5_0),X1)))
    | m1_subset_1(esk1_3(k1_relat_1(esk5_0),X1,esk5_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_37]),c_0_41])])).

cnf(c_0_45,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_46,plain,(
    ! [X15,X16] :
      ( ( ~ v5_relat_1(X16,X15)
        | r1_tarski(k2_relat_1(X16),X15)
        | ~ v1_relat_1(X16) )
      & ( ~ r1_tarski(k2_relat_1(X16),X15)
        | v5_relat_1(X16,X15)
        | ~ v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_47,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_48,negated_conjecture,
    ( k3_funct_2(esk3_0,esk4_0,esk5_0,esk1_3(k1_relat_1(esk5_0),X1,esk5_0)) = k1_funct_1(esk5_0,esk1_3(k1_relat_1(esk5_0),X1,esk5_0))
    | m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk5_0),X1))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( ~ r1_tarski(k2_relset_1(esk3_0,esk4_0,esk5_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_50,negated_conjecture,
    ( k2_relset_1(esk3_0,esk4_0,esk5_0) = k2_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_16])).

cnf(c_0_51,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( k3_funct_2(esk3_0,esk4_0,esk5_0,esk1_3(k1_relat_1(esk5_0),X1,esk5_0)) = k1_funct_1(esk5_0,esk1_3(k1_relat_1(esk5_0),X1,esk5_0))
    | v5_relat_1(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(k3_funct_2(esk3_0,esk4_0,esk5_0,X1),esk2_0)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_54,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk5_0),esk2_0) ),
    inference(rw,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( k3_funct_2(esk3_0,esk4_0,esk5_0,esk1_3(k1_relat_1(esk5_0),X1,esk5_0)) = k1_funct_1(esk5_0,esk1_3(k1_relat_1(esk5_0),X1,esk5_0))
    | r1_tarski(k2_relat_1(esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_41])])).

cnf(c_0_56,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(k1_funct_1(X1,esk1_3(X2,X3,X1)),X3)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(k3_funct_2(esk3_0,esk4_0,esk5_0,esk1_3(k1_relat_1(esk5_0),X1,esk5_0)),esk2_0)
    | m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk5_0),X1))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_44])).

cnf(c_0_58,negated_conjecture,
    ( k3_funct_2(esk3_0,esk4_0,esk5_0,esk1_3(k1_relat_1(esk5_0),esk2_0,esk5_0)) = k1_funct_1(esk5_0,esk1_3(k1_relat_1(esk5_0),esk2_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_59,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k1_funct_1(X1,esk1_3(k1_relat_1(X1),X2,X1)),X2) ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,esk1_3(k1_relat_1(esk5_0),esk2_0,esk5_0)),esk2_0)
    | m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk5_0),esk2_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk5_0),esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_37]),c_0_41])])).

cnf(c_0_62,negated_conjecture,
    ( v5_relat_1(esk5_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_61])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_62]),c_0_41])]),c_0_54]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:29:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.21/0.37  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.21/0.37  #
% 0.21/0.37  # Preprocessing time       : 0.016 s
% 0.21/0.37  # Presaturation interreduction done
% 0.21/0.37  
% 0.21/0.37  # Proof found!
% 0.21/0.37  # SZS status Theorem
% 0.21/0.37  # SZS output start CNFRefutation
% 0.21/0.37  fof(t191_funct_2, conjecture, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>(![X5]:(m1_subset_1(X5,X2)=>r2_hidden(k3_funct_2(X2,X3,X4,X5),X1))=>r1_tarski(k2_relset_1(X2,X3,X4),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t191_funct_2)).
% 0.21/0.37  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.21/0.37  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.21/0.37  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.21/0.37  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.21/0.37  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.21/0.37  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.21/0.37  fof(t5_funct_2, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X3)=X1&![X4]:(r2_hidden(X4,X1)=>r2_hidden(k1_funct_1(X3,X4),X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 0.21/0.37  fof(redefinition_k3_funct_2, axiom, ![X1, X2, X3, X4]:(((((~(v1_xboole_0(X1))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,X1))=>k3_funct_2(X1,X2,X3,X4)=k1_funct_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 0.21/0.37  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.21/0.37  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.21/0.37  fof(c_0_11, negated_conjecture, ~(![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>(![X5]:(m1_subset_1(X5,X2)=>r2_hidden(k3_funct_2(X2,X3,X4,X5),X1))=>r1_tarski(k2_relset_1(X2,X3,X4),X1)))))), inference(assume_negation,[status(cth)],[t191_funct_2])).
% 0.21/0.37  fof(c_0_12, plain, ![X19, X20, X21]:((v4_relat_1(X21,X19)|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))&(v5_relat_1(X21,X20)|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.21/0.37  fof(c_0_13, negated_conjecture, ![X37]:(~v1_xboole_0(esk3_0)&(~v1_xboole_0(esk4_0)&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk3_0,esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))))&((~m1_subset_1(X37,esk3_0)|r2_hidden(k3_funct_2(esk3_0,esk4_0,esk5_0,X37),esk2_0))&~r1_tarski(k2_relset_1(esk3_0,esk4_0,esk5_0),esk2_0))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])).
% 0.21/0.37  fof(c_0_14, plain, ![X13, X14]:((~v4_relat_1(X14,X13)|r1_tarski(k1_relat_1(X14),X13)|~v1_relat_1(X14))&(~r1_tarski(k1_relat_1(X14),X13)|v4_relat_1(X14,X13)|~v1_relat_1(X14))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.21/0.37  cnf(c_0_15, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.37  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.37  cnf(c_0_17, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.37  cnf(c_0_18, negated_conjecture, (v4_relat_1(esk5_0,esk3_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.21/0.37  fof(c_0_19, plain, ![X11, X12]:(~v1_relat_1(X11)|(~m1_subset_1(X12,k1_zfmisc_1(X11))|v1_relat_1(X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.21/0.37  cnf(c_0_20, negated_conjecture, (r1_tarski(k1_relat_1(esk5_0),esk3_0)|~v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.21/0.37  cnf(c_0_21, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.37  fof(c_0_22, plain, ![X17, X18]:v1_relat_1(k2_zfmisc_1(X17,X18)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.21/0.37  fof(c_0_23, plain, ![X6, X7]:((~m1_subset_1(X6,k1_zfmisc_1(X7))|r1_tarski(X6,X7))&(~r1_tarski(X6,X7)|m1_subset_1(X6,k1_zfmisc_1(X7)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.21/0.37  cnf(c_0_24, negated_conjecture, (r1_tarski(k1_relat_1(esk5_0),esk3_0)|~v1_relat_1(X1)|~m1_subset_1(esk5_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.21/0.37  cnf(c_0_25, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.37  fof(c_0_26, plain, ![X8, X9, X10]:(~r2_hidden(X8,X9)|~m1_subset_1(X9,k1_zfmisc_1(X10))|m1_subset_1(X8,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.21/0.37  cnf(c_0_27, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.37  cnf(c_0_28, negated_conjecture, (r1_tarski(k1_relat_1(esk5_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_16]), c_0_25])])).
% 0.21/0.37  fof(c_0_29, plain, ![X29, X30, X31]:((((v1_funct_1(X31)|(r2_hidden(esk1_3(X29,X30,X31),X29)|k1_relat_1(X31)!=X29)|(~v1_relat_1(X31)|~v1_funct_1(X31)))&(v1_funct_2(X31,X29,X30)|(r2_hidden(esk1_3(X29,X30,X31),X29)|k1_relat_1(X31)!=X29)|(~v1_relat_1(X31)|~v1_funct_1(X31))))&(m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|(r2_hidden(esk1_3(X29,X30,X31),X29)|k1_relat_1(X31)!=X29)|(~v1_relat_1(X31)|~v1_funct_1(X31))))&(((v1_funct_1(X31)|(~r2_hidden(k1_funct_1(X31,esk1_3(X29,X30,X31)),X30)|k1_relat_1(X31)!=X29)|(~v1_relat_1(X31)|~v1_funct_1(X31)))&(v1_funct_2(X31,X29,X30)|(~r2_hidden(k1_funct_1(X31,esk1_3(X29,X30,X31)),X30)|k1_relat_1(X31)!=X29)|(~v1_relat_1(X31)|~v1_funct_1(X31))))&(m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|(~r2_hidden(k1_funct_1(X31,esk1_3(X29,X30,X31)),X30)|k1_relat_1(X31)!=X29)|(~v1_relat_1(X31)|~v1_funct_1(X31))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_funct_2])])])])).
% 0.21/0.37  fof(c_0_30, plain, ![X25, X26, X27, X28]:(v1_xboole_0(X25)|~v1_funct_1(X27)|~v1_funct_2(X27,X25,X26)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|~m1_subset_1(X28,X25)|k3_funct_2(X25,X26,X27,X28)=k1_funct_1(X27,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).
% 0.21/0.37  cnf(c_0_31, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.37  cnf(c_0_32, negated_conjecture, (m1_subset_1(k1_relat_1(esk5_0),k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.21/0.37  cnf(c_0_33, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|r2_hidden(esk1_3(X2,X3,X1),X2)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.37  cnf(c_0_34, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_21, c_0_25])).
% 0.21/0.37  cnf(c_0_35, plain, (v1_xboole_0(X1)|k3_funct_2(X1,X3,X2,X4)=k1_funct_1(X2,X4)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~m1_subset_1(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.37  cnf(c_0_36, negated_conjecture, (v1_funct_2(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.37  cnf(c_0_37, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.37  cnf(c_0_38, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.37  cnf(c_0_39, negated_conjecture, (m1_subset_1(X1,esk3_0)|~r2_hidden(X1,k1_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.21/0.37  cnf(c_0_40, plain, (r2_hidden(esk1_3(k1_relat_1(X1),X2,X1),k1_relat_1(X1))|m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_33])).
% 0.21/0.37  cnf(c_0_41, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_34, c_0_16])).
% 0.21/0.37  fof(c_0_42, plain, ![X22, X23, X24]:(~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))|k2_relset_1(X22,X23,X24)=k2_relat_1(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.21/0.37  cnf(c_0_43, negated_conjecture, (k3_funct_2(esk3_0,esk4_0,esk5_0,X1)=k1_funct_1(esk5_0,X1)|~m1_subset_1(X1,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_16])]), c_0_38])).
% 0.21/0.37  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk5_0),X1)))|m1_subset_1(esk1_3(k1_relat_1(esk5_0),X1,esk5_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_37]), c_0_41])])).
% 0.21/0.37  cnf(c_0_45, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.37  fof(c_0_46, plain, ![X15, X16]:((~v5_relat_1(X16,X15)|r1_tarski(k2_relat_1(X16),X15)|~v1_relat_1(X16))&(~r1_tarski(k2_relat_1(X16),X15)|v5_relat_1(X16,X15)|~v1_relat_1(X16))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.21/0.37  cnf(c_0_47, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.37  cnf(c_0_48, negated_conjecture, (k3_funct_2(esk3_0,esk4_0,esk5_0,esk1_3(k1_relat_1(esk5_0),X1,esk5_0))=k1_funct_1(esk5_0,esk1_3(k1_relat_1(esk5_0),X1,esk5_0))|m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk5_0),X1)))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.21/0.37  cnf(c_0_49, negated_conjecture, (~r1_tarski(k2_relset_1(esk3_0,esk4_0,esk5_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.37  cnf(c_0_50, negated_conjecture, (k2_relset_1(esk3_0,esk4_0,esk5_0)=k2_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_45, c_0_16])).
% 0.21/0.37  cnf(c_0_51, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.37  cnf(c_0_52, negated_conjecture, (k3_funct_2(esk3_0,esk4_0,esk5_0,esk1_3(k1_relat_1(esk5_0),X1,esk5_0))=k1_funct_1(esk5_0,esk1_3(k1_relat_1(esk5_0),X1,esk5_0))|v5_relat_1(esk5_0,X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.21/0.37  cnf(c_0_53, negated_conjecture, (r2_hidden(k3_funct_2(esk3_0,esk4_0,esk5_0,X1),esk2_0)|~m1_subset_1(X1,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.37  cnf(c_0_54, negated_conjecture, (~r1_tarski(k2_relat_1(esk5_0),esk2_0)), inference(rw,[status(thm)],[c_0_49, c_0_50])).
% 0.21/0.37  cnf(c_0_55, negated_conjecture, (k3_funct_2(esk3_0,esk4_0,esk5_0,esk1_3(k1_relat_1(esk5_0),X1,esk5_0))=k1_funct_1(esk5_0,esk1_3(k1_relat_1(esk5_0),X1,esk5_0))|r1_tarski(k2_relat_1(esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_41])])).
% 0.21/0.37  cnf(c_0_56, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(k1_funct_1(X1,esk1_3(X2,X3,X1)),X3)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.37  cnf(c_0_57, negated_conjecture, (r2_hidden(k3_funct_2(esk3_0,esk4_0,esk5_0,esk1_3(k1_relat_1(esk5_0),X1,esk5_0)),esk2_0)|m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk5_0),X1)))), inference(spm,[status(thm)],[c_0_53, c_0_44])).
% 0.21/0.37  cnf(c_0_58, negated_conjecture, (k3_funct_2(esk3_0,esk4_0,esk5_0,esk1_3(k1_relat_1(esk5_0),esk2_0,esk5_0))=k1_funct_1(esk5_0,esk1_3(k1_relat_1(esk5_0),esk2_0,esk5_0))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.21/0.37  cnf(c_0_59, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(k1_funct_1(X1,esk1_3(k1_relat_1(X1),X2,X1)),X2)), inference(er,[status(thm)],[c_0_56])).
% 0.21/0.37  cnf(c_0_60, negated_conjecture, (r2_hidden(k1_funct_1(esk5_0,esk1_3(k1_relat_1(esk5_0),esk2_0,esk5_0)),esk2_0)|m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk5_0),esk2_0)))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.21/0.37  cnf(c_0_61, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk5_0),esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_37]), c_0_41])])).
% 0.21/0.37  cnf(c_0_62, negated_conjecture, (v5_relat_1(esk5_0,esk2_0)), inference(spm,[status(thm)],[c_0_47, c_0_61])).
% 0.21/0.37  cnf(c_0_63, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_62]), c_0_41])]), c_0_54]), ['proof']).
% 0.21/0.37  # SZS output end CNFRefutation
% 0.21/0.37  # Proof object total steps             : 64
% 0.21/0.37  # Proof object clause steps            : 41
% 0.21/0.37  # Proof object formula steps           : 23
% 0.21/0.37  # Proof object conjectures             : 29
% 0.21/0.37  # Proof object clause conjectures      : 26
% 0.21/0.37  # Proof object formula conjectures     : 3
% 0.21/0.37  # Proof object initial clauses used    : 18
% 0.21/0.37  # Proof object initial formulas used   : 11
% 0.21/0.37  # Proof object generating inferences   : 20
% 0.21/0.37  # Proof object simplifying inferences  : 20
% 0.21/0.37  # Training examples: 0 positive, 0 negative
% 0.21/0.37  # Parsed axioms                        : 11
% 0.21/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.37  # Initial clauses                      : 26
% 0.21/0.37  # Removed in clause preprocessing      : 2
% 0.21/0.37  # Initial clauses in saturation        : 24
% 0.21/0.37  # Processed clauses                    : 93
% 0.21/0.37  # ...of these trivial                  : 0
% 0.21/0.37  # ...subsumed                          : 1
% 0.21/0.37  # ...remaining for further processing  : 92
% 0.21/0.37  # Other redundant clauses eliminated   : 4
% 0.21/0.37  # Clauses deleted for lack of memory   : 0
% 0.21/0.37  # Backward-subsumed                    : 0
% 0.21/0.37  # Backward-rewritten                   : 5
% 0.21/0.37  # Generated clauses                    : 79
% 0.21/0.37  # ...of the previous two non-trivial   : 64
% 0.21/0.37  # Contextual simplify-reflections      : 1
% 0.21/0.37  # Paramodulations                      : 75
% 0.21/0.37  # Factorizations                       : 0
% 0.21/0.37  # Equation resolutions                 : 4
% 0.21/0.37  # Propositional unsat checks           : 0
% 0.21/0.37  #    Propositional check models        : 0
% 0.21/0.37  #    Propositional check unsatisfiable : 0
% 0.21/0.37  #    Propositional clauses             : 0
% 0.21/0.37  #    Propositional clauses after purity: 0
% 0.21/0.37  #    Propositional unsat core size     : 0
% 0.21/0.37  #    Propositional preprocessing time  : 0.000
% 0.21/0.37  #    Propositional encoding time       : 0.000
% 0.21/0.37  #    Propositional solver time         : 0.000
% 0.21/0.37  #    Success case prop preproc time    : 0.000
% 0.21/0.37  #    Success case prop encoding time   : 0.000
% 0.21/0.37  #    Success case prop solver time     : 0.000
% 0.21/0.37  # Current number of processed clauses  : 59
% 0.21/0.37  #    Positive orientable unit clauses  : 16
% 0.21/0.37  #    Positive unorientable unit clauses: 0
% 0.21/0.37  #    Negative unit clauses             : 3
% 0.21/0.37  #    Non-unit-clauses                  : 40
% 0.21/0.37  # Current number of unprocessed clauses: 18
% 0.21/0.37  # ...number of literals in the above   : 67
% 0.21/0.37  # Current number of archived formulas  : 0
% 0.21/0.37  # Current number of archived clauses   : 29
% 0.21/0.37  # Clause-clause subsumption calls (NU) : 151
% 0.21/0.37  # Rec. Clause-clause subsumption calls : 90
% 0.21/0.37  # Non-unit clause-clause subsumptions  : 2
% 0.21/0.37  # Unit Clause-clause subsumption calls : 12
% 0.21/0.37  # Rewrite failures with RHS unbound    : 0
% 0.21/0.37  # BW rewrite match attempts            : 8
% 0.21/0.37  # BW rewrite match successes           : 4
% 0.21/0.37  # Condensation attempts                : 0
% 0.21/0.37  # Condensation successes               : 0
% 0.21/0.37  # Termbank termtop insertions          : 3410
% 0.21/0.37  
% 0.21/0.37  # -------------------------------------------------
% 0.21/0.37  # User time                : 0.020 s
% 0.21/0.37  # System time              : 0.002 s
% 0.21/0.37  # Total time               : 0.022 s
% 0.21/0.37  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
