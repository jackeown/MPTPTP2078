%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:43 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 782 expanded)
%              Number of clauses        :   64 ( 301 expanded)
%              Number of leaves         :   15 ( 194 expanded)
%              Depth                    :   12
%              Number of atoms          :  467 (6309 expanded)
%              Number of equality atoms :   87 (1155 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal clause size      :   55 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t6_tmap_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( ~ v1_xboole_0(X3)
                & m1_subset_1(X3,k1_zfmisc_1(X1)) )
             => ! [X4] :
                  ( ( ~ v1_xboole_0(X4)
                    & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                 => ( r1_subset_1(X3,X4)
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,X3,X2)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) )
                       => ! [X6] :
                            ( ( v1_funct_1(X6)
                              & v1_funct_2(X6,X4,X2)
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) )
                           => ( k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4)) = k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))
                              & k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3) = X5
                              & k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4) = X6 ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tmap_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t207_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_xboole_0(X1,X2)
       => k7_relat_1(k7_relat_1(X3,X1),X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(redefinition_r1_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2) )
     => ( r1_subset_1(X1,X2)
      <=> r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(d1_tmap_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( ~ v1_xboole_0(X3)
                & m1_subset_1(X3,k1_zfmisc_1(X1)) )
             => ! [X4] :
                  ( ( ~ v1_xboole_0(X4)
                    & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,X3,X2)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) )
                     => ! [X6] :
                          ( ( v1_funct_1(X6)
                            & v1_funct_2(X6,X4,X2)
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) )
                         => ( k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4)) = k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))
                           => ! [X7] :
                                ( ( v1_funct_1(X7)
                                  & v1_funct_2(X7,k4_subset_1(X1,X3,X4),X2)
                                  & m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))) )
                               => ( X7 = k1_tmap_1(X1,X2,X3,X4,X5,X6)
                                <=> ( k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X3) = X5
                                    & k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X4) = X6 ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tmap_1)).

fof(dt_k1_tmap_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X3)
        & m1_subset_1(X3,k1_zfmisc_1(X1))
        & ~ v1_xboole_0(X4)
        & m1_subset_1(X4,k1_zfmisc_1(X1))
        & v1_funct_1(X5)
        & v1_funct_2(X5,X3,X2)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
        & v1_funct_1(X6)
        & v1_funct_2(X6,X4,X2)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) )
     => ( v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))
        & v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)
        & m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tmap_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( ~ v1_xboole_0(X3)
                  & m1_subset_1(X3,k1_zfmisc_1(X1)) )
               => ! [X4] :
                    ( ( ~ v1_xboole_0(X4)
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                   => ( r1_subset_1(X3,X4)
                     => ! [X5] :
                          ( ( v1_funct_1(X5)
                            & v1_funct_2(X5,X3,X2)
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) )
                         => ! [X6] :
                              ( ( v1_funct_1(X6)
                                & v1_funct_2(X6,X4,X2)
                                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) )
                             => ( k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4)) = k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))
                                & k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3) = X5
                                & k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4) = X6 ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t6_tmap_1])).

fof(c_0_16,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v1_xboole_0(X8)
        | ~ r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_1(X10),X10)
        | v1_xboole_0(X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_17,plain,(
    ! [X14,X15,X17,X18,X19] :
      ( ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_xboole_0(X14,X15) )
      & ( r2_hidden(esk2_2(X14,X15),X15)
        | r1_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X19,X17)
        | ~ r2_hidden(X19,X18)
        | ~ r1_xboole_0(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_18,plain,(
    ! [X35,X36,X37] :
      ( ( v4_relat_1(X37,X35)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( v5_relat_1(X37,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_19,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0)
    & ~ v1_xboole_0(esk4_0)
    & ~ v1_xboole_0(esk5_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))
    & ~ v1_xboole_0(esk6_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0))
    & r1_subset_1(esk5_0,esk6_0)
    & v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,esk5_0,esk4_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0)))
    & v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,esk6_0,esk4_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk4_0)))
    & ( k2_partfun1(esk5_0,esk4_0,esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0)) != k2_partfun1(esk6_0,esk4_0,esk8_0,k9_subset_1(esk3_0,esk5_0,esk6_0))
      | k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk5_0) != esk7_0
      | k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk6_0) != esk8_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

fof(c_0_20,plain,(
    ! [X32,X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | v1_relat_1(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_21,plain,(
    ! [X25,X26,X27] :
      ( ~ v1_relat_1(X27)
      | ~ r1_xboole_0(X25,X26)
      | k7_relat_1(k7_relat_1(X27,X25),X26) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t207_relat_1])])).

cnf(c_0_22,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X38,X39,X40,X41] :
      ( ~ v1_funct_1(X40)
      | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
      | k2_partfun1(X38,X39,X40,X41) = k7_relat_1(X40,X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

fof(c_0_25,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X29)
      | ~ v4_relat_1(X29,X28)
      | X29 = k7_relat_1(X29,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_26,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_29,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(X20))
      | k9_subset_1(X20,X21,X22) = k3_xboole_0(X21,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_30,plain,(
    ! [X23,X24] : k1_setfam_1(k2_tarski(X23,X24)) = k3_xboole_0(X23,X24) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_31,plain,(
    ! [X12,X13] :
      ( ( ~ r1_xboole_0(X12,X13)
        | k3_xboole_0(X12,X13) = k1_xboole_0 )
      & ( k3_xboole_0(X12,X13) != k1_xboole_0
        | r1_xboole_0(X12,X13) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_32,plain,(
    ! [X30,X31] :
      ( ( ~ r1_subset_1(X30,X31)
        | r1_xboole_0(X30,X31)
        | v1_xboole_0(X30)
        | v1_xboole_0(X31) )
      & ( ~ r1_xboole_0(X30,X31)
        | r1_subset_1(X30,X31)
        | v1_xboole_0(X30)
        | v1_xboole_0(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).

cnf(c_0_33,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,plain,
    ( r1_xboole_0(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_35,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_37,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,negated_conjecture,
    ( v4_relat_1(esk8_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_39,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_27])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_41,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,plain,
    ( r1_xboole_0(X1,X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,negated_conjecture,
    ( r1_subset_1(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_46,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_47,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_48,plain,(
    ! [X42,X43,X44,X45,X46,X47,X48] :
      ( ( k2_partfun1(k4_subset_1(X42,X44,X45),X43,X48,X44) = X46
        | X48 != k1_tmap_1(X42,X43,X44,X45,X46,X47)
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,k4_subset_1(X42,X44,X45),X43)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X42,X44,X45),X43)))
        | k2_partfun1(X44,X43,X46,k9_subset_1(X42,X44,X45)) != k2_partfun1(X45,X43,X47,k9_subset_1(X42,X44,X45))
        | ~ v1_funct_1(X47)
        | ~ v1_funct_2(X47,X45,X43)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X43)))
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,X44,X43)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X43)))
        | v1_xboole_0(X45)
        | ~ m1_subset_1(X45,k1_zfmisc_1(X42))
        | v1_xboole_0(X44)
        | ~ m1_subset_1(X44,k1_zfmisc_1(X42))
        | v1_xboole_0(X43)
        | v1_xboole_0(X42) )
      & ( k2_partfun1(k4_subset_1(X42,X44,X45),X43,X48,X45) = X47
        | X48 != k1_tmap_1(X42,X43,X44,X45,X46,X47)
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,k4_subset_1(X42,X44,X45),X43)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X42,X44,X45),X43)))
        | k2_partfun1(X44,X43,X46,k9_subset_1(X42,X44,X45)) != k2_partfun1(X45,X43,X47,k9_subset_1(X42,X44,X45))
        | ~ v1_funct_1(X47)
        | ~ v1_funct_2(X47,X45,X43)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X43)))
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,X44,X43)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X43)))
        | v1_xboole_0(X45)
        | ~ m1_subset_1(X45,k1_zfmisc_1(X42))
        | v1_xboole_0(X44)
        | ~ m1_subset_1(X44,k1_zfmisc_1(X42))
        | v1_xboole_0(X43)
        | v1_xboole_0(X42) )
      & ( k2_partfun1(k4_subset_1(X42,X44,X45),X43,X48,X44) != X46
        | k2_partfun1(k4_subset_1(X42,X44,X45),X43,X48,X45) != X47
        | X48 = k1_tmap_1(X42,X43,X44,X45,X46,X47)
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,k4_subset_1(X42,X44,X45),X43)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X42,X44,X45),X43)))
        | k2_partfun1(X44,X43,X46,k9_subset_1(X42,X44,X45)) != k2_partfun1(X45,X43,X47,k9_subset_1(X42,X44,X45))
        | ~ v1_funct_1(X47)
        | ~ v1_funct_2(X47,X45,X43)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X43)))
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,X44,X43)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X43)))
        | v1_xboole_0(X45)
        | ~ m1_subset_1(X45,k1_zfmisc_1(X42))
        | v1_xboole_0(X44)
        | ~ m1_subset_1(X44,k1_zfmisc_1(X42))
        | v1_xboole_0(X43)
        | v1_xboole_0(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tmap_1])])])])])).

fof(c_0_49,plain,(
    ! [X49,X50,X51,X52,X53,X54] :
      ( ( v1_funct_1(k1_tmap_1(X49,X50,X51,X52,X53,X54))
        | v1_xboole_0(X49)
        | v1_xboole_0(X50)
        | v1_xboole_0(X51)
        | ~ m1_subset_1(X51,k1_zfmisc_1(X49))
        | v1_xboole_0(X52)
        | ~ m1_subset_1(X52,k1_zfmisc_1(X49))
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,X51,X50)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X50)))
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X52,X50)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X50))) )
      & ( v1_funct_2(k1_tmap_1(X49,X50,X51,X52,X53,X54),k4_subset_1(X49,X51,X52),X50)
        | v1_xboole_0(X49)
        | v1_xboole_0(X50)
        | v1_xboole_0(X51)
        | ~ m1_subset_1(X51,k1_zfmisc_1(X49))
        | v1_xboole_0(X52)
        | ~ m1_subset_1(X52,k1_zfmisc_1(X49))
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,X51,X50)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X50)))
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X52,X50)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X50))) )
      & ( m1_subset_1(k1_tmap_1(X49,X50,X51,X52,X53,X54),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X49,X51,X52),X50)))
        | v1_xboole_0(X49)
        | v1_xboole_0(X50)
        | v1_xboole_0(X51)
        | ~ m1_subset_1(X51,k1_zfmisc_1(X49))
        | v1_xboole_0(X52)
        | ~ m1_subset_1(X52,k1_zfmisc_1(X49))
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,X51,X50)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X50)))
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X52,X50)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X50))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tmap_1])])])])).

cnf(c_0_50,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_51,negated_conjecture,
    ( k7_relat_1(esk8_0,X1) = k2_partfun1(esk6_0,esk4_0,esk8_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_27]),c_0_36])])).

cnf(c_0_52,negated_conjecture,
    ( k7_relat_1(esk8_0,esk6_0) = esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_54,negated_conjecture,
    ( v4_relat_1(esk7_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_40])).

cnf(c_0_55,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_40])).

cnf(c_0_56,plain,
    ( k9_subset_1(X2,X3,X1) = k1_setfam_1(k2_tarski(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_58,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_43,c_0_42])).

cnf(c_0_59,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47])).

cnf(c_0_60,plain,
    ( k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X3) = X6
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | X5 != k1_tmap_1(X1,X4,X2,X3,X7,X6)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))
    | k2_partfun1(X2,X4,X7,k9_subset_1(X1,X2,X3)) != k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,X3,X4)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X7)
    | ~ v1_funct_2(X7,X2,X4)
    | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_61,plain,
    ( m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,X4,X2)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_62,plain,
    ( v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,X4,X2)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_63,plain,
    ( v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,X4,X2)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_64,negated_conjecture,
    ( k7_relat_1(k2_partfun1(esk6_0,esk4_0,esk8_0,X1),X2) = k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_39]),c_0_51])).

cnf(c_0_65,negated_conjecture,
    ( k2_partfun1(esk6_0,esk4_0,esk8_0,esk6_0) = esk8_0 ),
    inference(rw,[status(thm)],[c_0_52,c_0_51])).

cnf(c_0_66,negated_conjecture,
    ( k7_relat_1(esk7_0,X1) = k2_partfun1(esk5_0,esk4_0,esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_40]),c_0_53])])).

cnf(c_0_67,negated_conjecture,
    ( k7_relat_1(esk7_0,esk5_0) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_54]),c_0_55])])).

cnf(c_0_68,negated_conjecture,
    ( k2_partfun1(esk5_0,esk4_0,esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0)) != k2_partfun1(esk6_0,esk4_0,esk8_0,k9_subset_1(esk3_0,esk5_0,esk6_0))
    | k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk5_0) != esk7_0
    | k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk6_0) != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_69,negated_conjecture,
    ( k9_subset_1(esk3_0,X1,esk6_0) = k1_setfam_1(k2_tarski(X1,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_70,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk5_0,esk6_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_71,plain,
    ( k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X3) = X6
    | v1_xboole_0(X4)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3)) != k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))
    | ~ v1_funct_2(X5,X2,X4)
    | ~ v1_funct_2(X6,X3,X4)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_60]),c_0_61]),c_0_62]),c_0_63])).

cnf(c_0_72,negated_conjecture,
    ( k2_partfun1(esk6_0,esk4_0,esk8_0,X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_51])).

cnf(c_0_73,negated_conjecture,
    ( v1_funct_2(esk8_0,esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_74,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_75,negated_conjecture,
    ( k7_relat_1(k2_partfun1(esk5_0,esk4_0,esk7_0,X1),X2) = k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_55]),c_0_66])).

cnf(c_0_76,negated_conjecture,
    ( k2_partfun1(esk5_0,esk4_0,esk7_0,esk5_0) = esk7_0 ),
    inference(rw,[status(thm)],[c_0_67,c_0_66])).

cnf(c_0_77,plain,
    ( k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X2) = X6
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | X5 != k1_tmap_1(X1,X4,X2,X3,X6,X7)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))
    | k2_partfun1(X2,X4,X6,k9_subset_1(X1,X2,X3)) != k2_partfun1(X3,X4,X7,k9_subset_1(X1,X2,X3))
    | ~ v1_funct_1(X7)
    | ~ v1_funct_2(X7,X3,X4)
    | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,X2,X4)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_78,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk5_0) != esk7_0
    | k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk6_0) != esk8_0
    | k2_partfun1(esk6_0,esk4_0,esk8_0,k1_xboole_0) != k2_partfun1(esk5_0,esk4_0,esk7_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_69]),c_0_70]),c_0_69]),c_0_70])).

cnf(c_0_79,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_80,negated_conjecture,
    ( k2_partfun1(k4_subset_1(X1,X2,esk6_0),esk4_0,k1_tmap_1(X1,esk4_0,X2,esk6_0,X3,esk8_0),esk6_0) = esk8_0
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(X2,esk4_0,X3,k9_subset_1(X1,X2,esk6_0)) != k1_xboole_0
    | ~ v1_funct_2(X3,X2,esk4_0)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,esk4_0)))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(k9_subset_1(X1,X2,esk6_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73]),c_0_36]),c_0_27])]),c_0_46]),c_0_74])).

cnf(c_0_81,negated_conjecture,
    ( k2_partfun1(esk5_0,esk4_0,esk7_0,X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_66])).

cnf(c_0_82,negated_conjecture,
    ( v1_funct_2(esk7_0,esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_83,plain,
    ( k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X2) = X5
    | v1_xboole_0(X4)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3)) != k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))
    | ~ v1_funct_2(X6,X3,X4)
    | ~ v1_funct_2(X5,X2,X4)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_77]),c_0_61]),c_0_62]),c_0_63])).

cnf(c_0_84,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_85,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk5_0) != esk7_0
    | k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk6_0) != esk8_0
    | k2_partfun1(esk5_0,esk4_0,esk7_0,k1_xboole_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_72]),c_0_79])])).

cnf(c_0_86,negated_conjecture,
    ( k2_partfun1(k4_subset_1(X1,esk5_0,esk6_0),esk4_0,k1_tmap_1(X1,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk6_0) = esk8_0
    | v1_xboole_0(X1)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(k9_subset_1(X1,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82]),c_0_53]),c_0_40])]),c_0_47])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_88,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk3_0,X1,esk6_0),X2,k1_tmap_1(esk3_0,X2,X1,esk6_0,X3,X4),X1) = X3
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X3,k1_setfam_1(k2_tarski(X1,esk6_0))) != k2_partfun1(esk6_0,X2,X4,k1_setfam_1(k2_tarski(X1,esk6_0)))
    | ~ v1_funct_2(X4,esk6_0,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(esk6_0,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_69]),c_0_57])]),c_0_84]),c_0_46])).

cnf(c_0_89,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk5_0) != esk7_0
    | k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk6_0) != esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_81]),c_0_79])])).

cnf(c_0_90,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk6_0) = esk8_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_69]),c_0_57]),c_0_87]),c_0_70]),c_0_79])]),c_0_84])).

cnf(c_0_91,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,X1),esk5_0) = esk7_0
    | k2_partfun1(esk6_0,esk4_0,X1,k1_xboole_0) != k1_xboole_0
    | ~ v1_funct_2(X1,esk6_0,esk4_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk4_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_81]),c_0_70]),c_0_82]),c_0_53]),c_0_40]),c_0_87]),c_0_70]),c_0_79])]),c_0_74]),c_0_47])).

cnf(c_0_92,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk5_0) != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_90])])).

cnf(c_0_93,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_72]),c_0_73]),c_0_36]),c_0_27]),c_0_79])]),c_0_92]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:20:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.42  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.19/0.42  # and selection function SelectCQIPrecWNTNp.
% 0.19/0.42  #
% 0.19/0.42  # Preprocessing time       : 0.029 s
% 0.19/0.42  # Presaturation interreduction done
% 0.19/0.42  
% 0.19/0.42  # Proof found!
% 0.19/0.42  # SZS status Theorem
% 0.19/0.42  # SZS output start CNFRefutation
% 0.19/0.42  fof(t6_tmap_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>(r1_subset_1(X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3)=X5)&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4)=X6)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 0.19/0.42  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.42  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.19/0.42  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.42  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.42  fof(t207_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_xboole_0(X1,X2)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 0.19/0.42  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 0.19/0.42  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 0.19/0.42  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.19/0.42  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.19/0.42  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.19/0.42  fof(redefinition_r1_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))=>(r1_subset_1(X1,X2)<=>r1_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 0.19/0.42  fof(d1_tmap_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>(k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))=>![X7]:(((v1_funct_1(X7)&v1_funct_2(X7,k4_subset_1(X1,X3,X4),X2))&m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))))=>(X7=k1_tmap_1(X1,X2,X3,X4,X5,X6)<=>(k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X3)=X5&k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X4)=X6)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 0.19/0.42  fof(dt_k1_tmap_1, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((((((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))&~(v1_xboole_0(X3)))&m1_subset_1(X3,k1_zfmisc_1(X1)))&~(v1_xboole_0(X4)))&m1_subset_1(X4,k1_zfmisc_1(X1)))&v1_funct_1(X5))&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2))&m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 0.19/0.42  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.42  fof(c_0_15, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>(r1_subset_1(X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3)=X5)&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4)=X6))))))))), inference(assume_negation,[status(cth)],[t6_tmap_1])).
% 0.19/0.42  fof(c_0_16, plain, ![X8, X9, X10]:((~v1_xboole_0(X8)|~r2_hidden(X9,X8))&(r2_hidden(esk1_1(X10),X10)|v1_xboole_0(X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.42  fof(c_0_17, plain, ![X14, X15, X17, X18, X19]:(((r2_hidden(esk2_2(X14,X15),X14)|r1_xboole_0(X14,X15))&(r2_hidden(esk2_2(X14,X15),X15)|r1_xboole_0(X14,X15)))&(~r2_hidden(X19,X17)|~r2_hidden(X19,X18)|~r1_xboole_0(X17,X18))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.19/0.42  fof(c_0_18, plain, ![X35, X36, X37]:((v4_relat_1(X37,X35)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))&(v5_relat_1(X37,X36)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.42  fof(c_0_19, negated_conjecture, (~v1_xboole_0(esk3_0)&(~v1_xboole_0(esk4_0)&((~v1_xboole_0(esk5_0)&m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0)))&((~v1_xboole_0(esk6_0)&m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0)))&(r1_subset_1(esk5_0,esk6_0)&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk5_0,esk4_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0))))&(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk6_0,esk4_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk4_0))))&(k2_partfun1(esk5_0,esk4_0,esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0))!=k2_partfun1(esk6_0,esk4_0,esk8_0,k9_subset_1(esk3_0,esk5_0,esk6_0))|k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk5_0)!=esk7_0|k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk6_0)!=esk8_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.19/0.42  fof(c_0_20, plain, ![X32, X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|v1_relat_1(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.42  fof(c_0_21, plain, ![X25, X26, X27]:(~v1_relat_1(X27)|(~r1_xboole_0(X25,X26)|k7_relat_1(k7_relat_1(X27,X25),X26)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t207_relat_1])])).
% 0.19/0.42  cnf(c_0_22, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.42  cnf(c_0_23, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.42  fof(c_0_24, plain, ![X38, X39, X40, X41]:(~v1_funct_1(X40)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|k2_partfun1(X38,X39,X40,X41)=k7_relat_1(X40,X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 0.19/0.42  fof(c_0_25, plain, ![X28, X29]:(~v1_relat_1(X29)|~v4_relat_1(X29,X28)|X29=k7_relat_1(X29,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.19/0.42  cnf(c_0_26, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.42  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.42  cnf(c_0_28, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.42  fof(c_0_29, plain, ![X20, X21, X22]:(~m1_subset_1(X22,k1_zfmisc_1(X20))|k9_subset_1(X20,X21,X22)=k3_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.19/0.42  fof(c_0_30, plain, ![X23, X24]:k1_setfam_1(k2_tarski(X23,X24))=k3_xboole_0(X23,X24), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.19/0.42  fof(c_0_31, plain, ![X12, X13]:((~r1_xboole_0(X12,X13)|k3_xboole_0(X12,X13)=k1_xboole_0)&(k3_xboole_0(X12,X13)!=k1_xboole_0|r1_xboole_0(X12,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.19/0.42  fof(c_0_32, plain, ![X30, X31]:((~r1_subset_1(X30,X31)|r1_xboole_0(X30,X31)|(v1_xboole_0(X30)|v1_xboole_0(X31)))&(~r1_xboole_0(X30,X31)|r1_subset_1(X30,X31)|(v1_xboole_0(X30)|v1_xboole_0(X31)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).
% 0.19/0.42  cnf(c_0_33, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.42  cnf(c_0_34, plain, (r1_xboole_0(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.42  cnf(c_0_35, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.42  cnf(c_0_36, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.42  cnf(c_0_37, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.42  cnf(c_0_38, negated_conjecture, (v4_relat_1(esk8_0,esk6_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.42  cnf(c_0_39, negated_conjecture, (v1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_28, c_0_27])).
% 0.19/0.42  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.42  cnf(c_0_41, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.42  cnf(c_0_42, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.42  cnf(c_0_43, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.42  cnf(c_0_44, plain, (r1_xboole_0(X1,X2)|v1_xboole_0(X1)|v1_xboole_0(X2)|~r1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.42  cnf(c_0_45, negated_conjecture, (r1_subset_1(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.42  cnf(c_0_46, negated_conjecture, (~v1_xboole_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.42  cnf(c_0_47, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.42  fof(c_0_48, plain, ![X42, X43, X44, X45, X46, X47, X48]:(((k2_partfun1(k4_subset_1(X42,X44,X45),X43,X48,X44)=X46|X48!=k1_tmap_1(X42,X43,X44,X45,X46,X47)|(~v1_funct_1(X48)|~v1_funct_2(X48,k4_subset_1(X42,X44,X45),X43)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X42,X44,X45),X43))))|k2_partfun1(X44,X43,X46,k9_subset_1(X42,X44,X45))!=k2_partfun1(X45,X43,X47,k9_subset_1(X42,X44,X45))|(~v1_funct_1(X47)|~v1_funct_2(X47,X45,X43)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X43))))|(~v1_funct_1(X46)|~v1_funct_2(X46,X44,X43)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X43))))|(v1_xboole_0(X45)|~m1_subset_1(X45,k1_zfmisc_1(X42)))|(v1_xboole_0(X44)|~m1_subset_1(X44,k1_zfmisc_1(X42)))|v1_xboole_0(X43)|v1_xboole_0(X42))&(k2_partfun1(k4_subset_1(X42,X44,X45),X43,X48,X45)=X47|X48!=k1_tmap_1(X42,X43,X44,X45,X46,X47)|(~v1_funct_1(X48)|~v1_funct_2(X48,k4_subset_1(X42,X44,X45),X43)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X42,X44,X45),X43))))|k2_partfun1(X44,X43,X46,k9_subset_1(X42,X44,X45))!=k2_partfun1(X45,X43,X47,k9_subset_1(X42,X44,X45))|(~v1_funct_1(X47)|~v1_funct_2(X47,X45,X43)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X43))))|(~v1_funct_1(X46)|~v1_funct_2(X46,X44,X43)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X43))))|(v1_xboole_0(X45)|~m1_subset_1(X45,k1_zfmisc_1(X42)))|(v1_xboole_0(X44)|~m1_subset_1(X44,k1_zfmisc_1(X42)))|v1_xboole_0(X43)|v1_xboole_0(X42)))&(k2_partfun1(k4_subset_1(X42,X44,X45),X43,X48,X44)!=X46|k2_partfun1(k4_subset_1(X42,X44,X45),X43,X48,X45)!=X47|X48=k1_tmap_1(X42,X43,X44,X45,X46,X47)|(~v1_funct_1(X48)|~v1_funct_2(X48,k4_subset_1(X42,X44,X45),X43)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X42,X44,X45),X43))))|k2_partfun1(X44,X43,X46,k9_subset_1(X42,X44,X45))!=k2_partfun1(X45,X43,X47,k9_subset_1(X42,X44,X45))|(~v1_funct_1(X47)|~v1_funct_2(X47,X45,X43)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X43))))|(~v1_funct_1(X46)|~v1_funct_2(X46,X44,X43)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X43))))|(v1_xboole_0(X45)|~m1_subset_1(X45,k1_zfmisc_1(X42)))|(v1_xboole_0(X44)|~m1_subset_1(X44,k1_zfmisc_1(X42)))|v1_xboole_0(X43)|v1_xboole_0(X42))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tmap_1])])])])])).
% 0.19/0.42  fof(c_0_49, plain, ![X49, X50, X51, X52, X53, X54]:(((v1_funct_1(k1_tmap_1(X49,X50,X51,X52,X53,X54))|(v1_xboole_0(X49)|v1_xboole_0(X50)|v1_xboole_0(X51)|~m1_subset_1(X51,k1_zfmisc_1(X49))|v1_xboole_0(X52)|~m1_subset_1(X52,k1_zfmisc_1(X49))|~v1_funct_1(X53)|~v1_funct_2(X53,X51,X50)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X50)))|~v1_funct_1(X54)|~v1_funct_2(X54,X52,X50)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X50)))))&(v1_funct_2(k1_tmap_1(X49,X50,X51,X52,X53,X54),k4_subset_1(X49,X51,X52),X50)|(v1_xboole_0(X49)|v1_xboole_0(X50)|v1_xboole_0(X51)|~m1_subset_1(X51,k1_zfmisc_1(X49))|v1_xboole_0(X52)|~m1_subset_1(X52,k1_zfmisc_1(X49))|~v1_funct_1(X53)|~v1_funct_2(X53,X51,X50)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X50)))|~v1_funct_1(X54)|~v1_funct_2(X54,X52,X50)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X50))))))&(m1_subset_1(k1_tmap_1(X49,X50,X51,X52,X53,X54),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X49,X51,X52),X50)))|(v1_xboole_0(X49)|v1_xboole_0(X50)|v1_xboole_0(X51)|~m1_subset_1(X51,k1_zfmisc_1(X49))|v1_xboole_0(X52)|~m1_subset_1(X52,k1_zfmisc_1(X49))|~v1_funct_1(X53)|~v1_funct_2(X53,X51,X50)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X50)))|~v1_funct_1(X54)|~v1_funct_2(X54,X52,X50)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X50)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tmap_1])])])])).
% 0.19/0.42  cnf(c_0_50, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k1_xboole_0|~v1_relat_1(X1)|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.42  cnf(c_0_51, negated_conjecture, (k7_relat_1(esk8_0,X1)=k2_partfun1(esk6_0,esk4_0,esk8_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_27]), c_0_36])])).
% 0.19/0.42  cnf(c_0_52, negated_conjecture, (k7_relat_1(esk8_0,esk6_0)=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])])).
% 0.19/0.42  cnf(c_0_53, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.42  cnf(c_0_54, negated_conjecture, (v4_relat_1(esk7_0,esk5_0)), inference(spm,[status(thm)],[c_0_26, c_0_40])).
% 0.19/0.42  cnf(c_0_55, negated_conjecture, (v1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_28, c_0_40])).
% 0.19/0.42  cnf(c_0_56, plain, (k9_subset_1(X2,X3,X1)=k1_setfam_1(k2_tarski(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.42  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.42  cnf(c_0_58, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_43, c_0_42])).
% 0.19/0.42  cnf(c_0_59, negated_conjecture, (r1_xboole_0(esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_47])).
% 0.19/0.42  cnf(c_0_60, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X3)=X6|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X4)|v1_xboole_0(X1)|X5!=k1_tmap_1(X1,X4,X2,X3,X7,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|k2_partfun1(X2,X4,X7,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_1(X6)|~v1_funct_2(X6,X3,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X7)|~v1_funct_2(X7,X2,X4)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.42  cnf(c_0_61, plain, (m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2)))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.42  cnf(c_0_62, plain, (v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.42  cnf(c_0_63, plain, (v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.42  cnf(c_0_64, negated_conjecture, (k7_relat_1(k2_partfun1(esk6_0,esk4_0,esk8_0,X1),X2)=k1_xboole_0|~v1_xboole_0(X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_39]), c_0_51])).
% 0.19/0.42  cnf(c_0_65, negated_conjecture, (k2_partfun1(esk6_0,esk4_0,esk8_0,esk6_0)=esk8_0), inference(rw,[status(thm)],[c_0_52, c_0_51])).
% 0.19/0.42  cnf(c_0_66, negated_conjecture, (k7_relat_1(esk7_0,X1)=k2_partfun1(esk5_0,esk4_0,esk7_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_40]), c_0_53])])).
% 0.19/0.42  cnf(c_0_67, negated_conjecture, (k7_relat_1(esk7_0,esk5_0)=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_54]), c_0_55])])).
% 0.19/0.42  cnf(c_0_68, negated_conjecture, (k2_partfun1(esk5_0,esk4_0,esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0))!=k2_partfun1(esk6_0,esk4_0,esk8_0,k9_subset_1(esk3_0,esk5_0,esk6_0))|k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk5_0)!=esk7_0|k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk6_0)!=esk8_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.42  cnf(c_0_69, negated_conjecture, (k9_subset_1(esk3_0,X1,esk6_0)=k1_setfam_1(k2_tarski(X1,esk6_0))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.42  cnf(c_0_70, negated_conjecture, (k1_setfam_1(k2_tarski(esk5_0,esk6_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.42  cnf(c_0_71, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X3)=X6|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_2(X5,X2,X4)|~v1_funct_2(X6,X3,X4)|~v1_funct_1(X5)|~v1_funct_1(X6)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_60]), c_0_61]), c_0_62]), c_0_63])).
% 0.19/0.42  cnf(c_0_72, negated_conjecture, (k2_partfun1(esk6_0,esk4_0,esk8_0,X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_51])).
% 0.19/0.42  cnf(c_0_73, negated_conjecture, (v1_funct_2(esk8_0,esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.42  cnf(c_0_74, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.42  cnf(c_0_75, negated_conjecture, (k7_relat_1(k2_partfun1(esk5_0,esk4_0,esk7_0,X1),X2)=k1_xboole_0|~v1_xboole_0(X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_55]), c_0_66])).
% 0.19/0.42  cnf(c_0_76, negated_conjecture, (k2_partfun1(esk5_0,esk4_0,esk7_0,esk5_0)=esk7_0), inference(rw,[status(thm)],[c_0_67, c_0_66])).
% 0.19/0.42  cnf(c_0_77, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X2)=X6|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X4)|v1_xboole_0(X1)|X5!=k1_tmap_1(X1,X4,X2,X3,X6,X7)|~v1_funct_1(X5)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|k2_partfun1(X2,X4,X6,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X7,k9_subset_1(X1,X2,X3))|~v1_funct_1(X7)|~v1_funct_2(X7,X3,X4)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X6)|~v1_funct_2(X6,X2,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.42  cnf(c_0_78, negated_conjecture, (k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk5_0)!=esk7_0|k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk6_0)!=esk8_0|k2_partfun1(esk6_0,esk4_0,esk8_0,k1_xboole_0)!=k2_partfun1(esk5_0,esk4_0,esk7_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_69]), c_0_70]), c_0_69]), c_0_70])).
% 0.19/0.42  cnf(c_0_79, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.42  cnf(c_0_80, negated_conjecture, (k2_partfun1(k4_subset_1(X1,X2,esk6_0),esk4_0,k1_tmap_1(X1,esk4_0,X2,esk6_0,X3,esk8_0),esk6_0)=esk8_0|v1_xboole_0(X2)|v1_xboole_0(X1)|k2_partfun1(X2,esk4_0,X3,k9_subset_1(X1,X2,esk6_0))!=k1_xboole_0|~v1_funct_2(X3,X2,esk4_0)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,esk4_0)))|~m1_subset_1(esk6_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_xboole_0(k9_subset_1(X1,X2,esk6_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73]), c_0_36]), c_0_27])]), c_0_46]), c_0_74])).
% 0.19/0.42  cnf(c_0_81, negated_conjecture, (k2_partfun1(esk5_0,esk4_0,esk7_0,X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_66])).
% 0.19/0.42  cnf(c_0_82, negated_conjecture, (v1_funct_2(esk7_0,esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.42  cnf(c_0_83, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X2)=X5|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_2(X6,X3,X4)|~v1_funct_2(X5,X2,X4)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_77]), c_0_61]), c_0_62]), c_0_63])).
% 0.19/0.42  cnf(c_0_84, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.42  cnf(c_0_85, negated_conjecture, (k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk5_0)!=esk7_0|k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk6_0)!=esk8_0|k2_partfun1(esk5_0,esk4_0,esk7_0,k1_xboole_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_72]), c_0_79])])).
% 0.19/0.42  cnf(c_0_86, negated_conjecture, (k2_partfun1(k4_subset_1(X1,esk5_0,esk6_0),esk4_0,k1_tmap_1(X1,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk6_0)=esk8_0|v1_xboole_0(X1)|~m1_subset_1(esk6_0,k1_zfmisc_1(X1))|~m1_subset_1(esk5_0,k1_zfmisc_1(X1))|~v1_xboole_0(k9_subset_1(X1,esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82]), c_0_53]), c_0_40])]), c_0_47])).
% 0.19/0.42  cnf(c_0_87, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.42  cnf(c_0_88, negated_conjecture, (k2_partfun1(k4_subset_1(esk3_0,X1,esk6_0),X2,k1_tmap_1(esk3_0,X2,X1,esk6_0,X3,X4),X1)=X3|v1_xboole_0(X2)|v1_xboole_0(X1)|k2_partfun1(X1,X2,X3,k1_setfam_1(k2_tarski(X1,esk6_0)))!=k2_partfun1(esk6_0,X2,X4,k1_setfam_1(k2_tarski(X1,esk6_0)))|~v1_funct_2(X4,esk6_0,X2)|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X4)|~v1_funct_1(X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(esk6_0,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X1,k1_zfmisc_1(esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_69]), c_0_57])]), c_0_84]), c_0_46])).
% 0.19/0.42  cnf(c_0_89, negated_conjecture, (k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk5_0)!=esk7_0|k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk6_0)!=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_81]), c_0_79])])).
% 0.19/0.42  cnf(c_0_90, negated_conjecture, (k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk6_0)=esk8_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_69]), c_0_57]), c_0_87]), c_0_70]), c_0_79])]), c_0_84])).
% 0.19/0.42  cnf(c_0_91, negated_conjecture, (k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,X1),esk5_0)=esk7_0|k2_partfun1(esk6_0,esk4_0,X1,k1_xboole_0)!=k1_xboole_0|~v1_funct_2(X1,esk6_0,esk4_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk4_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_81]), c_0_70]), c_0_82]), c_0_53]), c_0_40]), c_0_87]), c_0_70]), c_0_79])]), c_0_74]), c_0_47])).
% 0.19/0.42  cnf(c_0_92, negated_conjecture, (k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk5_0)!=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_90])])).
% 0.19/0.42  cnf(c_0_93, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_72]), c_0_73]), c_0_36]), c_0_27]), c_0_79])]), c_0_92]), ['proof']).
% 0.19/0.42  # SZS output end CNFRefutation
% 0.19/0.42  # Proof object total steps             : 94
% 0.19/0.42  # Proof object clause steps            : 64
% 0.19/0.42  # Proof object formula steps           : 30
% 0.19/0.42  # Proof object conjectures             : 44
% 0.19/0.42  # Proof object clause conjectures      : 41
% 0.19/0.42  # Proof object formula conjectures     : 3
% 0.19/0.42  # Proof object initial clauses used    : 31
% 0.19/0.42  # Proof object initial formulas used   : 15
% 0.19/0.42  # Proof object generating inferences   : 25
% 0.19/0.42  # Proof object simplifying inferences  : 73
% 0.19/0.42  # Training examples: 0 positive, 0 negative
% 0.19/0.42  # Parsed axioms                        : 15
% 0.19/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.42  # Initial clauses                      : 38
% 0.19/0.42  # Removed in clause preprocessing      : 1
% 0.19/0.42  # Initial clauses in saturation        : 37
% 0.19/0.42  # Processed clauses                    : 513
% 0.19/0.42  # ...of these trivial                  : 6
% 0.19/0.42  # ...subsumed                          : 196
% 0.19/0.42  # ...remaining for further processing  : 311
% 0.19/0.42  # Other redundant clauses eliminated   : 4
% 0.19/0.42  # Clauses deleted for lack of memory   : 0
% 0.19/0.42  # Backward-subsumed                    : 5
% 0.19/0.42  # Backward-rewritten                   : 38
% 0.19/0.42  # Generated clauses                    : 648
% 0.19/0.42  # ...of the previous two non-trivial   : 591
% 0.19/0.42  # Contextual simplify-reflections      : 6
% 0.19/0.42  # Paramodulations                      : 639
% 0.19/0.42  # Factorizations                       : 0
% 0.19/0.42  # Equation resolutions                 : 10
% 0.19/0.42  # Propositional unsat checks           : 0
% 0.19/0.42  #    Propositional check models        : 0
% 0.19/0.42  #    Propositional check unsatisfiable : 0
% 0.19/0.42  #    Propositional clauses             : 0
% 0.19/0.42  #    Propositional clauses after purity: 0
% 0.19/0.42  #    Propositional unsat core size     : 0
% 0.19/0.42  #    Propositional preprocessing time  : 0.000
% 0.19/0.42  #    Propositional encoding time       : 0.000
% 0.19/0.42  #    Propositional solver time         : 0.000
% 0.19/0.42  #    Success case prop preproc time    : 0.000
% 0.19/0.42  #    Success case prop encoding time   : 0.000
% 0.19/0.42  #    Success case prop solver time     : 0.000
% 0.19/0.42  # Current number of processed clauses  : 228
% 0.19/0.42  #    Positive orientable unit clauses  : 75
% 0.19/0.42  #    Positive unorientable unit clauses: 2
% 0.19/0.42  #    Negative unit clauses             : 5
% 0.19/0.42  #    Non-unit-clauses                  : 146
% 0.19/0.42  # Current number of unprocessed clauses: 127
% 0.19/0.42  # ...number of literals in the above   : 1103
% 0.19/0.42  # Current number of archived formulas  : 0
% 0.19/0.42  # Current number of archived clauses   : 81
% 0.19/0.42  # Clause-clause subsumption calls (NU) : 14585
% 0.19/0.42  # Rec. Clause-clause subsumption calls : 2614
% 0.19/0.42  # Non-unit clause-clause subsumptions  : 161
% 0.19/0.42  # Unit Clause-clause subsumption calls : 964
% 0.19/0.42  # Rewrite failures with RHS unbound    : 0
% 0.19/0.42  # BW rewrite match attempts            : 131
% 0.19/0.42  # BW rewrite match successes           : 29
% 0.19/0.42  # Condensation attempts                : 0
% 0.19/0.42  # Condensation successes               : 0
% 0.19/0.42  # Termbank termtop insertions          : 34642
% 0.19/0.42  
% 0.19/0.42  # -------------------------------------------------
% 0.19/0.42  # User time                : 0.072 s
% 0.19/0.42  # System time              : 0.007 s
% 0.19/0.42  # Total time               : 0.079 s
% 0.19/0.42  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
