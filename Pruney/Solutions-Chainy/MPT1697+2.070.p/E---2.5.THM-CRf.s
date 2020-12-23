%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:44 EST 2020

% Result     : Theorem 0.37s
% Output     : CNFRefutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 578 expanded)
%              Number of clauses        :   63 ( 237 expanded)
%              Number of leaves         :   16 ( 143 expanded)
%              Depth                    :   12
%              Number of atoms          :  490 (4396 expanded)
%              Number of equality atoms :   87 ( 780 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal clause size      :   55 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

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

fof(t207_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_xboole_0(X1,X2)
       => k7_relat_1(k7_relat_1(X3,X1),X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(redefinition_r1_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2) )
     => ( r1_subset_1(X1,X2)
      <=> r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

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

fof(c_0_16,plain,(
    ! [X20,X21] :
      ( ( r1_tarski(X20,X21)
        | X20 != X21 )
      & ( r1_tarski(X21,X20)
        | X20 != X21 )
      & ( ~ r1_tarski(X20,X21)
        | ~ r1_tarski(X21,X20)
        | X20 = X21 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_17,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v1_xboole_0(X8)
        | ~ r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_1(X10),X10)
        | v1_xboole_0(X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_18,plain,(
    ! [X14,X15,X17,X18,X19] :
      ( ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_xboole_0(X14,X15) )
      & ( r2_hidden(esk2_2(X14,X15),X15)
        | r1_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X19,X17)
        | ~ r2_hidden(X19,X18)
        | ~ r1_xboole_0(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_19,plain,(
    ! [X27,X28] :
      ( ( ~ v4_relat_1(X28,X27)
        | r1_tarski(k1_relat_1(X28),X27)
        | ~ v1_relat_1(X28) )
      & ( ~ r1_tarski(k1_relat_1(X28),X27)
        | v4_relat_1(X28,X27)
        | ~ v1_relat_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,negated_conjecture,(
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

fof(c_0_22,plain,(
    ! [X29,X30,X31] :
      ( ~ v1_relat_1(X31)
      | ~ r1_xboole_0(X29,X30)
      | k7_relat_1(k7_relat_1(X31,X29),X30) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t207_relat_1])])).

cnf(c_0_23,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X33)
      | ~ v4_relat_1(X33,X32)
      | X33 = k7_relat_1(X33,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_26,plain,
    ( v4_relat_1(X1,X2)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_20])).

fof(c_0_28,plain,(
    ! [X34,X35] :
      ( ( ~ r1_subset_1(X34,X35)
        | r1_xboole_0(X34,X35)
        | v1_xboole_0(X34)
        | v1_xboole_0(X35) )
      & ( ~ r1_xboole_0(X34,X35)
        | r1_subset_1(X34,X35)
        | v1_xboole_0(X34)
        | v1_xboole_0(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).

fof(c_0_29,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).

cnf(c_0_30,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( r1_xboole_0(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( v4_relat_1(X1,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_34,plain,(
    ! [X39,X40,X41,X42] :
      ( ~ v1_funct_1(X41)
      | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
      | k2_partfun1(X39,X40,X41,X42) = k7_relat_1(X41,X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

fof(c_0_35,plain,(
    ! [X36,X37,X38] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | v1_relat_1(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_36,plain,(
    ! [X25,X26] :
      ( ( ~ m1_subset_1(X25,k1_zfmisc_1(X26))
        | r1_tarski(X25,X26) )
      & ( ~ r1_tarski(X25,X26)
        | m1_subset_1(X25,k1_zfmisc_1(X26)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_37,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(X22))
      | k9_subset_1(X22,X23,X24) = k3_xboole_0(X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_38,plain,(
    ! [X12,X13] :
      ( ( ~ r1_xboole_0(X12,X13)
        | k3_xboole_0(X12,X13) = k1_xboole_0 )
      & ( k3_xboole_0(X12,X13) != k1_xboole_0
        | r1_xboole_0(X12,X13) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_39,plain,
    ( r1_xboole_0(X1,X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,negated_conjecture,
    ( r1_subset_1(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_43,plain,(
    ! [X43,X44,X45,X46,X47,X48,X49] :
      ( ( k2_partfun1(k4_subset_1(X43,X45,X46),X44,X49,X45) = X47
        | X49 != k1_tmap_1(X43,X44,X45,X46,X47,X48)
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,k4_subset_1(X43,X45,X46),X44)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X43,X45,X46),X44)))
        | k2_partfun1(X45,X44,X47,k9_subset_1(X43,X45,X46)) != k2_partfun1(X46,X44,X48,k9_subset_1(X43,X45,X46))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,X46,X44)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X44)))
        | ~ v1_funct_1(X47)
        | ~ v1_funct_2(X47,X45,X44)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X44)))
        | v1_xboole_0(X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(X43))
        | v1_xboole_0(X45)
        | ~ m1_subset_1(X45,k1_zfmisc_1(X43))
        | v1_xboole_0(X44)
        | v1_xboole_0(X43) )
      & ( k2_partfun1(k4_subset_1(X43,X45,X46),X44,X49,X46) = X48
        | X49 != k1_tmap_1(X43,X44,X45,X46,X47,X48)
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,k4_subset_1(X43,X45,X46),X44)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X43,X45,X46),X44)))
        | k2_partfun1(X45,X44,X47,k9_subset_1(X43,X45,X46)) != k2_partfun1(X46,X44,X48,k9_subset_1(X43,X45,X46))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,X46,X44)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X44)))
        | ~ v1_funct_1(X47)
        | ~ v1_funct_2(X47,X45,X44)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X44)))
        | v1_xboole_0(X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(X43))
        | v1_xboole_0(X45)
        | ~ m1_subset_1(X45,k1_zfmisc_1(X43))
        | v1_xboole_0(X44)
        | v1_xboole_0(X43) )
      & ( k2_partfun1(k4_subset_1(X43,X45,X46),X44,X49,X45) != X47
        | k2_partfun1(k4_subset_1(X43,X45,X46),X44,X49,X46) != X48
        | X49 = k1_tmap_1(X43,X44,X45,X46,X47,X48)
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,k4_subset_1(X43,X45,X46),X44)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X43,X45,X46),X44)))
        | k2_partfun1(X45,X44,X47,k9_subset_1(X43,X45,X46)) != k2_partfun1(X46,X44,X48,k9_subset_1(X43,X45,X46))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,X46,X44)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X44)))
        | ~ v1_funct_1(X47)
        | ~ v1_funct_2(X47,X45,X44)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X44)))
        | v1_xboole_0(X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(X43))
        | v1_xboole_0(X45)
        | ~ m1_subset_1(X45,k1_zfmisc_1(X43))
        | v1_xboole_0(X44)
        | v1_xboole_0(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tmap_1])])])])])).

fof(c_0_44,plain,(
    ! [X50,X51,X52,X53,X54,X55] :
      ( ( v1_funct_1(k1_tmap_1(X50,X51,X52,X53,X54,X55))
        | v1_xboole_0(X50)
        | v1_xboole_0(X51)
        | v1_xboole_0(X52)
        | ~ m1_subset_1(X52,k1_zfmisc_1(X50))
        | v1_xboole_0(X53)
        | ~ m1_subset_1(X53,k1_zfmisc_1(X50))
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X52,X51)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X51)))
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,X53,X51)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X51))) )
      & ( v1_funct_2(k1_tmap_1(X50,X51,X52,X53,X54,X55),k4_subset_1(X50,X52,X53),X51)
        | v1_xboole_0(X50)
        | v1_xboole_0(X51)
        | v1_xboole_0(X52)
        | ~ m1_subset_1(X52,k1_zfmisc_1(X50))
        | v1_xboole_0(X53)
        | ~ m1_subset_1(X53,k1_zfmisc_1(X50))
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X52,X51)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X51)))
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,X53,X51)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X51))) )
      & ( m1_subset_1(k1_tmap_1(X50,X51,X52,X53,X54,X55),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X50,X52,X53),X51)))
        | v1_xboole_0(X50)
        | v1_xboole_0(X51)
        | v1_xboole_0(X52)
        | ~ m1_subset_1(X52,k1_zfmisc_1(X50))
        | v1_xboole_0(X53)
        | ~ m1_subset_1(X53,k1_zfmisc_1(X50))
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X52,X51)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X51)))
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,X53,X51)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X51))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tmap_1])])])])).

cnf(c_0_45,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_46,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_47,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_49,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_50,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_51,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_52,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_54,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_55,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_42])).

cnf(c_0_56,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_57,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_58,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_59,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_60,plain,
    ( k7_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_61,negated_conjecture,
    ( k7_relat_1(esk8_0,X1) = k2_partfun1(esk6_0,esk4_0,esk8_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])])).

cnf(c_0_62,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_48])).

cnf(c_0_63,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_27])).

cnf(c_0_64,negated_conjecture,
    ( k2_partfun1(esk5_0,esk4_0,esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0)) != k2_partfun1(esk6_0,esk4_0,esk8_0,k9_subset_1(esk3_0,esk5_0,esk6_0))
    | k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk5_0) != esk7_0
    | k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk6_0) != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_65,negated_conjecture,
    ( k9_subset_1(esk3_0,X1,esk6_0) = k3_xboole_0(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_66,negated_conjecture,
    ( k3_xboole_0(esk5_0,esk6_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_68,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_69,plain,
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
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_56]),c_0_57]),c_0_58]),c_0_59])).

cnf(c_0_70,negated_conjecture,
    ( k2_partfun1(esk6_0,esk4_0,esk8_0,X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])])).

cnf(c_0_71,negated_conjecture,
    ( v1_funct_2(esk8_0,esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_72,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_73,plain,
    ( k3_xboole_0(X1,X2) = k9_subset_1(X2,X1,X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_63])).

cnf(c_0_74,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_75,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk5_0) != esk7_0
    | k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk6_0) != esk8_0
    | k2_partfun1(esk6_0,esk4_0,esk8_0,k1_xboole_0) != k2_partfun1(esk5_0,esk4_0,esk7_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_65]),c_0_66]),c_0_65]),c_0_66])).

cnf(c_0_76,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_77,negated_conjecture,
    ( k7_relat_1(esk7_0,X1) = k2_partfun1(esk5_0,esk4_0,esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_67]),c_0_68])])).

cnf(c_0_78,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_67])).

cnf(c_0_79,negated_conjecture,
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
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71]),c_0_49]),c_0_48])]),c_0_41]),c_0_72])).

cnf(c_0_80,negated_conjecture,
    ( k9_subset_1(esk3_0,X1,esk6_0) = k9_subset_1(esk6_0,X1,esk6_0) ),
    inference(rw,[status(thm)],[c_0_65,c_0_73])).

cnf(c_0_81,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_82,plain,
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
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_74]),c_0_57]),c_0_58]),c_0_59])).

cnf(c_0_83,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk5_0) != esk7_0
    | k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk6_0) != esk8_0
    | k2_partfun1(esk5_0,esk4_0,esk7_0,k1_xboole_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_70]),c_0_76])])).

cnf(c_0_84,negated_conjecture,
    ( k2_partfun1(esk5_0,esk4_0,esk7_0,X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_77]),c_0_78])])).

cnf(c_0_85,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk3_0,X1,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,X1,esk6_0,X2,esk8_0),esk6_0) = esk8_0
    | v1_xboole_0(X1)
    | k2_partfun1(X1,esk4_0,X2,k9_subset_1(esk6_0,X1,esk6_0)) != k1_xboole_0
    | ~ v1_funct_2(X2,X1,esk4_0)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0))
    | ~ v1_xboole_0(k9_subset_1(esk6_0,X1,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_53])]),c_0_81])).

cnf(c_0_86,negated_conjecture,
    ( v1_funct_2(esk7_0,esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_88,negated_conjecture,
    ( k9_subset_1(esk6_0,esk5_0,esk6_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_66,c_0_73])).

cnf(c_0_89,negated_conjecture,
    ( k2_partfun1(k4_subset_1(X1,X2,esk6_0),esk4_0,k1_tmap_1(X1,esk4_0,X2,esk6_0,X3,esk8_0),X2) = X3
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(X2,esk4_0,X3,k9_subset_1(X1,X2,esk6_0)) != k1_xboole_0
    | ~ v1_funct_2(X3,X2,esk4_0)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,esk4_0)))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(k9_subset_1(X1,X2,esk6_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_70]),c_0_71]),c_0_49]),c_0_48])]),c_0_41]),c_0_72])).

cnf(c_0_90,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk5_0) != esk7_0
    | k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk6_0) != esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_76])])).

cnf(c_0_91,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk6_0) = esk8_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_84]),c_0_86]),c_0_68]),c_0_67]),c_0_87]),c_0_88]),c_0_76])]),c_0_42])).

cnf(c_0_92,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk3_0,X1,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,X1,esk6_0,X2,esk8_0),X1) = X2
    | v1_xboole_0(X1)
    | k2_partfun1(X1,esk4_0,X2,k9_subset_1(esk6_0,X1,esk6_0)) != k1_xboole_0
    | ~ v1_funct_2(X2,X1,esk4_0)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0))
    | ~ v1_xboole_0(k9_subset_1(esk6_0,X1,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_80]),c_0_53])]),c_0_81])).

cnf(c_0_93,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk5_0) != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_91])])).

cnf(c_0_94,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_84]),c_0_86]),c_0_68]),c_0_67]),c_0_87]),c_0_88]),c_0_76])]),c_0_93]),c_0_42]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:01:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.37/0.55  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.37/0.55  # and selection function SelectCQIPrecWNTNp.
% 0.37/0.55  #
% 0.37/0.55  # Preprocessing time       : 0.029 s
% 0.37/0.55  # Presaturation interreduction done
% 0.37/0.55  
% 0.37/0.55  # Proof found!
% 0.37/0.55  # SZS status Theorem
% 0.37/0.55  # SZS output start CNFRefutation
% 0.37/0.55  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.37/0.55  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.37/0.55  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.37/0.55  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.37/0.55  fof(t6_tmap_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>(r1_subset_1(X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3)=X5)&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4)=X6)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 0.37/0.55  fof(t207_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_xboole_0(X1,X2)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 0.37/0.55  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 0.37/0.55  fof(redefinition_r1_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))=>(r1_subset_1(X1,X2)<=>r1_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 0.37/0.55  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 0.37/0.55  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.37/0.55  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.37/0.55  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.37/0.55  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.37/0.55  fof(d1_tmap_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>(k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))=>![X7]:(((v1_funct_1(X7)&v1_funct_2(X7,k4_subset_1(X1,X3,X4),X2))&m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))))=>(X7=k1_tmap_1(X1,X2,X3,X4,X5,X6)<=>(k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X3)=X5&k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X4)=X6)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 0.37/0.55  fof(dt_k1_tmap_1, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((((((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))&~(v1_xboole_0(X3)))&m1_subset_1(X3,k1_zfmisc_1(X1)))&~(v1_xboole_0(X4)))&m1_subset_1(X4,k1_zfmisc_1(X1)))&v1_funct_1(X5))&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2))&m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 0.37/0.55  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.37/0.55  fof(c_0_16, plain, ![X20, X21]:(((r1_tarski(X20,X21)|X20!=X21)&(r1_tarski(X21,X20)|X20!=X21))&(~r1_tarski(X20,X21)|~r1_tarski(X21,X20)|X20=X21)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.37/0.55  fof(c_0_17, plain, ![X8, X9, X10]:((~v1_xboole_0(X8)|~r2_hidden(X9,X8))&(r2_hidden(esk1_1(X10),X10)|v1_xboole_0(X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.37/0.55  fof(c_0_18, plain, ![X14, X15, X17, X18, X19]:(((r2_hidden(esk2_2(X14,X15),X14)|r1_xboole_0(X14,X15))&(r2_hidden(esk2_2(X14,X15),X15)|r1_xboole_0(X14,X15)))&(~r2_hidden(X19,X17)|~r2_hidden(X19,X18)|~r1_xboole_0(X17,X18))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.37/0.55  fof(c_0_19, plain, ![X27, X28]:((~v4_relat_1(X28,X27)|r1_tarski(k1_relat_1(X28),X27)|~v1_relat_1(X28))&(~r1_tarski(k1_relat_1(X28),X27)|v4_relat_1(X28,X27)|~v1_relat_1(X28))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.37/0.55  cnf(c_0_20, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.37/0.55  fof(c_0_21, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>(r1_subset_1(X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3)=X5)&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4)=X6))))))))), inference(assume_negation,[status(cth)],[t6_tmap_1])).
% 0.37/0.55  fof(c_0_22, plain, ![X29, X30, X31]:(~v1_relat_1(X31)|(~r1_xboole_0(X29,X30)|k7_relat_1(k7_relat_1(X31,X29),X30)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t207_relat_1])])).
% 0.37/0.55  cnf(c_0_23, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.37/0.55  cnf(c_0_24, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.37/0.55  fof(c_0_25, plain, ![X32, X33]:(~v1_relat_1(X33)|~v4_relat_1(X33,X32)|X33=k7_relat_1(X33,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.37/0.55  cnf(c_0_26, plain, (v4_relat_1(X1,X2)|~r1_tarski(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.37/0.55  cnf(c_0_27, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_20])).
% 0.37/0.55  fof(c_0_28, plain, ![X34, X35]:((~r1_subset_1(X34,X35)|r1_xboole_0(X34,X35)|(v1_xboole_0(X34)|v1_xboole_0(X35)))&(~r1_xboole_0(X34,X35)|r1_subset_1(X34,X35)|(v1_xboole_0(X34)|v1_xboole_0(X35)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).
% 0.37/0.55  fof(c_0_29, negated_conjecture, (~v1_xboole_0(esk3_0)&(~v1_xboole_0(esk4_0)&((~v1_xboole_0(esk5_0)&m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0)))&((~v1_xboole_0(esk6_0)&m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0)))&(r1_subset_1(esk5_0,esk6_0)&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk5_0,esk4_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0))))&(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk6_0,esk4_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk4_0))))&(k2_partfun1(esk5_0,esk4_0,esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0))!=k2_partfun1(esk6_0,esk4_0,esk8_0,k9_subset_1(esk3_0,esk5_0,esk6_0))|k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk5_0)!=esk7_0|k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk6_0)!=esk8_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).
% 0.37/0.55  cnf(c_0_30, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.37/0.55  cnf(c_0_31, plain, (r1_xboole_0(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.37/0.55  cnf(c_0_32, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.37/0.55  cnf(c_0_33, plain, (v4_relat_1(X1,k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.37/0.55  fof(c_0_34, plain, ![X39, X40, X41, X42]:(~v1_funct_1(X41)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|k2_partfun1(X39,X40,X41,X42)=k7_relat_1(X41,X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 0.37/0.55  fof(c_0_35, plain, ![X36, X37, X38]:(~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))|v1_relat_1(X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.37/0.55  fof(c_0_36, plain, ![X25, X26]:((~m1_subset_1(X25,k1_zfmisc_1(X26))|r1_tarski(X25,X26))&(~r1_tarski(X25,X26)|m1_subset_1(X25,k1_zfmisc_1(X26)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.37/0.55  fof(c_0_37, plain, ![X22, X23, X24]:(~m1_subset_1(X24,k1_zfmisc_1(X22))|k9_subset_1(X22,X23,X24)=k3_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.37/0.55  fof(c_0_38, plain, ![X12, X13]:((~r1_xboole_0(X12,X13)|k3_xboole_0(X12,X13)=k1_xboole_0)&(k3_xboole_0(X12,X13)!=k1_xboole_0|r1_xboole_0(X12,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.37/0.55  cnf(c_0_39, plain, (r1_xboole_0(X1,X2)|v1_xboole_0(X1)|v1_xboole_0(X2)|~r1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.37/0.55  cnf(c_0_40, negated_conjecture, (r1_subset_1(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.37/0.55  cnf(c_0_41, negated_conjecture, (~v1_xboole_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.37/0.55  cnf(c_0_42, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.37/0.55  fof(c_0_43, plain, ![X43, X44, X45, X46, X47, X48, X49]:(((k2_partfun1(k4_subset_1(X43,X45,X46),X44,X49,X45)=X47|X49!=k1_tmap_1(X43,X44,X45,X46,X47,X48)|(~v1_funct_1(X49)|~v1_funct_2(X49,k4_subset_1(X43,X45,X46),X44)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X43,X45,X46),X44))))|k2_partfun1(X45,X44,X47,k9_subset_1(X43,X45,X46))!=k2_partfun1(X46,X44,X48,k9_subset_1(X43,X45,X46))|(~v1_funct_1(X48)|~v1_funct_2(X48,X46,X44)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X44))))|(~v1_funct_1(X47)|~v1_funct_2(X47,X45,X44)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X44))))|(v1_xboole_0(X46)|~m1_subset_1(X46,k1_zfmisc_1(X43)))|(v1_xboole_0(X45)|~m1_subset_1(X45,k1_zfmisc_1(X43)))|v1_xboole_0(X44)|v1_xboole_0(X43))&(k2_partfun1(k4_subset_1(X43,X45,X46),X44,X49,X46)=X48|X49!=k1_tmap_1(X43,X44,X45,X46,X47,X48)|(~v1_funct_1(X49)|~v1_funct_2(X49,k4_subset_1(X43,X45,X46),X44)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X43,X45,X46),X44))))|k2_partfun1(X45,X44,X47,k9_subset_1(X43,X45,X46))!=k2_partfun1(X46,X44,X48,k9_subset_1(X43,X45,X46))|(~v1_funct_1(X48)|~v1_funct_2(X48,X46,X44)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X44))))|(~v1_funct_1(X47)|~v1_funct_2(X47,X45,X44)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X44))))|(v1_xboole_0(X46)|~m1_subset_1(X46,k1_zfmisc_1(X43)))|(v1_xboole_0(X45)|~m1_subset_1(X45,k1_zfmisc_1(X43)))|v1_xboole_0(X44)|v1_xboole_0(X43)))&(k2_partfun1(k4_subset_1(X43,X45,X46),X44,X49,X45)!=X47|k2_partfun1(k4_subset_1(X43,X45,X46),X44,X49,X46)!=X48|X49=k1_tmap_1(X43,X44,X45,X46,X47,X48)|(~v1_funct_1(X49)|~v1_funct_2(X49,k4_subset_1(X43,X45,X46),X44)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X43,X45,X46),X44))))|k2_partfun1(X45,X44,X47,k9_subset_1(X43,X45,X46))!=k2_partfun1(X46,X44,X48,k9_subset_1(X43,X45,X46))|(~v1_funct_1(X48)|~v1_funct_2(X48,X46,X44)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X44))))|(~v1_funct_1(X47)|~v1_funct_2(X47,X45,X44)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X44))))|(v1_xboole_0(X46)|~m1_subset_1(X46,k1_zfmisc_1(X43)))|(v1_xboole_0(X45)|~m1_subset_1(X45,k1_zfmisc_1(X43)))|v1_xboole_0(X44)|v1_xboole_0(X43))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tmap_1])])])])])).
% 0.37/0.55  fof(c_0_44, plain, ![X50, X51, X52, X53, X54, X55]:(((v1_funct_1(k1_tmap_1(X50,X51,X52,X53,X54,X55))|(v1_xboole_0(X50)|v1_xboole_0(X51)|v1_xboole_0(X52)|~m1_subset_1(X52,k1_zfmisc_1(X50))|v1_xboole_0(X53)|~m1_subset_1(X53,k1_zfmisc_1(X50))|~v1_funct_1(X54)|~v1_funct_2(X54,X52,X51)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X51)))|~v1_funct_1(X55)|~v1_funct_2(X55,X53,X51)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X51)))))&(v1_funct_2(k1_tmap_1(X50,X51,X52,X53,X54,X55),k4_subset_1(X50,X52,X53),X51)|(v1_xboole_0(X50)|v1_xboole_0(X51)|v1_xboole_0(X52)|~m1_subset_1(X52,k1_zfmisc_1(X50))|v1_xboole_0(X53)|~m1_subset_1(X53,k1_zfmisc_1(X50))|~v1_funct_1(X54)|~v1_funct_2(X54,X52,X51)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X51)))|~v1_funct_1(X55)|~v1_funct_2(X55,X53,X51)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X51))))))&(m1_subset_1(k1_tmap_1(X50,X51,X52,X53,X54,X55),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X50,X52,X53),X51)))|(v1_xboole_0(X50)|v1_xboole_0(X51)|v1_xboole_0(X52)|~m1_subset_1(X52,k1_zfmisc_1(X50))|v1_xboole_0(X53)|~m1_subset_1(X53,k1_zfmisc_1(X50))|~v1_funct_1(X54)|~v1_funct_2(X54,X52,X51)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X51)))|~v1_funct_1(X55)|~v1_funct_2(X55,X53,X51)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X51)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tmap_1])])])])).
% 0.37/0.55  cnf(c_0_45, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k1_xboole_0|~v1_relat_1(X1)|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.37/0.55  cnf(c_0_46, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.37/0.55  cnf(c_0_47, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.37/0.55  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.37/0.55  cnf(c_0_49, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.37/0.55  cnf(c_0_50, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.37/0.55  cnf(c_0_51, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.37/0.55  cnf(c_0_52, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.37/0.55  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.37/0.55  cnf(c_0_54, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.37/0.55  cnf(c_0_55, negated_conjecture, (r1_xboole_0(esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_42])).
% 0.37/0.55  cnf(c_0_56, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X3)=X6|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X4)|v1_xboole_0(X1)|X5!=k1_tmap_1(X1,X4,X2,X3,X7,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|k2_partfun1(X2,X4,X7,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_1(X6)|~v1_funct_2(X6,X3,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X7)|~v1_funct_2(X7,X2,X4)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.37/0.55  cnf(c_0_57, plain, (m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2)))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.37/0.55  cnf(c_0_58, plain, (v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.37/0.55  cnf(c_0_59, plain, (v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.37/0.55  cnf(c_0_60, plain, (k7_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.37/0.55  cnf(c_0_61, negated_conjecture, (k7_relat_1(esk8_0,X1)=k2_partfun1(esk6_0,esk4_0,esk8_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])])).
% 0.37/0.55  cnf(c_0_62, negated_conjecture, (v1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_50, c_0_48])).
% 0.37/0.55  cnf(c_0_63, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_51, c_0_27])).
% 0.37/0.55  cnf(c_0_64, negated_conjecture, (k2_partfun1(esk5_0,esk4_0,esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0))!=k2_partfun1(esk6_0,esk4_0,esk8_0,k9_subset_1(esk3_0,esk5_0,esk6_0))|k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk5_0)!=esk7_0|k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk6_0)!=esk8_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.37/0.55  cnf(c_0_65, negated_conjecture, (k9_subset_1(esk3_0,X1,esk6_0)=k3_xboole_0(X1,esk6_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.37/0.55  cnf(c_0_66, negated_conjecture, (k3_xboole_0(esk5_0,esk6_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.37/0.55  cnf(c_0_67, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.37/0.55  cnf(c_0_68, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.37/0.55  cnf(c_0_69, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X3)=X6|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_2(X5,X2,X4)|~v1_funct_2(X6,X3,X4)|~v1_funct_1(X5)|~v1_funct_1(X6)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_56]), c_0_57]), c_0_58]), c_0_59])).
% 0.37/0.55  cnf(c_0_70, negated_conjecture, (k2_partfun1(esk6_0,esk4_0,esk8_0,X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62])])).
% 0.37/0.55  cnf(c_0_71, negated_conjecture, (v1_funct_2(esk8_0,esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.37/0.55  cnf(c_0_72, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.37/0.55  cnf(c_0_73, plain, (k3_xboole_0(X1,X2)=k9_subset_1(X2,X1,X2)), inference(spm,[status(thm)],[c_0_52, c_0_63])).
% 0.37/0.55  cnf(c_0_74, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X2)=X6|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X4)|v1_xboole_0(X1)|X5!=k1_tmap_1(X1,X4,X2,X3,X6,X7)|~v1_funct_1(X5)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|k2_partfun1(X2,X4,X6,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X7,k9_subset_1(X1,X2,X3))|~v1_funct_1(X7)|~v1_funct_2(X7,X3,X4)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X6)|~v1_funct_2(X6,X2,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.37/0.55  cnf(c_0_75, negated_conjecture, (k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk5_0)!=esk7_0|k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk6_0)!=esk8_0|k2_partfun1(esk6_0,esk4_0,esk8_0,k1_xboole_0)!=k2_partfun1(esk5_0,esk4_0,esk7_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_65]), c_0_66]), c_0_65]), c_0_66])).
% 0.37/0.55  cnf(c_0_76, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.37/0.55  cnf(c_0_77, negated_conjecture, (k7_relat_1(esk7_0,X1)=k2_partfun1(esk5_0,esk4_0,esk7_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_67]), c_0_68])])).
% 0.37/0.55  cnf(c_0_78, negated_conjecture, (v1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_50, c_0_67])).
% 0.37/0.55  cnf(c_0_79, negated_conjecture, (k2_partfun1(k4_subset_1(X1,X2,esk6_0),esk4_0,k1_tmap_1(X1,esk4_0,X2,esk6_0,X3,esk8_0),esk6_0)=esk8_0|v1_xboole_0(X2)|v1_xboole_0(X1)|k2_partfun1(X2,esk4_0,X3,k9_subset_1(X1,X2,esk6_0))!=k1_xboole_0|~v1_funct_2(X3,X2,esk4_0)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,esk4_0)))|~m1_subset_1(esk6_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_xboole_0(k9_subset_1(X1,X2,esk6_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71]), c_0_49]), c_0_48])]), c_0_41]), c_0_72])).
% 0.37/0.55  cnf(c_0_80, negated_conjecture, (k9_subset_1(esk3_0,X1,esk6_0)=k9_subset_1(esk6_0,X1,esk6_0)), inference(rw,[status(thm)],[c_0_65, c_0_73])).
% 0.37/0.55  cnf(c_0_81, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.37/0.55  cnf(c_0_82, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X2)=X5|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_2(X6,X3,X4)|~v1_funct_2(X5,X2,X4)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_74]), c_0_57]), c_0_58]), c_0_59])).
% 0.37/0.55  cnf(c_0_83, negated_conjecture, (k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk5_0)!=esk7_0|k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk6_0)!=esk8_0|k2_partfun1(esk5_0,esk4_0,esk7_0,k1_xboole_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_70]), c_0_76])])).
% 0.37/0.55  cnf(c_0_84, negated_conjecture, (k2_partfun1(esk5_0,esk4_0,esk7_0,X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_77]), c_0_78])])).
% 0.37/0.55  cnf(c_0_85, negated_conjecture, (k2_partfun1(k4_subset_1(esk3_0,X1,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,X1,esk6_0,X2,esk8_0),esk6_0)=esk8_0|v1_xboole_0(X1)|k2_partfun1(X1,esk4_0,X2,k9_subset_1(esk6_0,X1,esk6_0))!=k1_xboole_0|~v1_funct_2(X2,X1,esk4_0)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk4_0)))|~m1_subset_1(X1,k1_zfmisc_1(esk3_0))|~v1_xboole_0(k9_subset_1(esk6_0,X1,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_53])]), c_0_81])).
% 0.37/0.55  cnf(c_0_86, negated_conjecture, (v1_funct_2(esk7_0,esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.37/0.55  cnf(c_0_87, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.37/0.55  cnf(c_0_88, negated_conjecture, (k9_subset_1(esk6_0,esk5_0,esk6_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_66, c_0_73])).
% 0.37/0.55  cnf(c_0_89, negated_conjecture, (k2_partfun1(k4_subset_1(X1,X2,esk6_0),esk4_0,k1_tmap_1(X1,esk4_0,X2,esk6_0,X3,esk8_0),X2)=X3|v1_xboole_0(X2)|v1_xboole_0(X1)|k2_partfun1(X2,esk4_0,X3,k9_subset_1(X1,X2,esk6_0))!=k1_xboole_0|~v1_funct_2(X3,X2,esk4_0)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,esk4_0)))|~m1_subset_1(esk6_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_xboole_0(k9_subset_1(X1,X2,esk6_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_70]), c_0_71]), c_0_49]), c_0_48])]), c_0_41]), c_0_72])).
% 0.37/0.55  cnf(c_0_90, negated_conjecture, (k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk5_0)!=esk7_0|k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk6_0)!=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_76])])).
% 0.37/0.55  cnf(c_0_91, negated_conjecture, (k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk6_0)=esk8_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_84]), c_0_86]), c_0_68]), c_0_67]), c_0_87]), c_0_88]), c_0_76])]), c_0_42])).
% 0.37/0.55  cnf(c_0_92, negated_conjecture, (k2_partfun1(k4_subset_1(esk3_0,X1,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,X1,esk6_0,X2,esk8_0),X1)=X2|v1_xboole_0(X1)|k2_partfun1(X1,esk4_0,X2,k9_subset_1(esk6_0,X1,esk6_0))!=k1_xboole_0|~v1_funct_2(X2,X1,esk4_0)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk4_0)))|~m1_subset_1(X1,k1_zfmisc_1(esk3_0))|~v1_xboole_0(k9_subset_1(esk6_0,X1,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_80]), c_0_53])]), c_0_81])).
% 0.37/0.55  cnf(c_0_93, negated_conjecture, (k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk5_0)!=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_91])])).
% 0.37/0.55  cnf(c_0_94, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_84]), c_0_86]), c_0_68]), c_0_67]), c_0_87]), c_0_88]), c_0_76])]), c_0_93]), c_0_42]), ['proof']).
% 0.37/0.55  # SZS output end CNFRefutation
% 0.37/0.55  # Proof object total steps             : 95
% 0.37/0.55  # Proof object clause steps            : 63
% 0.37/0.55  # Proof object formula steps           : 32
% 0.37/0.55  # Proof object conjectures             : 38
% 0.37/0.55  # Proof object clause conjectures      : 35
% 0.37/0.55  # Proof object formula conjectures     : 3
% 0.37/0.55  # Proof object initial clauses used    : 32
% 0.37/0.55  # Proof object initial formulas used   : 16
% 0.37/0.55  # Proof object generating inferences   : 24
% 0.37/0.55  # Proof object simplifying inferences  : 66
% 0.37/0.55  # Training examples: 0 positive, 0 negative
% 0.37/0.55  # Parsed axioms                        : 16
% 0.37/0.55  # Removed by relevancy pruning/SinE    : 0
% 0.37/0.55  # Initial clauses                      : 42
% 0.37/0.55  # Removed in clause preprocessing      : 0
% 0.37/0.55  # Initial clauses in saturation        : 42
% 0.37/0.55  # Processed clauses                    : 1865
% 0.37/0.55  # ...of these trivial                  : 3
% 0.37/0.55  # ...subsumed                          : 1164
% 0.37/0.55  # ...remaining for further processing  : 698
% 0.37/0.55  # Other redundant clauses eliminated   : 6
% 0.37/0.55  # Clauses deleted for lack of memory   : 0
% 0.37/0.55  # Backward-subsumed                    : 13
% 0.37/0.55  # Backward-rewritten                   : 28
% 0.37/0.55  # Generated clauses                    : 3537
% 0.37/0.55  # ...of the previous two non-trivial   : 2980
% 0.37/0.55  # Contextual simplify-reflections      : 6
% 0.37/0.55  # Paramodulations                      : 3504
% 0.37/0.55  # Factorizations                       : 0
% 0.37/0.55  # Equation resolutions                 : 34
% 0.37/0.55  # Propositional unsat checks           : 0
% 0.37/0.55  #    Propositional check models        : 0
% 0.37/0.55  #    Propositional check unsatisfiable : 0
% 0.37/0.55  #    Propositional clauses             : 0
% 0.37/0.55  #    Propositional clauses after purity: 0
% 0.37/0.55  #    Propositional unsat core size     : 0
% 0.37/0.55  #    Propositional preprocessing time  : 0.000
% 0.37/0.55  #    Propositional encoding time       : 0.000
% 0.37/0.55  #    Propositional solver time         : 0.000
% 0.37/0.55  #    Success case prop preproc time    : 0.000
% 0.37/0.55  #    Success case prop encoding time   : 0.000
% 0.37/0.55  #    Success case prop solver time     : 0.000
% 0.37/0.55  # Current number of processed clauses  : 611
% 0.37/0.55  #    Positive orientable unit clauses  : 99
% 0.37/0.55  #    Positive unorientable unit clauses: 0
% 0.37/0.55  #    Negative unit clauses             : 5
% 0.37/0.55  #    Non-unit-clauses                  : 507
% 0.37/0.55  # Current number of unprocessed clauses: 1135
% 0.37/0.55  # ...number of literals in the above   : 7341
% 0.37/0.55  # Current number of archived formulas  : 0
% 0.37/0.55  # Current number of archived clauses   : 82
% 0.37/0.55  # Clause-clause subsumption calls (NU) : 121676
% 0.37/0.55  # Rec. Clause-clause subsumption calls : 32942
% 0.37/0.55  # Non-unit clause-clause subsumptions  : 995
% 0.37/0.55  # Unit Clause-clause subsumption calls : 1924
% 0.37/0.55  # Rewrite failures with RHS unbound    : 0
% 0.37/0.55  # BW rewrite match attempts            : 136
% 0.37/0.55  # BW rewrite match successes           : 19
% 0.37/0.55  # Condensation attempts                : 0
% 0.37/0.55  # Condensation successes               : 0
% 0.37/0.55  # Termbank termtop insertions          : 158005
% 0.37/0.55  
% 0.37/0.55  # -------------------------------------------------
% 0.37/0.55  # User time                : 0.202 s
% 0.37/0.55  # System time              : 0.006 s
% 0.37/0.55  # Total time               : 0.208 s
% 0.37/0.55  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
