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
% DateTime   : Thu Dec  3 11:16:36 EST 2020

% Result     : Theorem 0.70s
% Output     : CNFRefutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 868 expanded)
%              Number of clauses        :   93 ( 349 expanded)
%              Number of leaves         :   20 ( 213 expanded)
%              Depth                    :   13
%              Number of atoms          :  603 (6604 expanded)
%              Number of equality atoms :  109 (1124 expanded)
%              Maximal formula depth    :   28 (   5 average)
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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(cc5_funct_2,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X2) )
           => ( v1_funct_1(X3)
              & v1_partfun1(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

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

fof(redefinition_r1_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2) )
     => ( r1_subset_1(X1,X2)
      <=> r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(t192_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k7_relat_1(X2,k3_xboole_0(k1_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

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

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

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

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_20,negated_conjecture,(
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

fof(c_0_21,plain,(
    ! [X10,X11,X13,X14,X15] :
      ( ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_2(X10,X11),X11)
        | r1_xboole_0(X10,X11) )
      & ( ~ r2_hidden(X15,X13)
        | ~ r2_hidden(X15,X14)
        | ~ r1_xboole_0(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_22,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(X16,X17)
        | X16 != X17 )
      & ( r1_tarski(X17,X16)
        | X16 != X17 )
      & ( ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X17,X16)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_23,plain,(
    ! [X43,X44,X45] :
      ( ( v1_funct_1(X45)
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,X43,X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
        | v1_xboole_0(X44) )
      & ( v1_partfun1(X45,X43)
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,X43,X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
        | v1_xboole_0(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

fof(c_0_24,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    & ~ v1_xboole_0(esk3_0)
    & ~ v1_xboole_0(esk4_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
    & ~ v1_xboole_0(esk5_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0))
    & r1_subset_1(esk4_0,esk5_0)
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk4_0,esk3_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))
    & v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,esk5_0,esk3_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0)))
    & ( k2_partfun1(esk4_0,esk3_0,esk6_0,k9_subset_1(esk2_0,esk4_0,esk5_0)) != k2_partfun1(esk5_0,esk3_0,esk7_0,k9_subset_1(esk2_0,esk4_0,esk5_0))
      | k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0) != esk6_0
      | k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0) != esk7_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).

fof(c_0_25,plain,(
    ! [X40,X41,X42] :
      ( ( v4_relat_1(X42,X40)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( v5_relat_1(X42,X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_26,plain,(
    ! [X37,X38,X39] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
      | v1_relat_1(X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_29,plain,(
    ! [X35,X36] :
      ( ( ~ r1_subset_1(X35,X36)
        | r1_xboole_0(X35,X36)
        | v1_xboole_0(X35)
        | v1_xboole_0(X36) )
      & ( ~ r1_xboole_0(X35,X36)
        | r1_subset_1(X35,X36)
        | v1_xboole_0(X35)
        | v1_xboole_0(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).

fof(c_0_30,plain,(
    ! [X25,X26,X27] :
      ( ~ r2_hidden(X25,X26)
      | ~ m1_subset_1(X26,k1_zfmisc_1(X27))
      | ~ v1_xboole_0(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_31,plain,(
    ! [X23,X24] :
      ( ( ~ m1_subset_1(X23,k1_zfmisc_1(X24))
        | r1_tarski(X23,X24) )
      & ( ~ r1_tarski(X23,X24)
        | m1_subset_1(X23,k1_zfmisc_1(X24)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_33,plain,(
    ! [X46,X47] :
      ( ( ~ v1_partfun1(X47,X46)
        | k1_relat_1(X47) = X46
        | ~ v1_relat_1(X47)
        | ~ v4_relat_1(X47,X46) )
      & ( k1_relat_1(X47) != X46
        | v1_partfun1(X47,X46)
        | ~ v1_relat_1(X47)
        | ~ v4_relat_1(X47,X46) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

cnf(c_0_34,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_2(esk7_0,esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_38,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_39,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_40,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_42,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_43,plain,
    ( r1_xboole_0(X1,X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_44,negated_conjecture,
    ( r1_subset_1(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_45,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_46,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_48,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_32])).

fof(c_0_50,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X29)
      | k7_relat_1(X29,X28) = k7_relat_1(X29,k3_xboole_0(k1_relat_1(X29),X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t192_relat_1])])).

cnf(c_0_51,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_52,negated_conjecture,
    ( v1_partfun1(esk7_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37])]),c_0_38])).

cnf(c_0_53,negated_conjecture,
    ( v4_relat_1(esk7_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_37])).

cnf(c_0_54,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_37])).

fof(c_0_55,plain,(
    ! [X8,X9] :
      ( ( ~ r1_xboole_0(X8,X9)
        | k3_xboole_0(X8,X9) = k1_xboole_0 )
      & ( k3_xboole_0(X8,X9) != k1_xboole_0
        | r1_xboole_0(X8,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_56,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_57,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_46])).

fof(c_0_58,plain,(
    ! [X30,X31,X32] :
      ( ~ v1_relat_1(X32)
      | ~ r1_xboole_0(X30,X31)
      | k7_relat_1(k7_relat_1(X32,X30),X31) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t207_relat_1])])).

cnf(c_0_59,plain,
    ( r1_xboole_0(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_47,c_0_42])).

cnf(c_0_60,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

fof(c_0_61,plain,(
    ! [X33,X34] :
      ( ~ v1_relat_1(X34)
      | ~ v4_relat_1(X34,X33)
      | X34 = k7_relat_1(X34,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_62,plain,
    ( k7_relat_1(X1,X2) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_63,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_54])])).

cnf(c_0_64,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_65,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_66,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_67,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_69,plain,(
    ! [X59,X60,X61,X62,X63,X64] :
      ( ( v1_funct_1(k1_tmap_1(X59,X60,X61,X62,X63,X64))
        | v1_xboole_0(X59)
        | v1_xboole_0(X60)
        | v1_xboole_0(X61)
        | ~ m1_subset_1(X61,k1_zfmisc_1(X59))
        | v1_xboole_0(X62)
        | ~ m1_subset_1(X62,k1_zfmisc_1(X59))
        | ~ v1_funct_1(X63)
        | ~ v1_funct_2(X63,X61,X60)
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X60)))
        | ~ v1_funct_1(X64)
        | ~ v1_funct_2(X64,X62,X60)
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X60))) )
      & ( v1_funct_2(k1_tmap_1(X59,X60,X61,X62,X63,X64),k4_subset_1(X59,X61,X62),X60)
        | v1_xboole_0(X59)
        | v1_xboole_0(X60)
        | v1_xboole_0(X61)
        | ~ m1_subset_1(X61,k1_zfmisc_1(X59))
        | v1_xboole_0(X62)
        | ~ m1_subset_1(X62,k1_zfmisc_1(X59))
        | ~ v1_funct_1(X63)
        | ~ v1_funct_2(X63,X61,X60)
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X60)))
        | ~ v1_funct_1(X64)
        | ~ v1_funct_2(X64,X62,X60)
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X60))) )
      & ( m1_subset_1(k1_tmap_1(X59,X60,X61,X62,X63,X64),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X59,X61,X62),X60)))
        | v1_xboole_0(X59)
        | v1_xboole_0(X60)
        | v1_xboole_0(X61)
        | ~ m1_subset_1(X61,k1_zfmisc_1(X59))
        | v1_xboole_0(X62)
        | ~ m1_subset_1(X62,k1_zfmisc_1(X59))
        | ~ v1_funct_1(X63)
        | ~ v1_funct_2(X63,X61,X60)
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X60)))
        | ~ v1_funct_1(X64)
        | ~ v1_funct_2(X64,X62,X60)
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X60))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tmap_1])])])])).

fof(c_0_70,plain,(
    ! [X21,X22] :
      ( ~ v1_xboole_0(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | v1_xboole_0(X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_71,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_72,plain,
    ( r1_xboole_0(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_73,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

fof(c_0_74,plain,(
    ! [X48,X49,X50,X51] :
      ( ~ v1_funct_1(X50)
      | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))
      | k2_partfun1(X48,X49,X50,X51) = k7_relat_1(X50,X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

fof(c_0_75,plain,(
    ! [X18,X19,X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(X18))
      | k9_subset_1(X18,X19,X20) = k3_xboole_0(X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_76,negated_conjecture,
    ( k7_relat_1(esk7_0,k3_xboole_0(esk5_0,X1)) = k7_relat_1(esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_54])])).

cnf(c_0_77,negated_conjecture,
    ( k3_xboole_0(esk5_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_78,negated_conjecture,
    ( v1_partfun1(esk6_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_66]),c_0_67]),c_0_68])]),c_0_38])).

cnf(c_0_79,negated_conjecture,
    ( v4_relat_1(esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_68])).

cnf(c_0_80,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_68])).

fof(c_0_81,plain,(
    ! [X52,X53,X54,X55,X56,X57,X58] :
      ( ( k2_partfun1(k4_subset_1(X52,X54,X55),X53,X58,X54) = X56
        | X58 != k1_tmap_1(X52,X53,X54,X55,X56,X57)
        | ~ v1_funct_1(X58)
        | ~ v1_funct_2(X58,k4_subset_1(X52,X54,X55),X53)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X52,X54,X55),X53)))
        | k2_partfun1(X54,X53,X56,k9_subset_1(X52,X54,X55)) != k2_partfun1(X55,X53,X57,k9_subset_1(X52,X54,X55))
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,X55,X53)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X53)))
        | ~ v1_funct_1(X56)
        | ~ v1_funct_2(X56,X54,X53)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X53)))
        | v1_xboole_0(X55)
        | ~ m1_subset_1(X55,k1_zfmisc_1(X52))
        | v1_xboole_0(X54)
        | ~ m1_subset_1(X54,k1_zfmisc_1(X52))
        | v1_xboole_0(X53)
        | v1_xboole_0(X52) )
      & ( k2_partfun1(k4_subset_1(X52,X54,X55),X53,X58,X55) = X57
        | X58 != k1_tmap_1(X52,X53,X54,X55,X56,X57)
        | ~ v1_funct_1(X58)
        | ~ v1_funct_2(X58,k4_subset_1(X52,X54,X55),X53)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X52,X54,X55),X53)))
        | k2_partfun1(X54,X53,X56,k9_subset_1(X52,X54,X55)) != k2_partfun1(X55,X53,X57,k9_subset_1(X52,X54,X55))
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,X55,X53)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X53)))
        | ~ v1_funct_1(X56)
        | ~ v1_funct_2(X56,X54,X53)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X53)))
        | v1_xboole_0(X55)
        | ~ m1_subset_1(X55,k1_zfmisc_1(X52))
        | v1_xboole_0(X54)
        | ~ m1_subset_1(X54,k1_zfmisc_1(X52))
        | v1_xboole_0(X53)
        | v1_xboole_0(X52) )
      & ( k2_partfun1(k4_subset_1(X52,X54,X55),X53,X58,X54) != X56
        | k2_partfun1(k4_subset_1(X52,X54,X55),X53,X58,X55) != X57
        | X58 = k1_tmap_1(X52,X53,X54,X55,X56,X57)
        | ~ v1_funct_1(X58)
        | ~ v1_funct_2(X58,k4_subset_1(X52,X54,X55),X53)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X52,X54,X55),X53)))
        | k2_partfun1(X54,X53,X56,k9_subset_1(X52,X54,X55)) != k2_partfun1(X55,X53,X57,k9_subset_1(X52,X54,X55))
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,X55,X53)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X53)))
        | ~ v1_funct_1(X56)
        | ~ v1_funct_2(X56,X54,X53)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X53)))
        | v1_xboole_0(X55)
        | ~ m1_subset_1(X55,k1_zfmisc_1(X52))
        | v1_xboole_0(X54)
        | ~ m1_subset_1(X54,k1_zfmisc_1(X52))
        | v1_xboole_0(X53)
        | v1_xboole_0(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tmap_1])])])])])).

cnf(c_0_82,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_83,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_84,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_85,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_86,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_87,negated_conjecture,
    ( k7_relat_1(esk7_0,esk5_0) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_53]),c_0_54])])).

cnf(c_0_88,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_89,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_90,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_91,negated_conjecture,
    ( k7_relat_1(k7_relat_1(X1,esk5_0),esk4_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_65])).

cnf(c_0_92,negated_conjecture,
    ( k7_relat_1(esk7_0,esk4_0) = k7_relat_1(esk7_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_93,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_78]),c_0_79]),c_0_80])])).

cnf(c_0_94,negated_conjecture,
    ( k7_relat_1(k7_relat_1(X1,esk4_0),esk5_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_57])).

cnf(c_0_95,negated_conjecture,
    ( k7_relat_1(esk6_0,esk4_0) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_79]),c_0_80])])).

cnf(c_0_96,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_97,plain,
    ( m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2)))
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4)
    | ~ v1_funct_2(X6,X4,X2)
    | ~ v1_funct_2(X5,X3,X2)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_98,plain,
    ( v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4)
    | ~ v1_funct_2(X6,X4,X2)
    | ~ v1_funct_2(X5,X3,X2)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[c_0_84,c_0_83])).

cnf(c_0_99,plain,
    ( v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4)
    | ~ v1_funct_2(X6,X4,X2)
    | ~ v1_funct_2(X5,X3,X2)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[c_0_85,c_0_83])).

cnf(c_0_100,negated_conjecture,
    ( k7_relat_1(esk7_0,X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_54])])).

cnf(c_0_101,negated_conjecture,
    ( k7_relat_1(esk7_0,X1) = k2_partfun1(esk5_0,esk3_0,esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_37]),c_0_36])])).

cnf(c_0_102,negated_conjecture,
    ( k2_partfun1(esk4_0,esk3_0,esk6_0,k9_subset_1(esk2_0,esk4_0,esk5_0)) != k2_partfun1(esk5_0,esk3_0,esk7_0,k9_subset_1(esk2_0,esk4_0,esk5_0))
    | k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0) != esk6_0
    | k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0) != esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_103,negated_conjecture,
    ( k9_subset_1(esk2_0,X1,esk5_0) = k3_xboole_0(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_104,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_64,c_0_57])).

cnf(c_0_105,negated_conjecture,
    ( k7_relat_1(esk7_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_87]),c_0_92]),c_0_54])])).

cnf(c_0_106,negated_conjecture,
    ( k7_relat_1(esk6_0,k3_xboole_0(esk4_0,X1)) = k7_relat_1(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_93]),c_0_80])])).

cnf(c_0_107,negated_conjecture,
    ( k7_relat_1(esk6_0,esk5_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_80])])).

cnf(c_0_108,plain,
    ( k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X2) = X5
    | v1_xboole_0(X4)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3)) != k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))
    | ~ v1_funct_2(X6,X3,X4)
    | ~ v1_funct_2(X5,X2,X4)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_96,c_0_83])]),c_0_97]),c_0_98]),c_0_99])).

cnf(c_0_109,negated_conjecture,
    ( k2_partfun1(esk5_0,esk3_0,esk7_0,X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_110,plain,
    ( k3_xboole_0(X1,X2) = k9_subset_1(X2,X1,X2) ),
    inference(spm,[status(thm)],[c_0_89,c_0_60])).

cnf(c_0_111,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_112,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0) != esk6_0
    | k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0) != esk7_0
    | k2_partfun1(esk5_0,esk3_0,esk7_0,k1_xboole_0) != k2_partfun1(esk4_0,esk3_0,esk6_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_103]),c_0_104]),c_0_103]),c_0_104])).

cnf(c_0_113,negated_conjecture,
    ( k2_partfun1(esk5_0,esk3_0,esk7_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_105,c_0_101])).

cnf(c_0_114,negated_conjecture,
    ( k7_relat_1(esk6_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_104]),c_0_107])).

cnf(c_0_115,negated_conjecture,
    ( k7_relat_1(esk6_0,X1) = k2_partfun1(esk4_0,esk3_0,esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_68]),c_0_67])])).

cnf(c_0_116,negated_conjecture,
    ( k2_partfun1(k4_subset_1(X1,X2,esk5_0),esk3_0,k1_tmap_1(X1,esk3_0,X2,esk5_0,X3,esk7_0),X2) = X3
    | v1_xboole_0(X2)
    | k2_partfun1(X2,esk3_0,X3,k9_subset_1(X1,X2,esk5_0)) != k1_xboole_0
    | ~ v1_funct_2(X3,X2,esk3_0)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,esk3_0)))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(k9_subset_1(X1,X2,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_35]),c_0_36]),c_0_37])]),c_0_45]),c_0_38])).

cnf(c_0_117,negated_conjecture,
    ( k9_subset_1(esk2_0,X1,esk5_0) = k9_subset_1(esk5_0,X1,esk5_0) ),
    inference(rw,[status(thm)],[c_0_103,c_0_110])).

cnf(c_0_118,negated_conjecture,
    ( k7_relat_1(esk6_0,X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_95]),c_0_80])])).

cnf(c_0_119,plain,
    ( k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X3) = X6
    | v1_xboole_0(X4)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3)) != k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))
    | ~ v1_funct_2(X5,X2,X4)
    | ~ v1_funct_2(X6,X3,X4)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_111,c_0_83])]),c_0_97]),c_0_98]),c_0_99])).

cnf(c_0_120,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0) != esk6_0
    | k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0) != esk7_0
    | k2_partfun1(esk4_0,esk3_0,esk6_0,k1_xboole_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_121,negated_conjecture,
    ( k2_partfun1(esk4_0,esk3_0,esk6_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_114,c_0_115])).

cnf(c_0_122,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,X1,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,X1,esk5_0,X2,esk7_0),X1) = X2
    | v1_xboole_0(X1)
    | k2_partfun1(X1,esk3_0,X2,k9_subset_1(esk5_0,X1,esk5_0)) != k1_xboole_0
    | ~ v1_funct_2(X2,X1,esk3_0)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0))
    | ~ v1_xboole_0(k9_subset_1(esk5_0,X1,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_90])])).

cnf(c_0_123,negated_conjecture,
    ( k2_partfun1(esk4_0,esk3_0,esk6_0,X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_118,c_0_115])).

cnf(c_0_124,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_125,negated_conjecture,
    ( k9_subset_1(esk5_0,esk4_0,esk5_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_104,c_0_110])).

cnf(c_0_126,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_127,negated_conjecture,
    ( k2_partfun1(k4_subset_1(X1,X2,esk5_0),esk3_0,k1_tmap_1(X1,esk3_0,X2,esk5_0,X3,esk7_0),esk5_0) = esk7_0
    | v1_xboole_0(X2)
    | k2_partfun1(X2,esk3_0,X3,k9_subset_1(X1,X2,esk5_0)) != k1_xboole_0
    | ~ v1_funct_2(X3,X2,esk3_0)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,esk3_0)))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(k9_subset_1(X1,X2,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_109]),c_0_35]),c_0_36]),c_0_37])]),c_0_45]),c_0_38])).

cnf(c_0_128,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0) != esk6_0
    | k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0) != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_120,c_0_121])])).

cnf(c_0_129,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0) = esk6_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_123]),c_0_66]),c_0_67]),c_0_68]),c_0_124]),c_0_125]),c_0_126])]),c_0_46])).

cnf(c_0_130,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,X1,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,X1,esk5_0,X2,esk7_0),esk5_0) = esk7_0
    | v1_xboole_0(X1)
    | k2_partfun1(X1,esk3_0,X2,k9_subset_1(esk5_0,X1,esk5_0)) != k1_xboole_0
    | ~ v1_funct_2(X2,X1,esk3_0)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0))
    | ~ v1_xboole_0(k9_subset_1(esk5_0,X1,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_117]),c_0_90])])).

cnf(c_0_131,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0) != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_128,c_0_129])])).

cnf(c_0_132,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_123]),c_0_66]),c_0_67]),c_0_68]),c_0_124]),c_0_125]),c_0_126])]),c_0_131]),c_0_46]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:41:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.21/0.35  # No SInE strategy applied
% 0.21/0.35  # Trying AutoSched0 for 299 seconds
% 0.70/0.87  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.70/0.87  # and selection function SelectCQIPrecWNTNp.
% 0.70/0.87  #
% 0.70/0.87  # Preprocessing time       : 0.030 s
% 0.70/0.87  # Presaturation interreduction done
% 0.70/0.87  
% 0.70/0.87  # Proof found!
% 0.70/0.87  # SZS status Theorem
% 0.70/0.87  # SZS output start CNFRefutation
% 0.70/0.87  fof(t6_tmap_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>(r1_subset_1(X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3)=X5)&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4)=X6)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 0.70/0.87  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.70/0.87  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.70/0.87  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.70/0.87  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.70/0.87  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.70/0.87  fof(redefinition_r1_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))=>(r1_subset_1(X1,X2)<=>r1_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 0.70/0.87  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.70/0.87  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.70/0.87  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 0.70/0.87  fof(t192_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k7_relat_1(X2,k3_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_relat_1)).
% 0.70/0.87  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.70/0.87  fof(t207_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_xboole_0(X1,X2)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 0.70/0.87  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 0.70/0.87  fof(dt_k1_tmap_1, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((((((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))&~(v1_xboole_0(X3)))&m1_subset_1(X3,k1_zfmisc_1(X1)))&~(v1_xboole_0(X4)))&m1_subset_1(X4,k1_zfmisc_1(X1)))&v1_funct_1(X5))&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2))&m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 0.70/0.87  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.70/0.87  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 0.70/0.87  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.70/0.87  fof(d1_tmap_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>(k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))=>![X7]:(((v1_funct_1(X7)&v1_funct_2(X7,k4_subset_1(X1,X3,X4),X2))&m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))))=>(X7=k1_tmap_1(X1,X2,X3,X4,X5,X6)<=>(k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X3)=X5&k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X4)=X6)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 0.70/0.87  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.70/0.87  fof(c_0_20, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>(r1_subset_1(X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3)=X5)&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4)=X6))))))))), inference(assume_negation,[status(cth)],[t6_tmap_1])).
% 0.70/0.87  fof(c_0_21, plain, ![X10, X11, X13, X14, X15]:(((r2_hidden(esk1_2(X10,X11),X10)|r1_xboole_0(X10,X11))&(r2_hidden(esk1_2(X10,X11),X11)|r1_xboole_0(X10,X11)))&(~r2_hidden(X15,X13)|~r2_hidden(X15,X14)|~r1_xboole_0(X13,X14))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.70/0.87  fof(c_0_22, plain, ![X16, X17]:(((r1_tarski(X16,X17)|X16!=X17)&(r1_tarski(X17,X16)|X16!=X17))&(~r1_tarski(X16,X17)|~r1_tarski(X17,X16)|X16=X17)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.70/0.87  fof(c_0_23, plain, ![X43, X44, X45]:((v1_funct_1(X45)|(~v1_funct_1(X45)|~v1_funct_2(X45,X43,X44))|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))|v1_xboole_0(X44))&(v1_partfun1(X45,X43)|(~v1_funct_1(X45)|~v1_funct_2(X45,X43,X44))|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))|v1_xboole_0(X44))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.70/0.87  fof(c_0_24, negated_conjecture, (~v1_xboole_0(esk2_0)&(~v1_xboole_0(esk3_0)&((~v1_xboole_0(esk4_0)&m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)))&((~v1_xboole_0(esk5_0)&m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0)))&(r1_subset_1(esk4_0,esk5_0)&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk4_0,esk3_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))))&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk5_0,esk3_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0))))&(k2_partfun1(esk4_0,esk3_0,esk6_0,k9_subset_1(esk2_0,esk4_0,esk5_0))!=k2_partfun1(esk5_0,esk3_0,esk7_0,k9_subset_1(esk2_0,esk4_0,esk5_0))|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0)!=esk6_0|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0)!=esk7_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).
% 0.70/0.87  fof(c_0_25, plain, ![X40, X41, X42]:((v4_relat_1(X42,X40)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))&(v5_relat_1(X42,X41)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.70/0.87  fof(c_0_26, plain, ![X37, X38, X39]:(~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))|v1_relat_1(X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.70/0.87  cnf(c_0_27, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.70/0.87  cnf(c_0_28, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.70/0.87  fof(c_0_29, plain, ![X35, X36]:((~r1_subset_1(X35,X36)|r1_xboole_0(X35,X36)|(v1_xboole_0(X35)|v1_xboole_0(X36)))&(~r1_xboole_0(X35,X36)|r1_subset_1(X35,X36)|(v1_xboole_0(X35)|v1_xboole_0(X36)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).
% 0.70/0.87  fof(c_0_30, plain, ![X25, X26, X27]:(~r2_hidden(X25,X26)|~m1_subset_1(X26,k1_zfmisc_1(X27))|~v1_xboole_0(X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.70/0.87  fof(c_0_31, plain, ![X23, X24]:((~m1_subset_1(X23,k1_zfmisc_1(X24))|r1_tarski(X23,X24))&(~r1_tarski(X23,X24)|m1_subset_1(X23,k1_zfmisc_1(X24)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.70/0.87  cnf(c_0_32, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.70/0.87  fof(c_0_33, plain, ![X46, X47]:((~v1_partfun1(X47,X46)|k1_relat_1(X47)=X46|(~v1_relat_1(X47)|~v4_relat_1(X47,X46)))&(k1_relat_1(X47)!=X46|v1_partfun1(X47,X46)|(~v1_relat_1(X47)|~v4_relat_1(X47,X46)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 0.70/0.87  cnf(c_0_34, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.70/0.87  cnf(c_0_35, negated_conjecture, (v1_funct_2(esk7_0,esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.70/0.87  cnf(c_0_36, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.70/0.87  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.70/0.87  cnf(c_0_38, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.70/0.87  cnf(c_0_39, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.70/0.87  cnf(c_0_40, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.70/0.87  cnf(c_0_41, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.70/0.87  cnf(c_0_42, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.70/0.87  cnf(c_0_43, plain, (r1_xboole_0(X1,X2)|v1_xboole_0(X1)|v1_xboole_0(X2)|~r1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.70/0.87  cnf(c_0_44, negated_conjecture, (r1_subset_1(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.70/0.87  cnf(c_0_45, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.70/0.87  cnf(c_0_46, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.70/0.87  cnf(c_0_47, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.70/0.87  cnf(c_0_48, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.70/0.87  cnf(c_0_49, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_32])).
% 0.70/0.87  fof(c_0_50, plain, ![X28, X29]:(~v1_relat_1(X29)|k7_relat_1(X29,X28)=k7_relat_1(X29,k3_xboole_0(k1_relat_1(X29),X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t192_relat_1])])).
% 0.70/0.87  cnf(c_0_51, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.70/0.87  cnf(c_0_52, negated_conjecture, (v1_partfun1(esk7_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_37])]), c_0_38])).
% 0.70/0.87  cnf(c_0_53, negated_conjecture, (v4_relat_1(esk7_0,esk5_0)), inference(spm,[status(thm)],[c_0_39, c_0_37])).
% 0.70/0.87  cnf(c_0_54, negated_conjecture, (v1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_40, c_0_37])).
% 0.70/0.87  fof(c_0_55, plain, ![X8, X9]:((~r1_xboole_0(X8,X9)|k3_xboole_0(X8,X9)=k1_xboole_0)&(k3_xboole_0(X8,X9)!=k1_xboole_0|r1_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.70/0.87  cnf(c_0_56, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.70/0.87  cnf(c_0_57, negated_conjecture, (r1_xboole_0(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_46])).
% 0.70/0.87  fof(c_0_58, plain, ![X30, X31, X32]:(~v1_relat_1(X32)|(~r1_xboole_0(X30,X31)|k7_relat_1(k7_relat_1(X32,X30),X31)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t207_relat_1])])).
% 0.70/0.87  cnf(c_0_59, plain, (r1_xboole_0(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_47, c_0_42])).
% 0.70/0.87  cnf(c_0_60, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.70/0.87  fof(c_0_61, plain, ![X33, X34]:(~v1_relat_1(X34)|~v4_relat_1(X34,X33)|X34=k7_relat_1(X34,X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.70/0.87  cnf(c_0_62, plain, (k7_relat_1(X1,X2)=k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.70/0.87  cnf(c_0_63, negated_conjecture, (k1_relat_1(esk7_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_54])])).
% 0.70/0.87  cnf(c_0_64, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.70/0.87  cnf(c_0_65, negated_conjecture, (r1_xboole_0(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.70/0.87  cnf(c_0_66, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.70/0.87  cnf(c_0_67, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.70/0.87  cnf(c_0_68, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.70/0.87  fof(c_0_69, plain, ![X59, X60, X61, X62, X63, X64]:(((v1_funct_1(k1_tmap_1(X59,X60,X61,X62,X63,X64))|(v1_xboole_0(X59)|v1_xboole_0(X60)|v1_xboole_0(X61)|~m1_subset_1(X61,k1_zfmisc_1(X59))|v1_xboole_0(X62)|~m1_subset_1(X62,k1_zfmisc_1(X59))|~v1_funct_1(X63)|~v1_funct_2(X63,X61,X60)|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X60)))|~v1_funct_1(X64)|~v1_funct_2(X64,X62,X60)|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X60)))))&(v1_funct_2(k1_tmap_1(X59,X60,X61,X62,X63,X64),k4_subset_1(X59,X61,X62),X60)|(v1_xboole_0(X59)|v1_xboole_0(X60)|v1_xboole_0(X61)|~m1_subset_1(X61,k1_zfmisc_1(X59))|v1_xboole_0(X62)|~m1_subset_1(X62,k1_zfmisc_1(X59))|~v1_funct_1(X63)|~v1_funct_2(X63,X61,X60)|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X60)))|~v1_funct_1(X64)|~v1_funct_2(X64,X62,X60)|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X60))))))&(m1_subset_1(k1_tmap_1(X59,X60,X61,X62,X63,X64),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X59,X61,X62),X60)))|(v1_xboole_0(X59)|v1_xboole_0(X60)|v1_xboole_0(X61)|~m1_subset_1(X61,k1_zfmisc_1(X59))|v1_xboole_0(X62)|~m1_subset_1(X62,k1_zfmisc_1(X59))|~v1_funct_1(X63)|~v1_funct_2(X63,X61,X60)|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X60)))|~v1_funct_1(X64)|~v1_funct_2(X64,X62,X60)|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X60)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tmap_1])])])])).
% 0.70/0.87  fof(c_0_70, plain, ![X21, X22]:(~v1_xboole_0(X21)|(~m1_subset_1(X22,k1_zfmisc_1(X21))|v1_xboole_0(X22))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.70/0.87  cnf(c_0_71, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.70/0.87  cnf(c_0_72, plain, (r1_xboole_0(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.70/0.87  cnf(c_0_73, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.70/0.87  fof(c_0_74, plain, ![X48, X49, X50, X51]:(~v1_funct_1(X50)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))|k2_partfun1(X48,X49,X50,X51)=k7_relat_1(X50,X51)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 0.70/0.87  fof(c_0_75, plain, ![X18, X19, X20]:(~m1_subset_1(X20,k1_zfmisc_1(X18))|k9_subset_1(X18,X19,X20)=k3_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.70/0.87  cnf(c_0_76, negated_conjecture, (k7_relat_1(esk7_0,k3_xboole_0(esk5_0,X1))=k7_relat_1(esk7_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_54])])).
% 0.70/0.87  cnf(c_0_77, negated_conjecture, (k3_xboole_0(esk5_0,esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.70/0.87  cnf(c_0_78, negated_conjecture, (v1_partfun1(esk6_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_66]), c_0_67]), c_0_68])]), c_0_38])).
% 0.70/0.87  cnf(c_0_79, negated_conjecture, (v4_relat_1(esk6_0,esk4_0)), inference(spm,[status(thm)],[c_0_39, c_0_68])).
% 0.70/0.87  cnf(c_0_80, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_40, c_0_68])).
% 0.70/0.87  fof(c_0_81, plain, ![X52, X53, X54, X55, X56, X57, X58]:(((k2_partfun1(k4_subset_1(X52,X54,X55),X53,X58,X54)=X56|X58!=k1_tmap_1(X52,X53,X54,X55,X56,X57)|(~v1_funct_1(X58)|~v1_funct_2(X58,k4_subset_1(X52,X54,X55),X53)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X52,X54,X55),X53))))|k2_partfun1(X54,X53,X56,k9_subset_1(X52,X54,X55))!=k2_partfun1(X55,X53,X57,k9_subset_1(X52,X54,X55))|(~v1_funct_1(X57)|~v1_funct_2(X57,X55,X53)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X53))))|(~v1_funct_1(X56)|~v1_funct_2(X56,X54,X53)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X53))))|(v1_xboole_0(X55)|~m1_subset_1(X55,k1_zfmisc_1(X52)))|(v1_xboole_0(X54)|~m1_subset_1(X54,k1_zfmisc_1(X52)))|v1_xboole_0(X53)|v1_xboole_0(X52))&(k2_partfun1(k4_subset_1(X52,X54,X55),X53,X58,X55)=X57|X58!=k1_tmap_1(X52,X53,X54,X55,X56,X57)|(~v1_funct_1(X58)|~v1_funct_2(X58,k4_subset_1(X52,X54,X55),X53)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X52,X54,X55),X53))))|k2_partfun1(X54,X53,X56,k9_subset_1(X52,X54,X55))!=k2_partfun1(X55,X53,X57,k9_subset_1(X52,X54,X55))|(~v1_funct_1(X57)|~v1_funct_2(X57,X55,X53)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X53))))|(~v1_funct_1(X56)|~v1_funct_2(X56,X54,X53)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X53))))|(v1_xboole_0(X55)|~m1_subset_1(X55,k1_zfmisc_1(X52)))|(v1_xboole_0(X54)|~m1_subset_1(X54,k1_zfmisc_1(X52)))|v1_xboole_0(X53)|v1_xboole_0(X52)))&(k2_partfun1(k4_subset_1(X52,X54,X55),X53,X58,X54)!=X56|k2_partfun1(k4_subset_1(X52,X54,X55),X53,X58,X55)!=X57|X58=k1_tmap_1(X52,X53,X54,X55,X56,X57)|(~v1_funct_1(X58)|~v1_funct_2(X58,k4_subset_1(X52,X54,X55),X53)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X52,X54,X55),X53))))|k2_partfun1(X54,X53,X56,k9_subset_1(X52,X54,X55))!=k2_partfun1(X55,X53,X57,k9_subset_1(X52,X54,X55))|(~v1_funct_1(X57)|~v1_funct_2(X57,X55,X53)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X53))))|(~v1_funct_1(X56)|~v1_funct_2(X56,X54,X53)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X53))))|(v1_xboole_0(X55)|~m1_subset_1(X55,k1_zfmisc_1(X52)))|(v1_xboole_0(X54)|~m1_subset_1(X54,k1_zfmisc_1(X52)))|v1_xboole_0(X53)|v1_xboole_0(X52))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tmap_1])])])])])).
% 0.70/0.87  cnf(c_0_82, plain, (m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2)))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.70/0.87  cnf(c_0_83, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.70/0.87  cnf(c_0_84, plain, (v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.70/0.87  cnf(c_0_85, plain, (v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.70/0.87  cnf(c_0_86, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k1_xboole_0|~v1_relat_1(X1)|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.70/0.87  cnf(c_0_87, negated_conjecture, (k7_relat_1(esk7_0,esk5_0)=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_53]), c_0_54])])).
% 0.70/0.87  cnf(c_0_88, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.70/0.87  cnf(c_0_89, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.70/0.87  cnf(c_0_90, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.70/0.87  cnf(c_0_91, negated_conjecture, (k7_relat_1(k7_relat_1(X1,esk5_0),esk4_0)=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_71, c_0_65])).
% 0.70/0.87  cnf(c_0_92, negated_conjecture, (k7_relat_1(esk7_0,esk4_0)=k7_relat_1(esk7_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.70/0.87  cnf(c_0_93, negated_conjecture, (k1_relat_1(esk6_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_78]), c_0_79]), c_0_80])])).
% 0.70/0.87  cnf(c_0_94, negated_conjecture, (k7_relat_1(k7_relat_1(X1,esk4_0),esk5_0)=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_71, c_0_57])).
% 0.70/0.87  cnf(c_0_95, negated_conjecture, (k7_relat_1(esk6_0,esk4_0)=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_79]), c_0_80])])).
% 0.70/0.87  cnf(c_0_96, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X2)=X6|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X4)|v1_xboole_0(X1)|X5!=k1_tmap_1(X1,X4,X2,X3,X6,X7)|~v1_funct_1(X5)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|k2_partfun1(X2,X4,X6,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X7,k9_subset_1(X1,X2,X3))|~v1_funct_1(X7)|~v1_funct_2(X7,X3,X4)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X6)|~v1_funct_2(X6,X2,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.70/0.87  cnf(c_0_97, plain, (m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2)))|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~v1_funct_2(X6,X4,X2)|~v1_funct_2(X5,X3,X2)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[c_0_82, c_0_83])).
% 0.70/0.87  cnf(c_0_98, plain, (v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~v1_funct_2(X6,X4,X2)|~v1_funct_2(X5,X3,X2)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[c_0_84, c_0_83])).
% 0.70/0.87  cnf(c_0_99, plain, (v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~v1_funct_2(X6,X4,X2)|~v1_funct_2(X5,X3,X2)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[c_0_85, c_0_83])).
% 0.70/0.87  cnf(c_0_100, negated_conjecture, (k7_relat_1(esk7_0,X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_54])])).
% 0.70/0.87  cnf(c_0_101, negated_conjecture, (k7_relat_1(esk7_0,X1)=k2_partfun1(esk5_0,esk3_0,esk7_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_37]), c_0_36])])).
% 0.70/0.87  cnf(c_0_102, negated_conjecture, (k2_partfun1(esk4_0,esk3_0,esk6_0,k9_subset_1(esk2_0,esk4_0,esk5_0))!=k2_partfun1(esk5_0,esk3_0,esk7_0,k9_subset_1(esk2_0,esk4_0,esk5_0))|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0)!=esk6_0|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0)!=esk7_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.70/0.87  cnf(c_0_103, negated_conjecture, (k9_subset_1(esk2_0,X1,esk5_0)=k3_xboole_0(X1,esk5_0)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.70/0.87  cnf(c_0_104, negated_conjecture, (k3_xboole_0(esk4_0,esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_64, c_0_57])).
% 0.70/0.87  cnf(c_0_105, negated_conjecture, (k7_relat_1(esk7_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_87]), c_0_92]), c_0_54])])).
% 0.70/0.87  cnf(c_0_106, negated_conjecture, (k7_relat_1(esk6_0,k3_xboole_0(esk4_0,X1))=k7_relat_1(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_93]), c_0_80])])).
% 0.70/0.87  cnf(c_0_107, negated_conjecture, (k7_relat_1(esk6_0,esk5_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_80])])).
% 0.70/0.87  cnf(c_0_108, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X2)=X5|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_2(X6,X3,X4)|~v1_funct_2(X5,X2,X4)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_96, c_0_83])]), c_0_97]), c_0_98]), c_0_99])).
% 0.70/0.87  cnf(c_0_109, negated_conjecture, (k2_partfun1(esk5_0,esk3_0,esk7_0,X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 0.70/0.87  cnf(c_0_110, plain, (k3_xboole_0(X1,X2)=k9_subset_1(X2,X1,X2)), inference(spm,[status(thm)],[c_0_89, c_0_60])).
% 0.70/0.87  cnf(c_0_111, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X3)=X6|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X4)|v1_xboole_0(X1)|X5!=k1_tmap_1(X1,X4,X2,X3,X7,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|k2_partfun1(X2,X4,X7,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_1(X6)|~v1_funct_2(X6,X3,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X7)|~v1_funct_2(X7,X2,X4)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.70/0.87  cnf(c_0_112, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0)!=esk6_0|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0)!=esk7_0|k2_partfun1(esk5_0,esk3_0,esk7_0,k1_xboole_0)!=k2_partfun1(esk4_0,esk3_0,esk6_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_103]), c_0_104]), c_0_103]), c_0_104])).
% 0.70/0.87  cnf(c_0_113, negated_conjecture, (k2_partfun1(esk5_0,esk3_0,esk7_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_105, c_0_101])).
% 0.70/0.87  cnf(c_0_114, negated_conjecture, (k7_relat_1(esk6_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_104]), c_0_107])).
% 0.70/0.87  cnf(c_0_115, negated_conjecture, (k7_relat_1(esk6_0,X1)=k2_partfun1(esk4_0,esk3_0,esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_68]), c_0_67])])).
% 0.70/0.87  cnf(c_0_116, negated_conjecture, (k2_partfun1(k4_subset_1(X1,X2,esk5_0),esk3_0,k1_tmap_1(X1,esk3_0,X2,esk5_0,X3,esk7_0),X2)=X3|v1_xboole_0(X2)|k2_partfun1(X2,esk3_0,X3,k9_subset_1(X1,X2,esk5_0))!=k1_xboole_0|~v1_funct_2(X3,X2,esk3_0)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,esk3_0)))|~m1_subset_1(esk5_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_xboole_0(k9_subset_1(X1,X2,esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_35]), c_0_36]), c_0_37])]), c_0_45]), c_0_38])).
% 0.70/0.87  cnf(c_0_117, negated_conjecture, (k9_subset_1(esk2_0,X1,esk5_0)=k9_subset_1(esk5_0,X1,esk5_0)), inference(rw,[status(thm)],[c_0_103, c_0_110])).
% 0.70/0.87  cnf(c_0_118, negated_conjecture, (k7_relat_1(esk6_0,X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_95]), c_0_80])])).
% 0.70/0.87  cnf(c_0_119, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X3)=X6|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_2(X5,X2,X4)|~v1_funct_2(X6,X3,X4)|~v1_funct_1(X5)|~v1_funct_1(X6)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_111, c_0_83])]), c_0_97]), c_0_98]), c_0_99])).
% 0.70/0.87  cnf(c_0_120, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0)!=esk6_0|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0)!=esk7_0|k2_partfun1(esk4_0,esk3_0,esk6_0,k1_xboole_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_112, c_0_113])).
% 0.70/0.87  cnf(c_0_121, negated_conjecture, (k2_partfun1(esk4_0,esk3_0,esk6_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_114, c_0_115])).
% 0.70/0.87  cnf(c_0_122, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,X1,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,X1,esk5_0,X2,esk7_0),X1)=X2|v1_xboole_0(X1)|k2_partfun1(X1,esk3_0,X2,k9_subset_1(esk5_0,X1,esk5_0))!=k1_xboole_0|~v1_funct_2(X2,X1,esk3_0)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))|~v1_xboole_0(k9_subset_1(esk5_0,X1,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_117]), c_0_90])])).
% 0.70/0.87  cnf(c_0_123, negated_conjecture, (k2_partfun1(esk4_0,esk3_0,esk6_0,X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_118, c_0_115])).
% 0.70/0.87  cnf(c_0_124, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.70/0.87  cnf(c_0_125, negated_conjecture, (k9_subset_1(esk5_0,esk4_0,esk5_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_104, c_0_110])).
% 0.70/0.87  cnf(c_0_126, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.70/0.87  cnf(c_0_127, negated_conjecture, (k2_partfun1(k4_subset_1(X1,X2,esk5_0),esk3_0,k1_tmap_1(X1,esk3_0,X2,esk5_0,X3,esk7_0),esk5_0)=esk7_0|v1_xboole_0(X2)|k2_partfun1(X2,esk3_0,X3,k9_subset_1(X1,X2,esk5_0))!=k1_xboole_0|~v1_funct_2(X3,X2,esk3_0)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,esk3_0)))|~m1_subset_1(esk5_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_xboole_0(k9_subset_1(X1,X2,esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_109]), c_0_35]), c_0_36]), c_0_37])]), c_0_45]), c_0_38])).
% 0.70/0.87  cnf(c_0_128, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0)!=esk6_0|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0)!=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_120, c_0_121])])).
% 0.70/0.87  cnf(c_0_129, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0)=esk6_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_123]), c_0_66]), c_0_67]), c_0_68]), c_0_124]), c_0_125]), c_0_126])]), c_0_46])).
% 0.70/0.87  cnf(c_0_130, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,X1,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,X1,esk5_0,X2,esk7_0),esk5_0)=esk7_0|v1_xboole_0(X1)|k2_partfun1(X1,esk3_0,X2,k9_subset_1(esk5_0,X1,esk5_0))!=k1_xboole_0|~v1_funct_2(X2,X1,esk3_0)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))|~v1_xboole_0(k9_subset_1(esk5_0,X1,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_117]), c_0_90])])).
% 0.70/0.87  cnf(c_0_131, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0)!=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_128, c_0_129])])).
% 0.70/0.87  cnf(c_0_132, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_123]), c_0_66]), c_0_67]), c_0_68]), c_0_124]), c_0_125]), c_0_126])]), c_0_131]), c_0_46]), ['proof']).
% 0.70/0.87  # SZS output end CNFRefutation
% 0.70/0.87  # Proof object total steps             : 133
% 0.70/0.87  # Proof object clause steps            : 93
% 0.70/0.87  # Proof object formula steps           : 40
% 0.70/0.87  # Proof object conjectures             : 59
% 0.70/0.87  # Proof object clause conjectures      : 56
% 0.70/0.87  # Proof object formula conjectures     : 3
% 0.70/0.87  # Proof object initial clauses used    : 37
% 0.70/0.87  # Proof object initial formulas used   : 20
% 0.70/0.87  # Proof object generating inferences   : 42
% 0.70/0.87  # Proof object simplifying inferences  : 98
% 0.70/0.87  # Training examples: 0 positive, 0 negative
% 0.70/0.87  # Parsed axioms                        : 20
% 0.70/0.87  # Removed by relevancy pruning/SinE    : 0
% 0.70/0.87  # Initial clauses                      : 47
% 0.70/0.87  # Removed in clause preprocessing      : 1
% 0.70/0.87  # Initial clauses in saturation        : 46
% 0.70/0.87  # Processed clauses                    : 5209
% 0.70/0.87  # ...of these trivial                  : 102
% 0.70/0.87  # ...subsumed                          : 3758
% 0.70/0.87  # ...remaining for further processing  : 1349
% 0.70/0.87  # Other redundant clauses eliminated   : 7
% 0.70/0.87  # Clauses deleted for lack of memory   : 0
% 0.70/0.87  # Backward-subsumed                    : 69
% 0.70/0.87  # Backward-rewritten                   : 99
% 0.70/0.87  # Generated clauses                    : 24246
% 0.70/0.87  # ...of the previous two non-trivial   : 21046
% 0.70/0.87  # Contextual simplify-reflections      : 19
% 0.70/0.87  # Paramodulations                      : 24223
% 0.70/0.87  # Factorizations                       : 0
% 0.70/0.87  # Equation resolutions                 : 24
% 0.70/0.87  # Propositional unsat checks           : 0
% 0.70/0.87  #    Propositional check models        : 0
% 0.70/0.87  #    Propositional check unsatisfiable : 0
% 0.70/0.87  #    Propositional clauses             : 0
% 0.70/0.87  #    Propositional clauses after purity: 0
% 0.70/0.87  #    Propositional unsat core size     : 0
% 0.70/0.87  #    Propositional preprocessing time  : 0.000
% 0.70/0.87  #    Propositional encoding time       : 0.000
% 0.70/0.87  #    Propositional solver time         : 0.000
% 0.70/0.87  #    Success case prop preproc time    : 0.000
% 0.70/0.87  #    Success case prop encoding time   : 0.000
% 0.70/0.87  #    Success case prop solver time     : 0.000
% 0.70/0.87  # Current number of processed clauses  : 1130
% 0.70/0.87  #    Positive orientable unit clauses  : 155
% 0.70/0.87  #    Positive unorientable unit clauses: 0
% 0.70/0.87  #    Negative unit clauses             : 5
% 0.70/0.87  #    Non-unit-clauses                  : 970
% 0.70/0.87  # Current number of unprocessed clauses: 15681
% 0.70/0.87  # ...number of literals in the above   : 79686
% 0.70/0.87  # Current number of archived formulas  : 0
% 0.70/0.87  # Current number of archived clauses   : 213
% 0.70/0.87  # Clause-clause subsumption calls (NU) : 372100
% 0.70/0.87  # Rec. Clause-clause subsumption calls : 232443
% 0.70/0.87  # Non-unit clause-clause subsumptions  : 2234
% 0.70/0.87  # Unit Clause-clause subsumption calls : 13885
% 0.70/0.87  # Rewrite failures with RHS unbound    : 0
% 0.70/0.87  # BW rewrite match attempts            : 454
% 0.70/0.87  # BW rewrite match successes           : 78
% 0.70/0.87  # Condensation attempts                : 0
% 0.70/0.87  # Condensation successes               : 0
% 0.70/0.87  # Termbank termtop insertions          : 464147
% 0.70/0.87  
% 0.70/0.87  # -------------------------------------------------
% 0.70/0.87  # User time                : 0.507 s
% 0.70/0.87  # System time              : 0.016 s
% 0.70/0.87  # Total time               : 0.523 s
% 0.70/0.87  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
