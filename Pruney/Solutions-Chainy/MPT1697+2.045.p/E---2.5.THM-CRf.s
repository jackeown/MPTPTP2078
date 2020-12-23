%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:41 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :  134 (1106 expanded)
%              Number of clauses        :   95 ( 467 expanded)
%              Number of leaves         :   19 ( 269 expanded)
%              Depth                    :   12
%              Number of atoms          :  586 (7548 expanded)
%              Number of equality atoms :  108 (1346 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(cc5_funct_2,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X2) )
           => ( v1_funct_1(X3)
              & v1_partfun1(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t66_xboole_1,axiom,(
    ! [X1] :
      ( ~ ( ~ r1_xboole_0(X1,X1)
          & X1 = k1_xboole_0 )
      & ~ ( X1 != k1_xboole_0
          & r1_xboole_0(X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(redefinition_r1_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2) )
     => ( r1_subset_1(X1,X2)
      <=> r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(t187_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_xboole_0(X2,k1_relat_1(X1))
         => k7_relat_1(X1,X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tmap_1)).

fof(c_0_19,negated_conjecture,(
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

fof(c_0_20,plain,(
    ! [X10,X11,X13,X14,X15] :
      ( ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_2(X10,X11),X11)
        | r1_xboole_0(X10,X11) )
      & ( ~ r2_hidden(X15,X13)
        | ~ r2_hidden(X15,X14)
        | ~ r1_xboole_0(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_21,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(X16,X17)
        | X16 != X17 )
      & ( r1_tarski(X17,X16)
        | X16 != X17 )
      & ( ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X17,X16)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_22,plain,(
    ! [X41,X42,X43] :
      ( ( v1_funct_1(X43)
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,X41,X42)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
        | v1_xboole_0(X42) )
      & ( v1_partfun1(X43,X41)
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,X41,X42)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
        | v1_xboole_0(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

fof(c_0_23,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).

fof(c_0_24,plain,(
    ! [X38,X39,X40] :
      ( ( v4_relat_1(X40,X38)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( v5_relat_1(X40,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_25,plain,(
    ! [X35,X36,X37] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | v1_relat_1(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_28,plain,(
    ! [X18] :
      ( ( r1_xboole_0(X18,X18)
        | X18 != k1_xboole_0 )
      & ( X18 = k1_xboole_0
        | ~ r1_xboole_0(X18,X18) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).

fof(c_0_29,plain,(
    ! [X28,X29,X30] :
      ( ~ r2_hidden(X28,X29)
      | ~ m1_subset_1(X29,k1_zfmisc_1(X30))
      | ~ v1_xboole_0(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_30,plain,(
    ! [X26,X27] :
      ( ( ~ m1_subset_1(X26,k1_zfmisc_1(X27))
        | r1_tarski(X26,X27) )
      & ( ~ r1_tarski(X26,X27)
        | m1_subset_1(X26,k1_zfmisc_1(X27)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_32,plain,(
    ! [X44,X45] :
      ( ( ~ v1_partfun1(X45,X44)
        | k1_relat_1(X45) = X44
        | ~ v1_relat_1(X45)
        | ~ v4_relat_1(X45,X44) )
      & ( k1_relat_1(X45) != X44
        | v1_partfun1(X45,X44)
        | ~ v1_relat_1(X45)
        | ~ v4_relat_1(X45,X44) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

cnf(c_0_33,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_2(esk7_0,esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_38,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_39,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_40,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_41,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_42,plain,
    ( r1_xboole_0(X1,X1)
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_43,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(X21))
      | k9_subset_1(X21,X22,X23) = k3_xboole_0(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_44,plain,(
    ! [X24,X25] : k1_setfam_1(k2_tarski(X24,X25)) = k3_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_49,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_31])).

fof(c_0_51,plain,(
    ! [X8,X9] :
      ( ( ~ r1_xboole_0(X8,X9)
        | k3_xboole_0(X8,X9) = k1_xboole_0 )
      & ( k3_xboole_0(X8,X9) != k1_xboole_0
        | r1_xboole_0(X8,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_52,plain,(
    ! [X33,X34] :
      ( ( ~ r1_subset_1(X33,X34)
        | r1_xboole_0(X33,X34)
        | v1_xboole_0(X33)
        | v1_xboole_0(X34) )
      & ( ~ r1_xboole_0(X33,X34)
        | r1_subset_1(X33,X34)
        | v1_xboole_0(X33)
        | v1_xboole_0(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).

fof(c_0_53,plain,(
    ! [X31,X32] :
      ( ~ v1_relat_1(X31)
      | ~ r1_xboole_0(X32,k1_relat_1(X31))
      | k7_relat_1(X31,X32) = k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t187_relat_1])])])).

cnf(c_0_54,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_55,negated_conjecture,
    ( v1_partfun1(esk7_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_56,negated_conjecture,
    ( v4_relat_1(esk7_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_36])).

cnf(c_0_57,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_36])).

cnf(c_0_58,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_40])).

cnf(c_0_59,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_27])).

cnf(c_0_60,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_61,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_62,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_63,negated_conjecture,
    ( v1_partfun1(esk6_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_45]),c_0_46]),c_0_47])]),c_0_37])).

cnf(c_0_64,negated_conjecture,
    ( v4_relat_1(esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_47])).

cnf(c_0_65,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_47])).

cnf(c_0_66,plain,
    ( r1_xboole_0(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_48,c_0_27])).

cnf(c_0_67,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

fof(c_0_68,plain,(
    ! [X19,X20] :
      ( v1_xboole_0(X20)
      | ~ r1_tarski(X20,X19)
      | ~ r1_xboole_0(X20,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

cnf(c_0_69,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_70,plain,
    ( r1_xboole_0(X1,X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_71,negated_conjecture,
    ( r1_subset_1(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_72,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_73,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_74,plain,
    ( k7_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_75,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_57])])).

cnf(c_0_76,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_27])).

cnf(c_0_77,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

fof(c_0_78,plain,(
    ! [X46,X47,X48,X49] :
      ( ~ v1_funct_1(X48)
      | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))
      | k2_partfun1(X46,X47,X48,X49) = k7_relat_1(X48,X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

fof(c_0_79,plain,(
    ! [X50,X51,X52,X53,X54,X55,X56] :
      ( ( k2_partfun1(k4_subset_1(X50,X52,X53),X51,X56,X52) = X54
        | X56 != k1_tmap_1(X50,X51,X52,X53,X54,X55)
        | ~ v1_funct_1(X56)
        | ~ v1_funct_2(X56,k4_subset_1(X50,X52,X53),X51)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X50,X52,X53),X51)))
        | k2_partfun1(X52,X51,X54,k9_subset_1(X50,X52,X53)) != k2_partfun1(X53,X51,X55,k9_subset_1(X50,X52,X53))
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,X53,X51)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X51)))
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X52,X51)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X51)))
        | v1_xboole_0(X53)
        | ~ m1_subset_1(X53,k1_zfmisc_1(X50))
        | v1_xboole_0(X52)
        | ~ m1_subset_1(X52,k1_zfmisc_1(X50))
        | v1_xboole_0(X51)
        | v1_xboole_0(X50) )
      & ( k2_partfun1(k4_subset_1(X50,X52,X53),X51,X56,X53) = X55
        | X56 != k1_tmap_1(X50,X51,X52,X53,X54,X55)
        | ~ v1_funct_1(X56)
        | ~ v1_funct_2(X56,k4_subset_1(X50,X52,X53),X51)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X50,X52,X53),X51)))
        | k2_partfun1(X52,X51,X54,k9_subset_1(X50,X52,X53)) != k2_partfun1(X53,X51,X55,k9_subset_1(X50,X52,X53))
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,X53,X51)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X51)))
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X52,X51)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X51)))
        | v1_xboole_0(X53)
        | ~ m1_subset_1(X53,k1_zfmisc_1(X50))
        | v1_xboole_0(X52)
        | ~ m1_subset_1(X52,k1_zfmisc_1(X50))
        | v1_xboole_0(X51)
        | v1_xboole_0(X50) )
      & ( k2_partfun1(k4_subset_1(X50,X52,X53),X51,X56,X52) != X54
        | k2_partfun1(k4_subset_1(X50,X52,X53),X51,X56,X53) != X55
        | X56 = k1_tmap_1(X50,X51,X52,X53,X54,X55)
        | ~ v1_funct_1(X56)
        | ~ v1_funct_2(X56,k4_subset_1(X50,X52,X53),X51)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X50,X52,X53),X51)))
        | k2_partfun1(X52,X51,X54,k9_subset_1(X50,X52,X53)) != k2_partfun1(X53,X51,X55,k9_subset_1(X50,X52,X53))
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,X53,X51)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X51)))
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X52,X51)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X51)))
        | v1_xboole_0(X53)
        | ~ m1_subset_1(X53,k1_zfmisc_1(X50))
        | v1_xboole_0(X52)
        | ~ m1_subset_1(X52,k1_zfmisc_1(X50))
        | v1_xboole_0(X51)
        | v1_xboole_0(X50) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tmap_1])])])])])).

fof(c_0_80,plain,(
    ! [X57,X58,X59,X60,X61,X62] :
      ( ( v1_funct_1(k1_tmap_1(X57,X58,X59,X60,X61,X62))
        | v1_xboole_0(X57)
        | v1_xboole_0(X58)
        | v1_xboole_0(X59)
        | ~ m1_subset_1(X59,k1_zfmisc_1(X57))
        | v1_xboole_0(X60)
        | ~ m1_subset_1(X60,k1_zfmisc_1(X57))
        | ~ v1_funct_1(X61)
        | ~ v1_funct_2(X61,X59,X58)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X58)))
        | ~ v1_funct_1(X62)
        | ~ v1_funct_2(X62,X60,X58)
        | ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X58))) )
      & ( v1_funct_2(k1_tmap_1(X57,X58,X59,X60,X61,X62),k4_subset_1(X57,X59,X60),X58)
        | v1_xboole_0(X57)
        | v1_xboole_0(X58)
        | v1_xboole_0(X59)
        | ~ m1_subset_1(X59,k1_zfmisc_1(X57))
        | v1_xboole_0(X60)
        | ~ m1_subset_1(X60,k1_zfmisc_1(X57))
        | ~ v1_funct_1(X61)
        | ~ v1_funct_2(X61,X59,X58)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X58)))
        | ~ v1_funct_1(X62)
        | ~ v1_funct_2(X62,X60,X58)
        | ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X58))) )
      & ( m1_subset_1(k1_tmap_1(X57,X58,X59,X60,X61,X62),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X57,X59,X60),X58)))
        | v1_xboole_0(X57)
        | v1_xboole_0(X58)
        | v1_xboole_0(X59)
        | ~ m1_subset_1(X59,k1_zfmisc_1(X57))
        | v1_xboole_0(X60)
        | ~ m1_subset_1(X60,k1_zfmisc_1(X57))
        | ~ v1_funct_1(X61)
        | ~ v1_funct_2(X61,X59,X58)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X58)))
        | ~ v1_funct_1(X62)
        | ~ v1_funct_2(X62,X60,X58)
        | ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X58))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tmap_1])])])])).

cnf(c_0_81,plain,
    ( k9_subset_1(X2,X3,X1) = k1_setfam_1(k2_tarski(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_83,plain,
    ( r1_xboole_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_48,c_0_40])).

cnf(c_0_84,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_63]),c_0_64]),c_0_65])])).

cnf(c_0_85,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_86,plain,
    ( r1_xboole_0(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_87,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_88,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_69,c_0_62])).

cnf(c_0_89,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72]),c_0_73])).

cnf(c_0_90,negated_conjecture,
    ( k7_relat_1(esk7_0,X1) = k1_xboole_0
    | ~ r1_xboole_0(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_57])])).

cnf(c_0_91,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_92,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_93,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_94,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_95,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_96,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_97,negated_conjecture,
    ( k9_subset_1(esk2_0,X1,esk5_0) = k1_setfam_1(k2_tarski(X1,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_98,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k9_subset_1(X2,X1,X2) ),
    inference(spm,[status(thm)],[c_0_81,c_0_67])).

cnf(c_0_99,plain,
    ( r1_xboole_0(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_83,c_0_67])).

cnf(c_0_100,negated_conjecture,
    ( k7_relat_1(esk6_0,X1) = k1_xboole_0
    | ~ r1_xboole_0(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_84]),c_0_65])])).

cnf(c_0_101,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_102,plain,
    ( v1_xboole_0(X1)
    | ~ r1_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_87,c_0_50])).

cnf(c_0_103,negated_conjecture,
    ( k2_partfun1(esk4_0,esk3_0,esk6_0,k9_subset_1(esk2_0,esk4_0,esk5_0)) != k2_partfun1(esk5_0,esk3_0,esk7_0,k9_subset_1(esk2_0,esk4_0,esk5_0))
    | k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0) != esk6_0
    | k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0) != esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_104,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk4_0,esk5_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_105,negated_conjecture,
    ( k7_relat_1(esk7_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_106,negated_conjecture,
    ( k7_relat_1(esk7_0,X1) = k2_partfun1(esk5_0,esk3_0,esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_36]),c_0_35])])).

cnf(c_0_107,plain,
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
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_93]),c_0_94]),c_0_95]),c_0_96])).

cnf(c_0_108,negated_conjecture,
    ( k9_subset_1(esk2_0,X1,esk5_0) = k9_subset_1(esk5_0,X1,esk5_0) ),
    inference(rw,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_109,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_110,negated_conjecture,
    ( k7_relat_1(esk7_0,X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_90,c_0_99])).

cnf(c_0_111,negated_conjecture,
    ( k7_relat_1(esk6_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_100,c_0_91])).

cnf(c_0_112,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_101,c_0_101])).

cnf(c_0_113,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_102,c_0_60])).

cnf(c_0_114,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_115,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0) != esk6_0
    | k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0) != esk7_0
    | k2_partfun1(esk4_0,esk3_0,esk6_0,k1_xboole_0) != k2_partfun1(esk5_0,esk3_0,esk7_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_103,c_0_97]),c_0_104]),c_0_97]),c_0_104])).

cnf(c_0_116,negated_conjecture,
    ( k2_partfun1(esk5_0,esk3_0,esk7_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_117,negated_conjecture,
    ( k7_relat_1(esk6_0,X1) = k2_partfun1(esk4_0,esk3_0,esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_47]),c_0_46])])).

cnf(c_0_118,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,X1,esk5_0),X2,k1_tmap_1(esk2_0,X2,X1,esk5_0,X3,X4),X1) = X3
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X3,k9_subset_1(esk5_0,X1,esk5_0)) != k2_partfun1(esk5_0,X2,X4,k9_subset_1(esk5_0,X1,esk5_0))
    | ~ v1_funct_2(X4,esk5_0,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_82])]),c_0_109]),c_0_72])).

cnf(c_0_119,negated_conjecture,
    ( k2_partfun1(esk5_0,esk3_0,esk7_0,X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_110,c_0_106])).

cnf(c_0_120,negated_conjecture,
    ( k7_relat_1(esk6_0,X1) = X1
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_113])])).

cnf(c_0_121,plain,
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
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_114]),c_0_94]),c_0_95]),c_0_96])).

cnf(c_0_122,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0) != esk6_0
    | k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0) != esk7_0
    | k2_partfun1(esk4_0,esk3_0,esk6_0,k1_xboole_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_115,c_0_116])).

cnf(c_0_123,negated_conjecture,
    ( k2_partfun1(esk4_0,esk3_0,esk6_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_111,c_0_117])).

cnf(c_0_124,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,X1,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,X1,esk5_0,X2,esk7_0),X1) = X2
    | v1_xboole_0(X1)
    | k2_partfun1(X1,esk3_0,X2,k9_subset_1(esk5_0,X1,esk5_0)) != k1_xboole_0
    | ~ v1_funct_2(X2,X1,esk3_0)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0))
    | ~ v1_xboole_0(k9_subset_1(esk5_0,X1,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_34]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_125,negated_conjecture,
    ( k2_partfun1(esk4_0,esk3_0,esk6_0,X1) = X1
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_120,c_0_117])).

cnf(c_0_126,negated_conjecture,
    ( k9_subset_1(esk5_0,esk4_0,esk5_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_104,c_0_98])).

cnf(c_0_127,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_128,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,X1,esk5_0),X2,k1_tmap_1(esk2_0,X2,X1,esk5_0,X3,X4),esk5_0) = X4
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X3,k9_subset_1(esk5_0,X1,esk5_0)) != k2_partfun1(esk5_0,X2,X4,k9_subset_1(esk5_0,X1,esk5_0))
    | ~ v1_funct_2(X4,esk5_0,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_108]),c_0_82])]),c_0_109]),c_0_72])).

cnf(c_0_129,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0) != esk6_0
    | k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0) != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_122,c_0_123])])).

cnf(c_0_130,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0) = esk6_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_125]),c_0_126]),c_0_45]),c_0_46]),c_0_47]),c_0_127]),c_0_126]),c_0_113])]),c_0_73])).

cnf(c_0_131,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,X1,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,X1,esk5_0,X2,esk7_0),esk5_0) = esk7_0
    | v1_xboole_0(X1)
    | k2_partfun1(X1,esk3_0,X2,k9_subset_1(esk5_0,X1,esk5_0)) != k1_xboole_0
    | ~ v1_funct_2(X2,X1,esk3_0)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0))
    | ~ v1_xboole_0(k9_subset_1(esk5_0,X1,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_119]),c_0_34]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_132,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0) != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_129,c_0_130])])).

cnf(c_0_133,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_125]),c_0_126]),c_0_45]),c_0_46]),c_0_47]),c_0_127]),c_0_126]),c_0_113])]),c_0_132]),c_0_73]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:58:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 3.61/3.81  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 3.61/3.81  # and selection function SelectCQIPrecWNTNp.
% 3.61/3.81  #
% 3.61/3.81  # Preprocessing time       : 0.030 s
% 3.61/3.81  # Presaturation interreduction done
% 3.61/3.81  
% 3.61/3.81  # Proof found!
% 3.61/3.81  # SZS status Theorem
% 3.61/3.81  # SZS output start CNFRefutation
% 3.61/3.81  fof(t6_tmap_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>(r1_subset_1(X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3)=X5)&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4)=X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 3.61/3.81  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.61/3.81  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.61/3.81  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.61/3.81  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.61/3.81  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.61/3.81  fof(t66_xboole_1, axiom, ![X1]:(~((~(r1_xboole_0(X1,X1))&X1=k1_xboole_0))&~((X1!=k1_xboole_0&r1_xboole_0(X1,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 3.61/3.81  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.61/3.81  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.61/3.81  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 3.61/3.81  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.61/3.81  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.61/3.81  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.61/3.81  fof(redefinition_r1_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))=>(r1_subset_1(X1,X2)<=>r1_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 3.61/3.81  fof(t187_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_xboole_0(X2,k1_relat_1(X1))=>k7_relat_1(X1,X2)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 3.61/3.81  fof(t69_xboole_1, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.61/3.81  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.61/3.81  fof(d1_tmap_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>(k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))=>![X7]:(((v1_funct_1(X7)&v1_funct_2(X7,k4_subset_1(X1,X3,X4),X2))&m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))))=>(X7=k1_tmap_1(X1,X2,X3,X4,X5,X6)<=>(k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X3)=X5&k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X4)=X6)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 3.61/3.81  fof(dt_k1_tmap_1, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((((((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))&~(v1_xboole_0(X3)))&m1_subset_1(X3,k1_zfmisc_1(X1)))&~(v1_xboole_0(X4)))&m1_subset_1(X4,k1_zfmisc_1(X1)))&v1_funct_1(X5))&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2))&m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 3.61/3.81  fof(c_0_19, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>(r1_subset_1(X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3)=X5)&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4)=X6))))))))), inference(assume_negation,[status(cth)],[t6_tmap_1])).
% 3.61/3.81  fof(c_0_20, plain, ![X10, X11, X13, X14, X15]:(((r2_hidden(esk1_2(X10,X11),X10)|r1_xboole_0(X10,X11))&(r2_hidden(esk1_2(X10,X11),X11)|r1_xboole_0(X10,X11)))&(~r2_hidden(X15,X13)|~r2_hidden(X15,X14)|~r1_xboole_0(X13,X14))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 3.61/3.81  fof(c_0_21, plain, ![X16, X17]:(((r1_tarski(X16,X17)|X16!=X17)&(r1_tarski(X17,X16)|X16!=X17))&(~r1_tarski(X16,X17)|~r1_tarski(X17,X16)|X16=X17)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 3.61/3.81  fof(c_0_22, plain, ![X41, X42, X43]:((v1_funct_1(X43)|(~v1_funct_1(X43)|~v1_funct_2(X43,X41,X42))|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|v1_xboole_0(X42))&(v1_partfun1(X43,X41)|(~v1_funct_1(X43)|~v1_funct_2(X43,X41,X42))|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|v1_xboole_0(X42))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 3.61/3.81  fof(c_0_23, negated_conjecture, (~v1_xboole_0(esk2_0)&(~v1_xboole_0(esk3_0)&((~v1_xboole_0(esk4_0)&m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)))&((~v1_xboole_0(esk5_0)&m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0)))&(r1_subset_1(esk4_0,esk5_0)&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk4_0,esk3_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))))&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk5_0,esk3_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0))))&(k2_partfun1(esk4_0,esk3_0,esk6_0,k9_subset_1(esk2_0,esk4_0,esk5_0))!=k2_partfun1(esk5_0,esk3_0,esk7_0,k9_subset_1(esk2_0,esk4_0,esk5_0))|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0)!=esk6_0|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0)!=esk7_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).
% 3.61/3.81  fof(c_0_24, plain, ![X38, X39, X40]:((v4_relat_1(X40,X38)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))&(v5_relat_1(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 3.61/3.81  fof(c_0_25, plain, ![X35, X36, X37]:(~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|v1_relat_1(X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 3.61/3.81  cnf(c_0_26, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 3.61/3.81  cnf(c_0_27, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 3.61/3.81  fof(c_0_28, plain, ![X18]:((r1_xboole_0(X18,X18)|X18!=k1_xboole_0)&(X18=k1_xboole_0|~r1_xboole_0(X18,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).
% 3.61/3.81  fof(c_0_29, plain, ![X28, X29, X30]:(~r2_hidden(X28,X29)|~m1_subset_1(X29,k1_zfmisc_1(X30))|~v1_xboole_0(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 3.61/3.81  fof(c_0_30, plain, ![X26, X27]:((~m1_subset_1(X26,k1_zfmisc_1(X27))|r1_tarski(X26,X27))&(~r1_tarski(X26,X27)|m1_subset_1(X26,k1_zfmisc_1(X27)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 3.61/3.81  cnf(c_0_31, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 3.61/3.81  fof(c_0_32, plain, ![X44, X45]:((~v1_partfun1(X45,X44)|k1_relat_1(X45)=X44|(~v1_relat_1(X45)|~v4_relat_1(X45,X44)))&(k1_relat_1(X45)!=X44|v1_partfun1(X45,X44)|(~v1_relat_1(X45)|~v4_relat_1(X45,X44)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 3.61/3.81  cnf(c_0_33, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 3.61/3.81  cnf(c_0_34, negated_conjecture, (v1_funct_2(esk7_0,esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 3.61/3.81  cnf(c_0_35, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 3.61/3.81  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 3.61/3.81  cnf(c_0_37, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 3.61/3.81  cnf(c_0_38, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 3.61/3.81  cnf(c_0_39, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 3.61/3.81  cnf(c_0_40, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 3.61/3.81  cnf(c_0_41, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 3.61/3.81  cnf(c_0_42, plain, (r1_xboole_0(X1,X1)|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 3.61/3.81  fof(c_0_43, plain, ![X21, X22, X23]:(~m1_subset_1(X23,k1_zfmisc_1(X21))|k9_subset_1(X21,X22,X23)=k3_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 3.61/3.81  fof(c_0_44, plain, ![X24, X25]:k1_setfam_1(k2_tarski(X24,X25))=k3_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 3.61/3.81  cnf(c_0_45, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 3.61/3.81  cnf(c_0_46, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 3.61/3.81  cnf(c_0_47, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 3.61/3.81  cnf(c_0_48, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 3.61/3.81  cnf(c_0_49, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 3.61/3.81  cnf(c_0_50, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_31])).
% 3.61/3.81  fof(c_0_51, plain, ![X8, X9]:((~r1_xboole_0(X8,X9)|k3_xboole_0(X8,X9)=k1_xboole_0)&(k3_xboole_0(X8,X9)!=k1_xboole_0|r1_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 3.61/3.81  fof(c_0_52, plain, ![X33, X34]:((~r1_subset_1(X33,X34)|r1_xboole_0(X33,X34)|(v1_xboole_0(X33)|v1_xboole_0(X34)))&(~r1_xboole_0(X33,X34)|r1_subset_1(X33,X34)|(v1_xboole_0(X33)|v1_xboole_0(X34)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).
% 3.61/3.81  fof(c_0_53, plain, ![X31, X32]:(~v1_relat_1(X31)|(~r1_xboole_0(X32,k1_relat_1(X31))|k7_relat_1(X31,X32)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t187_relat_1])])])).
% 3.61/3.81  cnf(c_0_54, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 3.61/3.81  cnf(c_0_55, negated_conjecture, (v1_partfun1(esk7_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36])]), c_0_37])).
% 3.61/3.81  cnf(c_0_56, negated_conjecture, (v4_relat_1(esk7_0,esk5_0)), inference(spm,[status(thm)],[c_0_38, c_0_36])).
% 3.61/3.81  cnf(c_0_57, negated_conjecture, (v1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_39, c_0_36])).
% 3.61/3.81  cnf(c_0_58, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_26, c_0_40])).
% 3.61/3.81  cnf(c_0_59, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_41, c_0_27])).
% 3.61/3.81  cnf(c_0_60, plain, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(er,[status(thm)],[c_0_42])).
% 3.61/3.81  cnf(c_0_61, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 3.61/3.81  cnf(c_0_62, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 3.61/3.81  cnf(c_0_63, negated_conjecture, (v1_partfun1(esk6_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_45]), c_0_46]), c_0_47])]), c_0_37])).
% 3.61/3.81  cnf(c_0_64, negated_conjecture, (v4_relat_1(esk6_0,esk4_0)), inference(spm,[status(thm)],[c_0_38, c_0_47])).
% 3.61/3.81  cnf(c_0_65, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_39, c_0_47])).
% 3.61/3.81  cnf(c_0_66, plain, (r1_xboole_0(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_48, c_0_27])).
% 3.61/3.81  cnf(c_0_67, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 3.61/3.81  fof(c_0_68, plain, ![X19, X20]:(v1_xboole_0(X20)|(~r1_tarski(X20,X19)|~r1_xboole_0(X20,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).
% 3.61/3.81  cnf(c_0_69, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 3.61/3.81  cnf(c_0_70, plain, (r1_xboole_0(X1,X2)|v1_xboole_0(X1)|v1_xboole_0(X2)|~r1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 3.61/3.81  cnf(c_0_71, negated_conjecture, (r1_subset_1(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 3.61/3.81  cnf(c_0_72, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 3.61/3.81  cnf(c_0_73, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 3.61/3.81  cnf(c_0_74, plain, (k7_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 3.61/3.81  cnf(c_0_75, negated_conjecture, (k1_relat_1(esk7_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_57])])).
% 3.61/3.81  cnf(c_0_76, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_58, c_0_27])).
% 3.61/3.81  cnf(c_0_77, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 3.61/3.81  fof(c_0_78, plain, ![X46, X47, X48, X49]:(~v1_funct_1(X48)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))|k2_partfun1(X46,X47,X48,X49)=k7_relat_1(X48,X49)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 3.61/3.81  fof(c_0_79, plain, ![X50, X51, X52, X53, X54, X55, X56]:(((k2_partfun1(k4_subset_1(X50,X52,X53),X51,X56,X52)=X54|X56!=k1_tmap_1(X50,X51,X52,X53,X54,X55)|(~v1_funct_1(X56)|~v1_funct_2(X56,k4_subset_1(X50,X52,X53),X51)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X50,X52,X53),X51))))|k2_partfun1(X52,X51,X54,k9_subset_1(X50,X52,X53))!=k2_partfun1(X53,X51,X55,k9_subset_1(X50,X52,X53))|(~v1_funct_1(X55)|~v1_funct_2(X55,X53,X51)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X51))))|(~v1_funct_1(X54)|~v1_funct_2(X54,X52,X51)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X51))))|(v1_xboole_0(X53)|~m1_subset_1(X53,k1_zfmisc_1(X50)))|(v1_xboole_0(X52)|~m1_subset_1(X52,k1_zfmisc_1(X50)))|v1_xboole_0(X51)|v1_xboole_0(X50))&(k2_partfun1(k4_subset_1(X50,X52,X53),X51,X56,X53)=X55|X56!=k1_tmap_1(X50,X51,X52,X53,X54,X55)|(~v1_funct_1(X56)|~v1_funct_2(X56,k4_subset_1(X50,X52,X53),X51)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X50,X52,X53),X51))))|k2_partfun1(X52,X51,X54,k9_subset_1(X50,X52,X53))!=k2_partfun1(X53,X51,X55,k9_subset_1(X50,X52,X53))|(~v1_funct_1(X55)|~v1_funct_2(X55,X53,X51)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X51))))|(~v1_funct_1(X54)|~v1_funct_2(X54,X52,X51)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X51))))|(v1_xboole_0(X53)|~m1_subset_1(X53,k1_zfmisc_1(X50)))|(v1_xboole_0(X52)|~m1_subset_1(X52,k1_zfmisc_1(X50)))|v1_xboole_0(X51)|v1_xboole_0(X50)))&(k2_partfun1(k4_subset_1(X50,X52,X53),X51,X56,X52)!=X54|k2_partfun1(k4_subset_1(X50,X52,X53),X51,X56,X53)!=X55|X56=k1_tmap_1(X50,X51,X52,X53,X54,X55)|(~v1_funct_1(X56)|~v1_funct_2(X56,k4_subset_1(X50,X52,X53),X51)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X50,X52,X53),X51))))|k2_partfun1(X52,X51,X54,k9_subset_1(X50,X52,X53))!=k2_partfun1(X53,X51,X55,k9_subset_1(X50,X52,X53))|(~v1_funct_1(X55)|~v1_funct_2(X55,X53,X51)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X51))))|(~v1_funct_1(X54)|~v1_funct_2(X54,X52,X51)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X51))))|(v1_xboole_0(X53)|~m1_subset_1(X53,k1_zfmisc_1(X50)))|(v1_xboole_0(X52)|~m1_subset_1(X52,k1_zfmisc_1(X50)))|v1_xboole_0(X51)|v1_xboole_0(X50))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tmap_1])])])])])).
% 3.61/3.81  fof(c_0_80, plain, ![X57, X58, X59, X60, X61, X62]:(((v1_funct_1(k1_tmap_1(X57,X58,X59,X60,X61,X62))|(v1_xboole_0(X57)|v1_xboole_0(X58)|v1_xboole_0(X59)|~m1_subset_1(X59,k1_zfmisc_1(X57))|v1_xboole_0(X60)|~m1_subset_1(X60,k1_zfmisc_1(X57))|~v1_funct_1(X61)|~v1_funct_2(X61,X59,X58)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X58)))|~v1_funct_1(X62)|~v1_funct_2(X62,X60,X58)|~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X58)))))&(v1_funct_2(k1_tmap_1(X57,X58,X59,X60,X61,X62),k4_subset_1(X57,X59,X60),X58)|(v1_xboole_0(X57)|v1_xboole_0(X58)|v1_xboole_0(X59)|~m1_subset_1(X59,k1_zfmisc_1(X57))|v1_xboole_0(X60)|~m1_subset_1(X60,k1_zfmisc_1(X57))|~v1_funct_1(X61)|~v1_funct_2(X61,X59,X58)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X58)))|~v1_funct_1(X62)|~v1_funct_2(X62,X60,X58)|~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X58))))))&(m1_subset_1(k1_tmap_1(X57,X58,X59,X60,X61,X62),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X57,X59,X60),X58)))|(v1_xboole_0(X57)|v1_xboole_0(X58)|v1_xboole_0(X59)|~m1_subset_1(X59,k1_zfmisc_1(X57))|v1_xboole_0(X60)|~m1_subset_1(X60,k1_zfmisc_1(X57))|~v1_funct_1(X61)|~v1_funct_2(X61,X59,X58)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X58)))|~v1_funct_1(X62)|~v1_funct_2(X62,X60,X58)|~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X58)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tmap_1])])])])).
% 3.61/3.81  cnf(c_0_81, plain, (k9_subset_1(X2,X3,X1)=k1_setfam_1(k2_tarski(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_61, c_0_62])).
% 3.61/3.81  cnf(c_0_82, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 3.61/3.81  cnf(c_0_83, plain, (r1_xboole_0(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_48, c_0_40])).
% 3.61/3.81  cnf(c_0_84, negated_conjecture, (k1_relat_1(esk6_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_63]), c_0_64]), c_0_65])])).
% 3.61/3.81  cnf(c_0_85, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 3.61/3.81  cnf(c_0_86, plain, (r1_xboole_0(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 3.61/3.81  cnf(c_0_87, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 3.61/3.81  cnf(c_0_88, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_69, c_0_62])).
% 3.61/3.81  cnf(c_0_89, negated_conjecture, (r1_xboole_0(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72]), c_0_73])).
% 3.61/3.81  cnf(c_0_90, negated_conjecture, (k7_relat_1(esk7_0,X1)=k1_xboole_0|~r1_xboole_0(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_57])])).
% 3.61/3.81  cnf(c_0_91, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 3.61/3.81  cnf(c_0_92, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_78])).
% 3.61/3.81  cnf(c_0_93, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X2)=X6|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X4)|v1_xboole_0(X1)|X5!=k1_tmap_1(X1,X4,X2,X3,X6,X7)|~v1_funct_1(X5)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|k2_partfun1(X2,X4,X6,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X7,k9_subset_1(X1,X2,X3))|~v1_funct_1(X7)|~v1_funct_2(X7,X3,X4)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X6)|~v1_funct_2(X6,X2,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_79])).
% 3.61/3.81  cnf(c_0_94, plain, (m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2)))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 3.61/3.81  cnf(c_0_95, plain, (v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 3.61/3.81  cnf(c_0_96, plain, (v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 3.61/3.81  cnf(c_0_97, negated_conjecture, (k9_subset_1(esk2_0,X1,esk5_0)=k1_setfam_1(k2_tarski(X1,esk5_0))), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 3.61/3.81  cnf(c_0_98, plain, (k1_setfam_1(k2_tarski(X1,X2))=k9_subset_1(X2,X1,X2)), inference(spm,[status(thm)],[c_0_81, c_0_67])).
% 3.61/3.81  cnf(c_0_99, plain, (r1_xboole_0(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_83, c_0_67])).
% 3.61/3.81  cnf(c_0_100, negated_conjecture, (k7_relat_1(esk6_0,X1)=k1_xboole_0|~r1_xboole_0(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_84]), c_0_65])])).
% 3.61/3.81  cnf(c_0_101, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 3.61/3.81  cnf(c_0_102, plain, (v1_xboole_0(X1)|~r1_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_87, c_0_50])).
% 3.61/3.81  cnf(c_0_103, negated_conjecture, (k2_partfun1(esk4_0,esk3_0,esk6_0,k9_subset_1(esk2_0,esk4_0,esk5_0))!=k2_partfun1(esk5_0,esk3_0,esk7_0,k9_subset_1(esk2_0,esk4_0,esk5_0))|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0)!=esk6_0|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0)!=esk7_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 3.61/3.81  cnf(c_0_104, negated_conjecture, (k1_setfam_1(k2_tarski(esk4_0,esk5_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 3.61/3.81  cnf(c_0_105, negated_conjecture, (k7_relat_1(esk7_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 3.61/3.81  cnf(c_0_106, negated_conjecture, (k7_relat_1(esk7_0,X1)=k2_partfun1(esk5_0,esk3_0,esk7_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_36]), c_0_35])])).
% 3.61/3.81  cnf(c_0_107, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X2)=X5|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_2(X6,X3,X4)|~v1_funct_2(X5,X2,X4)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_93]), c_0_94]), c_0_95]), c_0_96])).
% 3.61/3.81  cnf(c_0_108, negated_conjecture, (k9_subset_1(esk2_0,X1,esk5_0)=k9_subset_1(esk5_0,X1,esk5_0)), inference(rw,[status(thm)],[c_0_97, c_0_98])).
% 3.61/3.81  cnf(c_0_109, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 3.61/3.81  cnf(c_0_110, negated_conjecture, (k7_relat_1(esk7_0,X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_90, c_0_99])).
% 3.61/3.81  cnf(c_0_111, negated_conjecture, (k7_relat_1(esk6_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_100, c_0_91])).
% 3.61/3.81  cnf(c_0_112, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_101, c_0_101])).
% 3.61/3.81  cnf(c_0_113, plain, (v1_xboole_0(k1_xboole_0)), inference(spm,[status(thm)],[c_0_102, c_0_60])).
% 3.61/3.81  cnf(c_0_114, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X3)=X6|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X4)|v1_xboole_0(X1)|X5!=k1_tmap_1(X1,X4,X2,X3,X7,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|k2_partfun1(X2,X4,X7,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_1(X6)|~v1_funct_2(X6,X3,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X7)|~v1_funct_2(X7,X2,X4)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_79])).
% 3.61/3.81  cnf(c_0_115, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0)!=esk6_0|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0)!=esk7_0|k2_partfun1(esk4_0,esk3_0,esk6_0,k1_xboole_0)!=k2_partfun1(esk5_0,esk3_0,esk7_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_103, c_0_97]), c_0_104]), c_0_97]), c_0_104])).
% 3.61/3.81  cnf(c_0_116, negated_conjecture, (k2_partfun1(esk5_0,esk3_0,esk7_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_105, c_0_106])).
% 3.61/3.81  cnf(c_0_117, negated_conjecture, (k7_relat_1(esk6_0,X1)=k2_partfun1(esk4_0,esk3_0,esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_47]), c_0_46])])).
% 3.61/3.81  cnf(c_0_118, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,X1,esk5_0),X2,k1_tmap_1(esk2_0,X2,X1,esk5_0,X3,X4),X1)=X3|v1_xboole_0(X2)|v1_xboole_0(X1)|k2_partfun1(X1,X2,X3,k9_subset_1(esk5_0,X1,esk5_0))!=k2_partfun1(esk5_0,X2,X4,k9_subset_1(esk5_0,X1,esk5_0))|~v1_funct_2(X4,esk5_0,X2)|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X4)|~v1_funct_1(X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_82])]), c_0_109]), c_0_72])).
% 3.61/3.81  cnf(c_0_119, negated_conjecture, (k2_partfun1(esk5_0,esk3_0,esk7_0,X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_110, c_0_106])).
% 3.61/3.81  cnf(c_0_120, negated_conjecture, (k7_relat_1(esk6_0,X1)=X1|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_113])])).
% 3.61/3.81  cnf(c_0_121, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X3)=X6|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_2(X5,X2,X4)|~v1_funct_2(X6,X3,X4)|~v1_funct_1(X5)|~v1_funct_1(X6)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_114]), c_0_94]), c_0_95]), c_0_96])).
% 3.61/3.81  cnf(c_0_122, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0)!=esk6_0|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0)!=esk7_0|k2_partfun1(esk4_0,esk3_0,esk6_0,k1_xboole_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_115, c_0_116])).
% 3.61/3.81  cnf(c_0_123, negated_conjecture, (k2_partfun1(esk4_0,esk3_0,esk6_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_111, c_0_117])).
% 3.61/3.81  cnf(c_0_124, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,X1,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,X1,esk5_0,X2,esk7_0),X1)=X2|v1_xboole_0(X1)|k2_partfun1(X1,esk3_0,X2,k9_subset_1(esk5_0,X1,esk5_0))!=k1_xboole_0|~v1_funct_2(X2,X1,esk3_0)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))|~v1_xboole_0(k9_subset_1(esk5_0,X1,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_119]), c_0_34]), c_0_35]), c_0_36])]), c_0_37])).
% 3.61/3.81  cnf(c_0_125, negated_conjecture, (k2_partfun1(esk4_0,esk3_0,esk6_0,X1)=X1|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_120, c_0_117])).
% 3.61/3.81  cnf(c_0_126, negated_conjecture, (k9_subset_1(esk5_0,esk4_0,esk5_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_104, c_0_98])).
% 3.61/3.81  cnf(c_0_127, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 3.61/3.81  cnf(c_0_128, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,X1,esk5_0),X2,k1_tmap_1(esk2_0,X2,X1,esk5_0,X3,X4),esk5_0)=X4|v1_xboole_0(X2)|v1_xboole_0(X1)|k2_partfun1(X1,X2,X3,k9_subset_1(esk5_0,X1,esk5_0))!=k2_partfun1(esk5_0,X2,X4,k9_subset_1(esk5_0,X1,esk5_0))|~v1_funct_2(X4,esk5_0,X2)|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_108]), c_0_82])]), c_0_109]), c_0_72])).
% 3.61/3.81  cnf(c_0_129, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0)!=esk6_0|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0)!=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_122, c_0_123])])).
% 3.61/3.81  cnf(c_0_130, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0)=esk6_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_125]), c_0_126]), c_0_45]), c_0_46]), c_0_47]), c_0_127]), c_0_126]), c_0_113])]), c_0_73])).
% 3.61/3.81  cnf(c_0_131, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,X1,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,X1,esk5_0,X2,esk7_0),esk5_0)=esk7_0|v1_xboole_0(X1)|k2_partfun1(X1,esk3_0,X2,k9_subset_1(esk5_0,X1,esk5_0))!=k1_xboole_0|~v1_funct_2(X2,X1,esk3_0)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))|~v1_xboole_0(k9_subset_1(esk5_0,X1,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_119]), c_0_34]), c_0_35]), c_0_36])]), c_0_37])).
% 3.61/3.81  cnf(c_0_132, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0)!=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_129, c_0_130])])).
% 3.61/3.81  cnf(c_0_133, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_125]), c_0_126]), c_0_45]), c_0_46]), c_0_47]), c_0_127]), c_0_126]), c_0_113])]), c_0_132]), c_0_73]), ['proof']).
% 3.61/3.81  # SZS output end CNFRefutation
% 3.61/3.81  # Proof object total steps             : 134
% 3.61/3.81  # Proof object clause steps            : 95
% 3.61/3.81  # Proof object formula steps           : 39
% 3.61/3.81  # Proof object conjectures             : 52
% 3.61/3.81  # Proof object clause conjectures      : 49
% 3.61/3.81  # Proof object formula conjectures     : 3
% 3.61/3.81  # Proof object initial clauses used    : 38
% 3.61/3.81  # Proof object initial formulas used   : 19
% 3.61/3.81  # Proof object generating inferences   : 43
% 3.61/3.81  # Proof object simplifying inferences  : 88
% 3.61/3.81  # Training examples: 0 positive, 0 negative
% 3.61/3.81  # Parsed axioms                        : 19
% 3.61/3.81  # Removed by relevancy pruning/SinE    : 0
% 3.61/3.81  # Initial clauses                      : 47
% 3.61/3.81  # Removed in clause preprocessing      : 2
% 3.61/3.81  # Initial clauses in saturation        : 45
% 3.61/3.81  # Processed clauses                    : 23744
% 3.61/3.81  # ...of these trivial                  : 11
% 3.61/3.81  # ...subsumed                          : 19941
% 3.61/3.81  # ...remaining for further processing  : 3792
% 3.61/3.81  # Other redundant clauses eliminated   : 3908
% 3.61/3.81  # Clauses deleted for lack of memory   : 0
% 3.61/3.81  # Backward-subsumed                    : 102
% 3.61/3.81  # Backward-rewritten                   : 71
% 3.61/3.81  # Generated clauses                    : 168542
% 3.61/3.81  # ...of the previous two non-trivial   : 151887
% 3.61/3.81  # Contextual simplify-reflections      : 40
% 3.61/3.81  # Paramodulations                      : 164513
% 3.61/3.81  # Factorizations                       : 0
% 3.61/3.81  # Equation resolutions                 : 4030
% 3.61/3.81  # Propositional unsat checks           : 0
% 3.61/3.81  #    Propositional check models        : 0
% 3.61/3.81  #    Propositional check unsatisfiable : 0
% 3.61/3.81  #    Propositional clauses             : 0
% 3.61/3.81  #    Propositional clauses after purity: 0
% 3.61/3.81  #    Propositional unsat core size     : 0
% 3.61/3.81  #    Propositional preprocessing time  : 0.000
% 3.61/3.81  #    Propositional encoding time       : 0.000
% 3.61/3.81  #    Propositional solver time         : 0.000
% 3.61/3.81  #    Success case prop preproc time    : 0.000
% 3.61/3.81  #    Success case prop encoding time   : 0.000
% 3.61/3.81  #    Success case prop solver time     : 0.000
% 3.61/3.81  # Current number of processed clauses  : 3568
% 3.61/3.81  #    Positive orientable unit clauses  : 130
% 3.61/3.81  #    Positive unorientable unit clauses: 0
% 3.61/3.81  #    Negative unit clauses             : 7
% 3.61/3.81  #    Non-unit-clauses                  : 3431
% 3.61/3.81  # Current number of unprocessed clauses: 127978
% 3.61/3.81  # ...number of literals in the above   : 1228355
% 3.61/3.81  # Current number of archived formulas  : 0
% 3.61/3.81  # Current number of archived clauses   : 218
% 3.61/3.81  # Clause-clause subsumption calls (NU) : 8137992
% 3.61/3.81  # Rec. Clause-clause subsumption calls : 1243773
% 3.61/3.81  # Non-unit clause-clause subsumptions  : 15274
% 3.61/3.81  # Unit Clause-clause subsumption calls : 41573
% 3.61/3.81  # Rewrite failures with RHS unbound    : 0
% 3.61/3.81  # BW rewrite match attempts            : 296
% 3.61/3.81  # BW rewrite match successes           : 27
% 3.61/3.81  # Condensation attempts                : 0
% 3.61/3.81  # Condensation successes               : 0
% 3.61/3.81  # Termbank termtop insertions          : 7933022
% 3.61/3.82  
% 3.61/3.82  # -------------------------------------------------
% 3.61/3.82  # User time                : 3.396 s
% 3.61/3.82  # System time              : 0.083 s
% 3.61/3.82  # Total time               : 3.478 s
% 3.61/3.82  # Maximum resident set size: 1612 pages
%------------------------------------------------------------------------------
