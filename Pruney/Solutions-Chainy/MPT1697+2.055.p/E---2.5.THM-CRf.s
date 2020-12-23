%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:42 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 587 expanded)
%              Number of clauses        :   60 ( 220 expanded)
%              Number of leaves         :   15 ( 145 expanded)
%              Depth                    :   12
%              Number of atoms          :  493 (5077 expanded)
%              Number of equality atoms :   79 ( 858 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal clause size      :   55 (   4 average)
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

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

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

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

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

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

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
    ! [X32,X33,X34] :
      ( ( v1_funct_1(X34)
        | ~ v1_funct_1(X34)
        | ~ v1_funct_2(X34,X32,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
        | v1_xboole_0(X33) )
      & ( v1_partfun1(X34,X32)
        | ~ v1_funct_1(X34)
        | ~ v1_funct_2(X34,X32,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
        | v1_xboole_0(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

fof(c_0_17,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

fof(c_0_18,plain,(
    ! [X29,X30,X31] :
      ( ( v4_relat_1(X31,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( v5_relat_1(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_19,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | v1_relat_1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_20,plain,(
    ! [X35,X36] :
      ( ( ~ v1_partfun1(X36,X35)
        | k1_relat_1(X36) = X35
        | ~ v1_relat_1(X36)
        | ~ v4_relat_1(X36,X35) )
      & ( k1_relat_1(X36) != X35
        | v1_partfun1(X36,X35)
        | ~ v1_relat_1(X36)
        | ~ v4_relat_1(X36,X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

cnf(c_0_21,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_28,plain,(
    ! [X24,X25] :
      ( ~ r2_hidden(X24,X25)
      | ~ r1_tarski(X25,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_29,plain,(
    ! [X16] : r1_tarski(k1_xboole_0,X16) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_30,plain,(
    ! [X41,X42,X43,X44,X45,X46,X47] :
      ( ( k2_partfun1(k4_subset_1(X41,X43,X44),X42,X47,X43) = X45
        | X47 != k1_tmap_1(X41,X42,X43,X44,X45,X46)
        | ~ v1_funct_1(X47)
        | ~ v1_funct_2(X47,k4_subset_1(X41,X43,X44),X42)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X41,X43,X44),X42)))
        | k2_partfun1(X43,X42,X45,k9_subset_1(X41,X43,X44)) != k2_partfun1(X44,X42,X46,k9_subset_1(X41,X43,X44))
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,X44,X42)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X42)))
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,X43,X42)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X42)))
        | v1_xboole_0(X44)
        | ~ m1_subset_1(X44,k1_zfmisc_1(X41))
        | v1_xboole_0(X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(X41))
        | v1_xboole_0(X42)
        | v1_xboole_0(X41) )
      & ( k2_partfun1(k4_subset_1(X41,X43,X44),X42,X47,X44) = X46
        | X47 != k1_tmap_1(X41,X42,X43,X44,X45,X46)
        | ~ v1_funct_1(X47)
        | ~ v1_funct_2(X47,k4_subset_1(X41,X43,X44),X42)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X41,X43,X44),X42)))
        | k2_partfun1(X43,X42,X45,k9_subset_1(X41,X43,X44)) != k2_partfun1(X44,X42,X46,k9_subset_1(X41,X43,X44))
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,X44,X42)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X42)))
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,X43,X42)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X42)))
        | v1_xboole_0(X44)
        | ~ m1_subset_1(X44,k1_zfmisc_1(X41))
        | v1_xboole_0(X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(X41))
        | v1_xboole_0(X42)
        | v1_xboole_0(X41) )
      & ( k2_partfun1(k4_subset_1(X41,X43,X44),X42,X47,X43) != X45
        | k2_partfun1(k4_subset_1(X41,X43,X44),X42,X47,X44) != X46
        | X47 = k1_tmap_1(X41,X42,X43,X44,X45,X46)
        | ~ v1_funct_1(X47)
        | ~ v1_funct_2(X47,k4_subset_1(X41,X43,X44),X42)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X41,X43,X44),X42)))
        | k2_partfun1(X43,X42,X45,k9_subset_1(X41,X43,X44)) != k2_partfun1(X44,X42,X46,k9_subset_1(X41,X43,X44))
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,X44,X42)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X42)))
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,X43,X42)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X42)))
        | v1_xboole_0(X44)
        | ~ m1_subset_1(X44,k1_zfmisc_1(X41))
        | v1_xboole_0(X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(X41))
        | v1_xboole_0(X42)
        | v1_xboole_0(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tmap_1])])])])])).

fof(c_0_31,plain,(
    ! [X48,X49,X50,X51,X52,X53] :
      ( ( v1_funct_1(k1_tmap_1(X48,X49,X50,X51,X52,X53))
        | v1_xboole_0(X48)
        | v1_xboole_0(X49)
        | v1_xboole_0(X50)
        | ~ m1_subset_1(X50,k1_zfmisc_1(X48))
        | v1_xboole_0(X51)
        | ~ m1_subset_1(X51,k1_zfmisc_1(X48))
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,X50,X49)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X49)))
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,X51,X49)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X49))) )
      & ( v1_funct_2(k1_tmap_1(X48,X49,X50,X51,X52,X53),k4_subset_1(X48,X50,X51),X49)
        | v1_xboole_0(X48)
        | v1_xboole_0(X49)
        | v1_xboole_0(X50)
        | ~ m1_subset_1(X50,k1_zfmisc_1(X48))
        | v1_xboole_0(X51)
        | ~ m1_subset_1(X51,k1_zfmisc_1(X48))
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,X50,X49)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X49)))
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,X51,X49)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X49))) )
      & ( m1_subset_1(k1_tmap_1(X48,X49,X50,X51,X52,X53),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X48,X50,X51),X49)))
        | v1_xboole_0(X48)
        | v1_xboole_0(X49)
        | v1_xboole_0(X50)
        | ~ m1_subset_1(X50,k1_zfmisc_1(X48))
        | v1_xboole_0(X51)
        | ~ m1_subset_1(X51,k1_zfmisc_1(X48))
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,X50,X49)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X49)))
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,X51,X49)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X49))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tmap_1])])])])).

fof(c_0_32,plain,(
    ! [X17,X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(X17))
      | k9_subset_1(X17,X18,X19) = k3_xboole_0(X18,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_33,plain,(
    ! [X22,X23] :
      ( ( ~ r1_subset_1(X22,X23)
        | r1_xboole_0(X22,X23)
        | v1_xboole_0(X22)
        | v1_xboole_0(X23) )
      & ( ~ r1_xboole_0(X22,X23)
        | r1_subset_1(X22,X23)
        | v1_xboole_0(X22)
        | v1_xboole_0(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).

fof(c_0_34,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X20)
      | ~ r1_xboole_0(X21,k1_relat_1(X20))
      | k7_relat_1(X20,X21) = k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t187_relat_1])])])).

cnf(c_0_35,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_36,negated_conjecture,
    ( v1_partfun1(esk6_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_37,negated_conjecture,
    ( v4_relat_1(esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_24])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_24])).

cnf(c_0_39,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_41,plain,(
    ! [X10,X11,X13,X14,X15] :
      ( ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_2(X10,X11),X11)
        | r1_xboole_0(X10,X11) )
      & ( ~ r2_hidden(X15,X13)
        | ~ r2_hidden(X15,X14)
        | ~ r1_xboole_0(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_42,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_45,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_46,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_48,plain,(
    ! [X8,X9] :
      ( ( ~ r1_xboole_0(X8,X9)
        | k3_xboole_0(X8,X9) = k1_xboole_0 )
      & ( k3_xboole_0(X8,X9) != k1_xboole_0
        | r1_xboole_0(X8,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_49,plain,
    ( r1_xboole_0(X1,X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_50,negated_conjecture,
    ( r1_subset_1(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_51,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_53,plain,
    ( k7_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_54,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38])])).

cnf(c_0_55,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_56,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_57,plain,(
    ! [X37,X38,X39,X40] :
      ( ~ v1_funct_1(X39)
      | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
      | k2_partfun1(X37,X38,X39,X40) = k7_relat_1(X39,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

cnf(c_0_58,plain,
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
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_42]),c_0_43]),c_0_44]),c_0_45])).

cnf(c_0_59,negated_conjecture,
    ( k9_subset_1(esk2_0,X1,esk5_0) = k3_xboole_0(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_60,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_61,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_62,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_52])).

cnf(c_0_63,negated_conjecture,
    ( k7_relat_1(esk6_0,X1) = k1_xboole_0
    | ~ r1_xboole_0(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_38])])).

cnf(c_0_64,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_65,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_66,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_68,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_69,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,X1,esk5_0),X2,k1_tmap_1(esk2_0,X2,X1,esk5_0,X3,X4),X1) = X3
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X3,k3_xboole_0(X1,esk5_0)) != k2_partfun1(esk5_0,X2,X4,k3_xboole_0(X1,esk5_0))
    | ~ v1_funct_2(X4,esk5_0,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_47])]),c_0_60]),c_0_51])).

cnf(c_0_70,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_72,negated_conjecture,
    ( k7_relat_1(esk6_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_73,negated_conjecture,
    ( k7_relat_1(esk6_0,X1) = k2_partfun1(esk4_0,esk3_0,esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_24]),c_0_23])])).

cnf(c_0_74,plain,
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
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_66]),c_0_43]),c_0_44]),c_0_45])).

cnf(c_0_75,plain,
    ( k7_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_64])).

cnf(c_0_76,negated_conjecture,
    ( k7_relat_1(esk7_0,X1) = k2_partfun1(esk5_0,esk3_0,esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_67]),c_0_68])])).

cnf(c_0_77,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_67])).

cnf(c_0_78,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),X1,k1_tmap_1(esk2_0,X1,esk4_0,esk5_0,X2,X3),esk4_0) = X2
    | v1_xboole_0(X1)
    | k2_partfun1(esk4_0,X1,X2,k1_xboole_0) != k2_partfun1(esk5_0,X1,X3,k1_xboole_0)
    | ~ v1_funct_2(X3,esk5_0,X1)
    | ~ v1_funct_2(X2,esk4_0,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])]),c_0_52])).

cnf(c_0_79,negated_conjecture,
    ( k2_partfun1(esk4_0,esk3_0,esk6_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_80,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,X1,esk5_0),X2,k1_tmap_1(esk2_0,X2,X1,esk5_0,X3,X4),esk5_0) = X4
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X3,k3_xboole_0(X1,esk5_0)) != k2_partfun1(esk5_0,X2,X4,k3_xboole_0(X1,esk5_0))
    | ~ v1_funct_2(X4,esk5_0,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_59]),c_0_47])]),c_0_60]),c_0_51])).

cnf(c_0_81,negated_conjecture,
    ( k2_partfun1(esk4_0,esk3_0,esk6_0,k9_subset_1(esk2_0,esk4_0,esk5_0)) != k2_partfun1(esk5_0,esk3_0,esk7_0,k9_subset_1(esk2_0,esk4_0,esk5_0))
    | k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0) != esk6_0
    | k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0) != esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_82,negated_conjecture,
    ( k2_partfun1(esk5_0,esk3_0,esk7_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77])])).

cnf(c_0_83,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,X1),esk4_0) = esk6_0
    | k2_partfun1(esk5_0,esk3_0,X1,k1_xboole_0) != k1_xboole_0
    | ~ v1_funct_2(X1,esk5_0,esk3_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_22]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_84,negated_conjecture,
    ( v1_funct_2(esk7_0,esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_85,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),X1,k1_tmap_1(esk2_0,X1,esk4_0,esk5_0,X2,X3),esk5_0) = X3
    | v1_xboole_0(X1)
    | k2_partfun1(esk4_0,X1,X2,k1_xboole_0) != k2_partfun1(esk5_0,X1,X3,k1_xboole_0)
    | ~ v1_funct_2(X3,esk5_0,X1)
    | ~ v1_funct_2(X2,esk4_0,X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_70]),c_0_71])]),c_0_52])).

cnf(c_0_86,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0) != esk6_0
    | k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0) != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_59]),c_0_70]),c_0_79]),c_0_59]),c_0_70]),c_0_82])])).

cnf(c_0_87,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_82]),c_0_84]),c_0_68]),c_0_67])])).

cnf(c_0_88,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,X1),esk5_0) = X1
    | k2_partfun1(esk5_0,esk3_0,X1,k1_xboole_0) != k1_xboole_0
    | ~ v1_funct_2(X1,esk5_0,esk3_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_79]),c_0_22]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_89,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0) != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_87])])).

cnf(c_0_90,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_82]),c_0_84]),c_0_68]),c_0_67])]),c_0_89]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:26:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.19/0.41  # and selection function SelectCQIPrecWNTNp.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.029 s
% 0.19/0.41  # Presaturation interreduction done
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(t6_tmap_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>(r1_subset_1(X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3)=X5)&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4)=X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 0.19/0.41  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.19/0.41  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.41  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.41  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 0.19/0.41  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.19/0.41  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.41  fof(d1_tmap_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>(k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))=>![X7]:(((v1_funct_1(X7)&v1_funct_2(X7,k4_subset_1(X1,X3,X4),X2))&m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))))=>(X7=k1_tmap_1(X1,X2,X3,X4,X5,X6)<=>(k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X3)=X5&k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X4)=X6)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 0.19/0.41  fof(dt_k1_tmap_1, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((((((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))&~(v1_xboole_0(X3)))&m1_subset_1(X3,k1_zfmisc_1(X1)))&~(v1_xboole_0(X4)))&m1_subset_1(X4,k1_zfmisc_1(X1)))&v1_funct_1(X5))&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2))&m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 0.19/0.41  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.19/0.41  fof(redefinition_r1_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))=>(r1_subset_1(X1,X2)<=>r1_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 0.19/0.41  fof(t187_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_xboole_0(X2,k1_relat_1(X1))=>k7_relat_1(X1,X2)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 0.19/0.41  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.19/0.41  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.19/0.41  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 0.19/0.41  fof(c_0_15, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>(r1_subset_1(X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3)=X5)&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4)=X6))))))))), inference(assume_negation,[status(cth)],[t6_tmap_1])).
% 0.19/0.41  fof(c_0_16, plain, ![X32, X33, X34]:((v1_funct_1(X34)|(~v1_funct_1(X34)|~v1_funct_2(X34,X32,X33))|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|v1_xboole_0(X33))&(v1_partfun1(X34,X32)|(~v1_funct_1(X34)|~v1_funct_2(X34,X32,X33))|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|v1_xboole_0(X33))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.19/0.41  fof(c_0_17, negated_conjecture, (~v1_xboole_0(esk2_0)&(~v1_xboole_0(esk3_0)&((~v1_xboole_0(esk4_0)&m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)))&((~v1_xboole_0(esk5_0)&m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0)))&(r1_subset_1(esk4_0,esk5_0)&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk4_0,esk3_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))))&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk5_0,esk3_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0))))&(k2_partfun1(esk4_0,esk3_0,esk6_0,k9_subset_1(esk2_0,esk4_0,esk5_0))!=k2_partfun1(esk5_0,esk3_0,esk7_0,k9_subset_1(esk2_0,esk4_0,esk5_0))|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0)!=esk6_0|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0)!=esk7_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.19/0.41  fof(c_0_18, plain, ![X29, X30, X31]:((v4_relat_1(X31,X29)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))&(v5_relat_1(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.41  fof(c_0_19, plain, ![X26, X27, X28]:(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|v1_relat_1(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.41  fof(c_0_20, plain, ![X35, X36]:((~v1_partfun1(X36,X35)|k1_relat_1(X36)=X35|(~v1_relat_1(X36)|~v4_relat_1(X36,X35)))&(k1_relat_1(X36)!=X35|v1_partfun1(X36,X35)|(~v1_relat_1(X36)|~v4_relat_1(X36,X35)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 0.19/0.41  cnf(c_0_21, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.41  cnf(c_0_22, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  cnf(c_0_23, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  cnf(c_0_25, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  cnf(c_0_26, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  cnf(c_0_27, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  fof(c_0_28, plain, ![X24, X25]:(~r2_hidden(X24,X25)|~r1_tarski(X25,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.19/0.41  fof(c_0_29, plain, ![X16]:r1_tarski(k1_xboole_0,X16), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.41  fof(c_0_30, plain, ![X41, X42, X43, X44, X45, X46, X47]:(((k2_partfun1(k4_subset_1(X41,X43,X44),X42,X47,X43)=X45|X47!=k1_tmap_1(X41,X42,X43,X44,X45,X46)|(~v1_funct_1(X47)|~v1_funct_2(X47,k4_subset_1(X41,X43,X44),X42)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X41,X43,X44),X42))))|k2_partfun1(X43,X42,X45,k9_subset_1(X41,X43,X44))!=k2_partfun1(X44,X42,X46,k9_subset_1(X41,X43,X44))|(~v1_funct_1(X46)|~v1_funct_2(X46,X44,X42)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X42))))|(~v1_funct_1(X45)|~v1_funct_2(X45,X43,X42)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X42))))|(v1_xboole_0(X44)|~m1_subset_1(X44,k1_zfmisc_1(X41)))|(v1_xboole_0(X43)|~m1_subset_1(X43,k1_zfmisc_1(X41)))|v1_xboole_0(X42)|v1_xboole_0(X41))&(k2_partfun1(k4_subset_1(X41,X43,X44),X42,X47,X44)=X46|X47!=k1_tmap_1(X41,X42,X43,X44,X45,X46)|(~v1_funct_1(X47)|~v1_funct_2(X47,k4_subset_1(X41,X43,X44),X42)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X41,X43,X44),X42))))|k2_partfun1(X43,X42,X45,k9_subset_1(X41,X43,X44))!=k2_partfun1(X44,X42,X46,k9_subset_1(X41,X43,X44))|(~v1_funct_1(X46)|~v1_funct_2(X46,X44,X42)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X42))))|(~v1_funct_1(X45)|~v1_funct_2(X45,X43,X42)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X42))))|(v1_xboole_0(X44)|~m1_subset_1(X44,k1_zfmisc_1(X41)))|(v1_xboole_0(X43)|~m1_subset_1(X43,k1_zfmisc_1(X41)))|v1_xboole_0(X42)|v1_xboole_0(X41)))&(k2_partfun1(k4_subset_1(X41,X43,X44),X42,X47,X43)!=X45|k2_partfun1(k4_subset_1(X41,X43,X44),X42,X47,X44)!=X46|X47=k1_tmap_1(X41,X42,X43,X44,X45,X46)|(~v1_funct_1(X47)|~v1_funct_2(X47,k4_subset_1(X41,X43,X44),X42)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X41,X43,X44),X42))))|k2_partfun1(X43,X42,X45,k9_subset_1(X41,X43,X44))!=k2_partfun1(X44,X42,X46,k9_subset_1(X41,X43,X44))|(~v1_funct_1(X46)|~v1_funct_2(X46,X44,X42)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X42))))|(~v1_funct_1(X45)|~v1_funct_2(X45,X43,X42)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X42))))|(v1_xboole_0(X44)|~m1_subset_1(X44,k1_zfmisc_1(X41)))|(v1_xboole_0(X43)|~m1_subset_1(X43,k1_zfmisc_1(X41)))|v1_xboole_0(X42)|v1_xboole_0(X41))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tmap_1])])])])])).
% 0.19/0.41  fof(c_0_31, plain, ![X48, X49, X50, X51, X52, X53]:(((v1_funct_1(k1_tmap_1(X48,X49,X50,X51,X52,X53))|(v1_xboole_0(X48)|v1_xboole_0(X49)|v1_xboole_0(X50)|~m1_subset_1(X50,k1_zfmisc_1(X48))|v1_xboole_0(X51)|~m1_subset_1(X51,k1_zfmisc_1(X48))|~v1_funct_1(X52)|~v1_funct_2(X52,X50,X49)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X49)))|~v1_funct_1(X53)|~v1_funct_2(X53,X51,X49)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X49)))))&(v1_funct_2(k1_tmap_1(X48,X49,X50,X51,X52,X53),k4_subset_1(X48,X50,X51),X49)|(v1_xboole_0(X48)|v1_xboole_0(X49)|v1_xboole_0(X50)|~m1_subset_1(X50,k1_zfmisc_1(X48))|v1_xboole_0(X51)|~m1_subset_1(X51,k1_zfmisc_1(X48))|~v1_funct_1(X52)|~v1_funct_2(X52,X50,X49)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X49)))|~v1_funct_1(X53)|~v1_funct_2(X53,X51,X49)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X49))))))&(m1_subset_1(k1_tmap_1(X48,X49,X50,X51,X52,X53),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X48,X50,X51),X49)))|(v1_xboole_0(X48)|v1_xboole_0(X49)|v1_xboole_0(X50)|~m1_subset_1(X50,k1_zfmisc_1(X48))|v1_xboole_0(X51)|~m1_subset_1(X51,k1_zfmisc_1(X48))|~v1_funct_1(X52)|~v1_funct_2(X52,X50,X49)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X49)))|~v1_funct_1(X53)|~v1_funct_2(X53,X51,X49)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X49)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tmap_1])])])])).
% 0.19/0.41  fof(c_0_32, plain, ![X17, X18, X19]:(~m1_subset_1(X19,k1_zfmisc_1(X17))|k9_subset_1(X17,X18,X19)=k3_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.19/0.41  fof(c_0_33, plain, ![X22, X23]:((~r1_subset_1(X22,X23)|r1_xboole_0(X22,X23)|(v1_xboole_0(X22)|v1_xboole_0(X23)))&(~r1_xboole_0(X22,X23)|r1_subset_1(X22,X23)|(v1_xboole_0(X22)|v1_xboole_0(X23)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).
% 0.19/0.41  fof(c_0_34, plain, ![X20, X21]:(~v1_relat_1(X20)|(~r1_xboole_0(X21,k1_relat_1(X20))|k7_relat_1(X20,X21)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t187_relat_1])])])).
% 0.19/0.41  cnf(c_0_35, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.41  cnf(c_0_36, negated_conjecture, (v1_partfun1(esk6_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24])]), c_0_25])).
% 0.19/0.41  cnf(c_0_37, negated_conjecture, (v4_relat_1(esk6_0,esk4_0)), inference(spm,[status(thm)],[c_0_26, c_0_24])).
% 0.19/0.41  cnf(c_0_38, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_27, c_0_24])).
% 0.19/0.41  cnf(c_0_39, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.41  cnf(c_0_40, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.41  fof(c_0_41, plain, ![X10, X11, X13, X14, X15]:(((r2_hidden(esk1_2(X10,X11),X10)|r1_xboole_0(X10,X11))&(r2_hidden(esk1_2(X10,X11),X11)|r1_xboole_0(X10,X11)))&(~r2_hidden(X15,X13)|~r2_hidden(X15,X14)|~r1_xboole_0(X13,X14))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.19/0.41  cnf(c_0_42, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X2)=X6|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X4)|v1_xboole_0(X1)|X5!=k1_tmap_1(X1,X4,X2,X3,X6,X7)|~v1_funct_1(X5)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|k2_partfun1(X2,X4,X6,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X7,k9_subset_1(X1,X2,X3))|~v1_funct_1(X7)|~v1_funct_2(X7,X3,X4)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X6)|~v1_funct_2(X6,X2,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.41  cnf(c_0_43, plain, (m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2)))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.41  cnf(c_0_44, plain, (v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.41  cnf(c_0_45, plain, (v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.41  cnf(c_0_46, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.41  cnf(c_0_47, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  fof(c_0_48, plain, ![X8, X9]:((~r1_xboole_0(X8,X9)|k3_xboole_0(X8,X9)=k1_xboole_0)&(k3_xboole_0(X8,X9)!=k1_xboole_0|r1_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.19/0.41  cnf(c_0_49, plain, (r1_xboole_0(X1,X2)|v1_xboole_0(X1)|v1_xboole_0(X2)|~r1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.41  cnf(c_0_50, negated_conjecture, (r1_subset_1(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  cnf(c_0_51, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  cnf(c_0_52, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  cnf(c_0_53, plain, (k7_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.41  cnf(c_0_54, negated_conjecture, (k1_relat_1(esk6_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38])])).
% 0.19/0.41  cnf(c_0_55, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.41  cnf(c_0_56, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.41  fof(c_0_57, plain, ![X37, X38, X39, X40]:(~v1_funct_1(X39)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))|k2_partfun1(X37,X38,X39,X40)=k7_relat_1(X39,X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 0.19/0.41  cnf(c_0_58, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X2)=X5|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_2(X6,X3,X4)|~v1_funct_2(X5,X2,X4)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_42]), c_0_43]), c_0_44]), c_0_45])).
% 0.19/0.41  cnf(c_0_59, negated_conjecture, (k9_subset_1(esk2_0,X1,esk5_0)=k3_xboole_0(X1,esk5_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.41  cnf(c_0_60, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  cnf(c_0_61, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.41  cnf(c_0_62, negated_conjecture, (r1_xboole_0(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_52])).
% 0.19/0.41  cnf(c_0_63, negated_conjecture, (k7_relat_1(esk6_0,X1)=k1_xboole_0|~r1_xboole_0(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_38])])).
% 0.19/0.41  cnf(c_0_64, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.19/0.41  cnf(c_0_65, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.41  cnf(c_0_66, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X3)=X6|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X4)|v1_xboole_0(X1)|X5!=k1_tmap_1(X1,X4,X2,X3,X7,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|k2_partfun1(X2,X4,X7,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_1(X6)|~v1_funct_2(X6,X3,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X7)|~v1_funct_2(X7,X2,X4)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.41  cnf(c_0_67, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  cnf(c_0_68, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  cnf(c_0_69, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,X1,esk5_0),X2,k1_tmap_1(esk2_0,X2,X1,esk5_0,X3,X4),X1)=X3|v1_xboole_0(X2)|v1_xboole_0(X1)|k2_partfun1(X1,X2,X3,k3_xboole_0(X1,esk5_0))!=k2_partfun1(esk5_0,X2,X4,k3_xboole_0(X1,esk5_0))|~v1_funct_2(X4,esk5_0,X2)|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X4)|~v1_funct_1(X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_47])]), c_0_60]), c_0_51])).
% 0.19/0.41  cnf(c_0_70, negated_conjecture, (k3_xboole_0(esk4_0,esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.19/0.41  cnf(c_0_71, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  cnf(c_0_72, negated_conjecture, (k7_relat_1(esk6_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.19/0.41  cnf(c_0_73, negated_conjecture, (k7_relat_1(esk6_0,X1)=k2_partfun1(esk4_0,esk3_0,esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_24]), c_0_23])])).
% 0.19/0.41  cnf(c_0_74, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X3)=X6|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_2(X5,X2,X4)|~v1_funct_2(X6,X3,X4)|~v1_funct_1(X5)|~v1_funct_1(X6)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_66]), c_0_43]), c_0_44]), c_0_45])).
% 0.19/0.41  cnf(c_0_75, plain, (k7_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_53, c_0_64])).
% 0.19/0.41  cnf(c_0_76, negated_conjecture, (k7_relat_1(esk7_0,X1)=k2_partfun1(esk5_0,esk3_0,esk7_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_67]), c_0_68])])).
% 0.19/0.41  cnf(c_0_77, negated_conjecture, (v1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_27, c_0_67])).
% 0.19/0.41  cnf(c_0_78, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),X1,k1_tmap_1(esk2_0,X1,esk4_0,esk5_0,X2,X3),esk4_0)=X2|v1_xboole_0(X1)|k2_partfun1(esk4_0,X1,X2,k1_xboole_0)!=k2_partfun1(esk5_0,X1,X3,k1_xboole_0)|~v1_funct_2(X3,esk5_0,X1)|~v1_funct_2(X2,esk4_0,X1)|~v1_funct_1(X3)|~v1_funct_1(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])]), c_0_52])).
% 0.19/0.41  cnf(c_0_79, negated_conjecture, (k2_partfun1(esk4_0,esk3_0,esk6_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_72, c_0_73])).
% 0.19/0.41  cnf(c_0_80, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,X1,esk5_0),X2,k1_tmap_1(esk2_0,X2,X1,esk5_0,X3,X4),esk5_0)=X4|v1_xboole_0(X2)|v1_xboole_0(X1)|k2_partfun1(X1,X2,X3,k3_xboole_0(X1,esk5_0))!=k2_partfun1(esk5_0,X2,X4,k3_xboole_0(X1,esk5_0))|~v1_funct_2(X4,esk5_0,X2)|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_59]), c_0_47])]), c_0_60]), c_0_51])).
% 0.19/0.41  cnf(c_0_81, negated_conjecture, (k2_partfun1(esk4_0,esk3_0,esk6_0,k9_subset_1(esk2_0,esk4_0,esk5_0))!=k2_partfun1(esk5_0,esk3_0,esk7_0,k9_subset_1(esk2_0,esk4_0,esk5_0))|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0)!=esk6_0|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0)!=esk7_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  cnf(c_0_82, negated_conjecture, (k2_partfun1(esk5_0,esk3_0,esk7_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77])])).
% 0.19/0.41  cnf(c_0_83, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,X1),esk4_0)=esk6_0|k2_partfun1(esk5_0,esk3_0,X1,k1_xboole_0)!=k1_xboole_0|~v1_funct_2(X1,esk5_0,esk3_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_22]), c_0_23]), c_0_24])]), c_0_25])).
% 0.19/0.41  cnf(c_0_84, negated_conjecture, (v1_funct_2(esk7_0,esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  cnf(c_0_85, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),X1,k1_tmap_1(esk2_0,X1,esk4_0,esk5_0,X2,X3),esk5_0)=X3|v1_xboole_0(X1)|k2_partfun1(esk4_0,X1,X2,k1_xboole_0)!=k2_partfun1(esk5_0,X1,X3,k1_xboole_0)|~v1_funct_2(X3,esk5_0,X1)|~v1_funct_2(X2,esk4_0,X1)|~v1_funct_1(X2)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_70]), c_0_71])]), c_0_52])).
% 0.19/0.41  cnf(c_0_86, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0)!=esk6_0|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0)!=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_59]), c_0_70]), c_0_79]), c_0_59]), c_0_70]), c_0_82])])).
% 0.19/0.41  cnf(c_0_87, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0)=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_82]), c_0_84]), c_0_68]), c_0_67])])).
% 0.19/0.41  cnf(c_0_88, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,X1),esk5_0)=X1|k2_partfun1(esk5_0,esk3_0,X1,k1_xboole_0)!=k1_xboole_0|~v1_funct_2(X1,esk5_0,esk3_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_79]), c_0_22]), c_0_23]), c_0_24])]), c_0_25])).
% 0.19/0.41  cnf(c_0_89, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0)!=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_87])])).
% 0.19/0.41  cnf(c_0_90, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_82]), c_0_84]), c_0_68]), c_0_67])]), c_0_89]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 91
% 0.19/0.41  # Proof object clause steps            : 60
% 0.19/0.41  # Proof object formula steps           : 31
% 0.19/0.41  # Proof object conjectures             : 41
% 0.19/0.41  # Proof object clause conjectures      : 38
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 31
% 0.19/0.41  # Proof object initial formulas used   : 15
% 0.19/0.41  # Proof object generating inferences   : 24
% 0.19/0.41  # Proof object simplifying inferences  : 68
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 15
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 39
% 0.19/0.41  # Removed in clause preprocessing      : 1
% 0.19/0.41  # Initial clauses in saturation        : 38
% 0.19/0.41  # Processed clauses                    : 329
% 0.19/0.41  # ...of these trivial                  : 8
% 0.19/0.41  # ...subsumed                          : 12
% 0.19/0.41  # ...remaining for further processing  : 309
% 0.19/0.41  # Other redundant clauses eliminated   : 5
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 0
% 0.19/0.41  # Backward-rewritten                   : 21
% 0.19/0.41  # Generated clauses                    : 357
% 0.19/0.41  # ...of the previous two non-trivial   : 337
% 0.19/0.41  # Contextual simplify-reflections      : 6
% 0.19/0.41  # Paramodulations                      : 346
% 0.19/0.41  # Factorizations                       : 0
% 0.19/0.41  # Equation resolutions                 : 12
% 0.19/0.41  # Propositional unsat checks           : 0
% 0.19/0.41  #    Propositional check models        : 0
% 0.19/0.41  #    Propositional check unsatisfiable : 0
% 0.19/0.41  #    Propositional clauses             : 0
% 0.19/0.41  #    Propositional clauses after purity: 0
% 0.19/0.41  #    Propositional unsat core size     : 0
% 0.19/0.41  #    Propositional preprocessing time  : 0.000
% 0.19/0.41  #    Propositional encoding time       : 0.000
% 0.19/0.41  #    Propositional solver time         : 0.000
% 0.19/0.41  #    Success case prop preproc time    : 0.000
% 0.19/0.41  #    Success case prop encoding time   : 0.000
% 0.19/0.41  #    Success case prop solver time     : 0.000
% 0.19/0.41  # Current number of processed clauses  : 246
% 0.19/0.41  #    Positive orientable unit clauses  : 91
% 0.19/0.41  #    Positive unorientable unit clauses: 2
% 0.19/0.41  #    Negative unit clauses             : 6
% 0.19/0.41  #    Non-unit-clauses                  : 147
% 0.19/0.41  # Current number of unprocessed clauses: 84
% 0.19/0.41  # ...number of literals in the above   : 801
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 59
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 16066
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 947
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 18
% 0.19/0.41  # Unit Clause-clause subsumption calls : 2535
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 131
% 0.19/0.41  # BW rewrite match successes           : 19
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 26231
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.068 s
% 0.19/0.41  # System time              : 0.008 s
% 0.19/0.41  # Total time               : 0.076 s
% 0.19/0.41  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
