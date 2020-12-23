%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:37 EST 2020

% Result     : Theorem 0.70s
% Output     : CNFRefutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :  154 (6798 expanded)
%              Number of clauses        :  110 (2535 expanded)
%              Number of leaves         :   22 (1695 expanded)
%              Depth                    :   18
%              Number of atoms          :  658 (58261 expanded)
%              Number of equality atoms :  147 (9860 expanded)
%              Maximal formula depth    :   28 (   5 average)
%              Maximal clause size      :   55 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

fof(t187_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_xboole_0(X2,k1_relat_1(X1))
         => k7_relat_1(X1,X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

fof(redefinition_r1_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2) )
     => ( r1_subset_1(X1,X2)
      <=> r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

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

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(t162_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

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

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t1_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(c_0_22,negated_conjecture,(
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

fof(c_0_23,plain,(
    ! [X40,X41,X42] :
      ( ( v1_funct_1(X42)
        | ~ v1_funct_1(X42)
        | ~ v1_funct_2(X42,X40,X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
        | v1_xboole_0(X41) )
      & ( v1_partfun1(X42,X40)
        | ~ v1_funct_1(X42)
        | ~ v1_funct_2(X42,X40,X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
        | v1_xboole_0(X41) ) ) ),
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])).

fof(c_0_25,plain,(
    ! [X35,X36,X37] :
      ( ( v4_relat_1(X37,X35)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( v5_relat_1(X37,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_26,plain,(
    ! [X32,X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | v1_relat_1(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_27,plain,(
    ! [X43,X44] :
      ( ( ~ v1_partfun1(X44,X43)
        | k1_relat_1(X44) = X43
        | ~ v1_relat_1(X44)
        | ~ v4_relat_1(X44,X43) )
      & ( k1_relat_1(X44) != X43
        | v1_partfun1(X44,X43)
        | ~ v1_relat_1(X44)
        | ~ v4_relat_1(X44,X43) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

cnf(c_0_28,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_2(esk7_0,esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_35,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X25)
      | ~ r1_xboole_0(X26,k1_relat_1(X25))
      | k7_relat_1(X25,X26) = k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t187_relat_1])])])).

cnf(c_0_36,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( v1_partfun1(esk7_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( v4_relat_1(esk7_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_31])).

fof(c_0_40,plain,(
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

fof(c_0_41,plain,(
    ! [X56,X57,X58,X59,X60,X61] :
      ( ( v1_funct_1(k1_tmap_1(X56,X57,X58,X59,X60,X61))
        | v1_xboole_0(X56)
        | v1_xboole_0(X57)
        | v1_xboole_0(X58)
        | ~ m1_subset_1(X58,k1_zfmisc_1(X56))
        | v1_xboole_0(X59)
        | ~ m1_subset_1(X59,k1_zfmisc_1(X56))
        | ~ v1_funct_1(X60)
        | ~ v1_funct_2(X60,X58,X57)
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X57)))
        | ~ v1_funct_1(X61)
        | ~ v1_funct_2(X61,X59,X57)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X57))) )
      & ( v1_funct_2(k1_tmap_1(X56,X57,X58,X59,X60,X61),k4_subset_1(X56,X58,X59),X57)
        | v1_xboole_0(X56)
        | v1_xboole_0(X57)
        | v1_xboole_0(X58)
        | ~ m1_subset_1(X58,k1_zfmisc_1(X56))
        | v1_xboole_0(X59)
        | ~ m1_subset_1(X59,k1_zfmisc_1(X56))
        | ~ v1_funct_1(X60)
        | ~ v1_funct_2(X60,X58,X57)
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X57)))
        | ~ v1_funct_1(X61)
        | ~ v1_funct_2(X61,X59,X57)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X57))) )
      & ( m1_subset_1(k1_tmap_1(X56,X57,X58,X59,X60,X61),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X56,X58,X59),X57)))
        | v1_xboole_0(X56)
        | v1_xboole_0(X57)
        | v1_xboole_0(X58)
        | ~ m1_subset_1(X58,k1_zfmisc_1(X56))
        | v1_xboole_0(X59)
        | ~ m1_subset_1(X59,k1_zfmisc_1(X56))
        | ~ v1_funct_1(X60)
        | ~ v1_funct_2(X60,X58,X57)
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X57)))
        | ~ v1_funct_1(X61)
        | ~ v1_funct_2(X61,X59,X57)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X57))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tmap_1])])])])).

fof(c_0_42,plain,(
    ! [X13,X14] :
      ( ~ v1_xboole_0(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | v1_xboole_0(X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_43,plain,
    ( k7_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39])])).

cnf(c_0_45,plain,
    ( r1_xboole_0(X1,X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( r1_subset_1(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_47,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_48,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_49,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_52,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X29)
      | r1_tarski(k1_relat_1(k7_relat_1(X29,X28)),X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

cnf(c_0_53,negated_conjecture,
    ( k7_relat_1(esk7_0,X1) = k1_xboole_0
    | ~ r1_xboole_0(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_39])])).

cnf(c_0_54,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_48])).

fof(c_0_55,plain,(
    ! [X22,X23,X24] :
      ( ~ v1_relat_1(X22)
      | ~ r1_tarski(X23,X24)
      | k9_relat_1(k7_relat_1(X22,X24),X23) = k9_relat_1(X22,X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).

cnf(c_0_56,plain,
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
    inference(csr,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_60,plain,
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
    inference(csr,[status(thm)],[c_0_51,c_0_50])).

fof(c_0_61,plain,(
    ! [X49,X50,X51,X52,X53,X54,X55] :
      ( ( k2_partfun1(k4_subset_1(X49,X51,X52),X50,X55,X51) = X53
        | X55 != k1_tmap_1(X49,X50,X51,X52,X53,X54)
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,k4_subset_1(X49,X51,X52),X50)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X49,X51,X52),X50)))
        | k2_partfun1(X51,X50,X53,k9_subset_1(X49,X51,X52)) != k2_partfun1(X52,X50,X54,k9_subset_1(X49,X51,X52))
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X52,X50)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X50)))
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,X51,X50)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X50)))
        | v1_xboole_0(X52)
        | ~ m1_subset_1(X52,k1_zfmisc_1(X49))
        | v1_xboole_0(X51)
        | ~ m1_subset_1(X51,k1_zfmisc_1(X49))
        | v1_xboole_0(X50)
        | v1_xboole_0(X49) )
      & ( k2_partfun1(k4_subset_1(X49,X51,X52),X50,X55,X52) = X54
        | X55 != k1_tmap_1(X49,X50,X51,X52,X53,X54)
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,k4_subset_1(X49,X51,X52),X50)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X49,X51,X52),X50)))
        | k2_partfun1(X51,X50,X53,k9_subset_1(X49,X51,X52)) != k2_partfun1(X52,X50,X54,k9_subset_1(X49,X51,X52))
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X52,X50)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X50)))
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,X51,X50)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X50)))
        | v1_xboole_0(X52)
        | ~ m1_subset_1(X52,k1_zfmisc_1(X49))
        | v1_xboole_0(X51)
        | ~ m1_subset_1(X51,k1_zfmisc_1(X49))
        | v1_xboole_0(X50)
        | v1_xboole_0(X49) )
      & ( k2_partfun1(k4_subset_1(X49,X51,X52),X50,X55,X51) != X53
        | k2_partfun1(k4_subset_1(X49,X51,X52),X50,X55,X52) != X54
        | X55 = k1_tmap_1(X49,X50,X51,X52,X53,X54)
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,k4_subset_1(X49,X51,X52),X50)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X49,X51,X52),X50)))
        | k2_partfun1(X51,X50,X53,k9_subset_1(X49,X51,X52)) != k2_partfun1(X52,X50,X54,k9_subset_1(X49,X51,X52))
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X52,X50)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X50)))
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,X51,X50)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X50)))
        | v1_xboole_0(X52)
        | ~ m1_subset_1(X52,k1_zfmisc_1(X49))
        | v1_xboole_0(X51)
        | ~ m1_subset_1(X51,k1_zfmisc_1(X49))
        | v1_xboole_0(X50)
        | v1_xboole_0(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tmap_1])])])])])).

cnf(c_0_62,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_63,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_64,negated_conjecture,
    ( k7_relat_1(esk7_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_65,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

fof(c_0_66,plain,(
    ! [X45,X46,X47,X48] :
      ( ~ v1_funct_1(X47)
      | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
      | k2_partfun1(X45,X46,X47,X48) = k7_relat_1(X47,X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

fof(c_0_67,plain,(
    ! [X19] :
      ( ~ v1_relat_1(X19)
      | k9_relat_1(X19,k1_relat_1(X19)) = k2_relat_1(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

cnf(c_0_68,plain,
    ( k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_69,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X17)
      | v1_relat_1(k7_relat_1(X17,X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_70,plain,(
    ! [X38] :
      ( ( r2_hidden(esk1_1(X38),X38)
        | X38 = k1_xboole_0 )
      & ( r1_xboole_0(esk1_1(X38),X38)
        | X38 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_mcart_1])])])])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(k1_tmap_1(X1,esk3_0,X2,esk4_0,X3,esk6_0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,esk4_0),esk3_0)))
    | v1_xboole_0(X2)
    | ~ v1_funct_2(X3,X2,esk3_0)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,esk3_0)))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),c_0_59])]),c_0_48]),c_0_32])).

cnf(c_0_72,negated_conjecture,
    ( v1_funct_1(k1_tmap_1(X1,esk3_0,X2,esk4_0,X3,esk6_0))
    | v1_xboole_0(X2)
    | ~ v1_funct_2(X3,X2,esk3_0)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,esk3_0)))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_57]),c_0_58]),c_0_59])]),c_0_48]),c_0_32])).

cnf(c_0_73,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_74,plain,
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
    inference(csr,[status(thm)],[c_0_62,c_0_50])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(k1_xboole_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),c_0_39])])).

cnf(c_0_76,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_77,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_78,plain,
    ( k9_relat_1(k7_relat_1(X1,X2),k1_relat_1(k7_relat_1(X3,X2))) = k9_relat_1(X1,k1_relat_1(k7_relat_1(X3,X2)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_68,c_0_63])).

cnf(c_0_79,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_80,plain,
    ( r1_xboole_0(esk1_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(k1_tmap_1(X1,esk3_0,esk4_0,esk4_0,esk6_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,esk4_0,esk4_0),esk3_0)))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_57]),c_0_58]),c_0_59])]),c_0_48])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_83,negated_conjecture,
    ( v1_funct_1(k1_tmap_1(X1,esk3_0,esk4_0,esk4_0,esk6_0,esk6_0))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_57]),c_0_58]),c_0_59])]),c_0_48])).

cnf(c_0_84,plain,
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
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_73,c_0_50])]),c_0_56]),c_0_60]),c_0_74])).

fof(c_0_85,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X21)
      | k2_relat_1(k7_relat_1(X21,X20)) = k9_relat_1(X21,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_86,negated_conjecture,
    ( k9_relat_1(k7_relat_1(X1,esk4_0),k1_xboole_0) = k9_relat_1(X1,k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_75])).

cnf(c_0_87,negated_conjecture,
    ( k7_relat_1(esk6_0,X1) = k2_partfun1(esk4_0,esk3_0,esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_59]),c_0_58])])).

cnf(c_0_88,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_59])).

cnf(c_0_89,plain,
    ( k9_relat_1(X1,k1_relat_1(k7_relat_1(X1,X2))) = k2_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79])).

cnf(c_0_90,plain,
    ( k7_relat_1(X1,esk1_1(k1_relat_1(X1))) = k1_xboole_0
    | k1_relat_1(X1) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_80])).

cnf(c_0_91,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

fof(c_0_92,plain,(
    ! [X10,X11,X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(X10))
      | k9_subset_1(X10,X11,X12) = k3_xboole_0(X11,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_93,plain,(
    ! [X15,X16] : k1_setfam_1(k2_tarski(X15,X16)) = k3_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

cnf(c_0_94,negated_conjecture,
    ( k7_relat_1(esk7_0,X1) = k2_partfun1(esk5_0,esk3_0,esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_31]),c_0_30])])).

cnf(c_0_95,negated_conjecture,
    ( v1_relat_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_64]),c_0_39])])).

cnf(c_0_96,negated_conjecture,
    ( m1_subset_1(k1_tmap_1(esk2_0,esk3_0,esk4_0,esk4_0,esk6_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(esk2_0,esk4_0,esk4_0),esk3_0))) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_97,negated_conjecture,
    ( v1_funct_1(k1_tmap_1(esk2_0,esk3_0,esk4_0,esk4_0,esk6_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_82])).

cnf(c_0_98,plain,
    ( k2_partfun1(k4_subset_1(X1,X2,X2),X3,k1_tmap_1(X1,X3,X2,X2,X4,X4),X2) = X4
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(er,[status(thm)],[c_0_84])).

cnf(c_0_99,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_100,negated_conjecture,
    ( k9_relat_1(k2_partfun1(esk4_0,esk3_0,esk6_0,esk4_0),k1_xboole_0) = k9_relat_1(esk6_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88])])).

cnf(c_0_101,negated_conjecture,
    ( v1_relat_1(k2_partfun1(esk4_0,esk3_0,esk6_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_87]),c_0_88])])).

fof(c_0_102,plain,(
    ! [X27] :
      ( ( k1_relat_1(X27) != k1_xboole_0
        | X27 = k1_xboole_0
        | ~ v1_relat_1(X27) )
      & ( k2_relat_1(X27) != k1_xboole_0
        | X27 = k1_xboole_0
        | ~ v1_relat_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

cnf(c_0_103,plain,
    ( k9_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | k1_relat_1(X1) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_65]),c_0_91])).

cnf(c_0_104,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_105,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

fof(c_0_106,plain,(
    ! [X8,X9] :
      ( ( ~ r1_xboole_0(X8,X9)
        | k3_xboole_0(X8,X9) = k1_xboole_0 )
      & ( k3_xboole_0(X8,X9) != k1_xboole_0
        | r1_xboole_0(X8,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_107,negated_conjecture,
    ( k2_partfun1(esk5_0,esk3_0,esk7_0,esk4_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_64,c_0_94])).

cnf(c_0_108,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_65]),c_0_91]),c_0_95])])).

cnf(c_0_109,negated_conjecture,
    ( k7_relat_1(k1_tmap_1(esk2_0,esk3_0,esk4_0,esk4_0,esk6_0,esk6_0),X1) = k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk4_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk4_0,esk6_0,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_96]),c_0_97])])).

cnf(c_0_110,negated_conjecture,
    ( v1_relat_1(k1_tmap_1(esk2_0,esk3_0,esk4_0,esk4_0,esk6_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_96])).

cnf(c_0_111,negated_conjecture,
    ( k2_partfun1(k4_subset_1(X1,esk4_0,esk4_0),esk3_0,k1_tmap_1(X1,esk3_0,esk4_0,esk4_0,esk6_0,esk6_0),esk4_0) = esk6_0
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_57]),c_0_58]),c_0_59])]),c_0_32]),c_0_48])).

cnf(c_0_112,negated_conjecture,
    ( k9_relat_1(esk6_0,k1_xboole_0) = k2_relat_1(k7_relat_1(k2_partfun1(esk4_0,esk3_0,esk6_0,esk4_0),k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_101])])).

cnf(c_0_113,negated_conjecture,
    ( r1_tarski(k1_relat_1(k2_partfun1(esk5_0,esk3_0,esk7_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_94]),c_0_39])])).

cnf(c_0_114,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_115,negated_conjecture,
    ( k1_relat_1(k7_relat_1(X1,esk4_0)) = k1_xboole_0
    | k9_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_103]),c_0_79])).

cnf(c_0_116,plain,
    ( k9_subset_1(X2,X3,X1) = k1_setfam_1(k2_tarski(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_117,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_118,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_106])).

cnf(c_0_119,negated_conjecture,
    ( k9_relat_1(esk7_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_94]),c_0_107]),c_0_108]),c_0_39])])).

cnf(c_0_120,plain,
    ( X1 = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_121,negated_conjecture,
    ( k9_relat_1(X1,k1_xboole_0) = k2_relat_1(k7_relat_1(k7_relat_1(X1,esk4_0),k1_xboole_0))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_86]),c_0_79])).

cnf(c_0_122,negated_conjecture,
    ( k9_relat_1(k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk4_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk4_0,esk6_0,esk6_0),esk4_0),k1_xboole_0) = k9_relat_1(k1_tmap_1(esk2_0,esk3_0,esk4_0,esk4_0,esk6_0,esk6_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_109]),c_0_110])])).

cnf(c_0_123,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk4_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk4_0,esk6_0,esk6_0),esk4_0) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_111,c_0_82])).

cnf(c_0_124,negated_conjecture,
    ( k2_relat_1(k7_relat_1(k2_partfun1(esk4_0,esk3_0,esk6_0,esk4_0),k1_xboole_0)) = k2_relat_1(k2_partfun1(esk4_0,esk3_0,esk6_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_112]),c_0_87]),c_0_88])])).

cnf(c_0_125,negated_conjecture,
    ( k9_relat_1(k7_relat_1(X1,X2),k1_relat_1(k2_partfun1(esk5_0,esk3_0,esk7_0,X2))) = k9_relat_1(X1,k1_relat_1(k2_partfun1(esk5_0,esk3_0,esk7_0,X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_113])).

cnf(c_0_126,negated_conjecture,
    ( k9_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | k7_relat_1(X1,esk4_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_79])).

cnf(c_0_127,negated_conjecture,
    ( k9_subset_1(esk2_0,X1,esk5_0) = k1_setfam_1(k2_tarski(X1,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_116,c_0_117])).

cnf(c_0_128,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_118,c_0_105])).

cnf(c_0_129,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_130,negated_conjecture,
    ( k2_relat_1(k2_partfun1(esk5_0,esk3_0,esk7_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_119]),c_0_94]),c_0_39])])).

cnf(c_0_131,negated_conjecture,
    ( v1_relat_1(k2_partfun1(esk5_0,esk3_0,esk7_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_94]),c_0_39])])).

cnf(c_0_132,negated_conjecture,
    ( k7_relat_1(k7_relat_1(X1,esk4_0),k1_xboole_0) = k1_xboole_0
    | k9_relat_1(X1,k1_xboole_0) != k1_xboole_0
    | ~ v1_relat_1(k7_relat_1(k7_relat_1(X1,esk4_0),k1_xboole_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_120,c_0_121])).

cnf(c_0_133,negated_conjecture,
    ( k9_relat_1(k1_tmap_1(esk2_0,esk3_0,esk4_0,esk4_0,esk6_0,esk6_0),k1_xboole_0) = k2_relat_1(k2_partfun1(esk4_0,esk3_0,esk6_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_122,c_0_123]),c_0_112]),c_0_124])).

cnf(c_0_134,negated_conjecture,
    ( k9_relat_1(esk6_0,k1_xboole_0) = k2_relat_1(k2_partfun1(esk4_0,esk3_0,esk6_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_112,c_0_124])).

cnf(c_0_135,negated_conjecture,
    ( k9_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_126]),c_0_107]),c_0_65]),c_0_108]),c_0_107]),c_0_65])])).

cnf(c_0_136,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,X1,esk5_0),X2,k1_tmap_1(esk2_0,X2,X1,esk5_0,X3,X4),esk5_0) = X4
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X3,k1_setfam_1(k2_tarski(X1,esk5_0))) != k2_partfun1(esk5_0,X2,X4,k1_setfam_1(k2_tarski(X1,esk5_0)))
    | ~ v1_funct_2(X4,esk5_0,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_127]),c_0_117])]),c_0_47])).

cnf(c_0_137,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk4_0,esk5_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_128,c_0_54])).

cnf(c_0_138,plain,
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
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_129,c_0_50])]),c_0_56]),c_0_60]),c_0_74])).

cnf(c_0_139,negated_conjecture,
    ( k2_partfun1(esk4_0,esk3_0,esk6_0,k9_subset_1(esk2_0,esk4_0,esk5_0)) != k2_partfun1(esk5_0,esk3_0,esk7_0,k9_subset_1(esk2_0,esk4_0,esk5_0))
    | k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0) != esk6_0
    | k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0) != esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_140,negated_conjecture,
    ( k2_partfun1(esk5_0,esk3_0,esk7_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_130]),c_0_131])])).

cnf(c_0_141,negated_conjecture,
    ( k2_partfun1(esk4_0,esk3_0,esk6_0,k1_xboole_0) = k1_xboole_0
    | k2_relat_1(k2_partfun1(esk4_0,esk3_0,esk6_0,k1_xboole_0)) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_133]),c_0_109]),c_0_123]),c_0_87]),c_0_109]),c_0_123]),c_0_87]),c_0_101]),c_0_110])])).

cnf(c_0_142,negated_conjecture,
    ( k2_relat_1(k2_partfun1(esk4_0,esk3_0,esk6_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_135]),c_0_88])])).

cnf(c_0_143,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),X1,k1_tmap_1(esk2_0,X1,esk4_0,esk5_0,X2,X3),esk5_0) = X3
    | v1_xboole_0(X1)
    | k2_partfun1(esk4_0,X1,X2,k1_xboole_0) != k2_partfun1(esk5_0,X1,X3,k1_xboole_0)
    | ~ v1_funct_2(X3,esk5_0,X1)
    | ~ v1_funct_2(X2,esk4_0,X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_137]),c_0_82])]),c_0_48])).

cnf(c_0_144,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,X1,esk5_0),X2,k1_tmap_1(esk2_0,X2,X1,esk5_0,X3,X4),X1) = X3
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X3,k1_setfam_1(k2_tarski(X1,esk5_0))) != k2_partfun1(esk5_0,X2,X4,k1_setfam_1(k2_tarski(X1,esk5_0)))
    | ~ v1_funct_2(X4,esk5_0,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_127]),c_0_117])]),c_0_47])).

cnf(c_0_145,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0) != esk6_0
    | k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0) != esk7_0
    | k2_partfun1(esk4_0,esk3_0,esk6_0,k1_xboole_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_139,c_0_127]),c_0_137]),c_0_140]),c_0_127]),c_0_137])).

cnf(c_0_146,negated_conjecture,
    ( k2_partfun1(esk4_0,esk3_0,esk6_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_141,c_0_142])])).

cnf(c_0_147,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,X1,esk7_0),esk5_0) = esk7_0
    | k2_partfun1(esk4_0,esk3_0,X1,k1_xboole_0) != k1_xboole_0
    | ~ v1_funct_2(X1,esk4_0,esk3_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_140]),c_0_29]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_148,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),X1,k1_tmap_1(esk2_0,X1,esk4_0,esk5_0,X2,X3),esk4_0) = X2
    | v1_xboole_0(X1)
    | k2_partfun1(esk4_0,X1,X2,k1_xboole_0) != k2_partfun1(esk5_0,X1,X3,k1_xboole_0)
    | ~ v1_funct_2(X3,esk5_0,X1)
    | ~ v1_funct_2(X2,esk4_0,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_137]),c_0_82])]),c_0_48])).

cnf(c_0_149,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0) != esk6_0
    | k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0) != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_145,c_0_146])])).

cnf(c_0_150,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_146]),c_0_57]),c_0_58]),c_0_59])])).

cnf(c_0_151,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,X1),esk4_0) = esk6_0
    | k2_partfun1(esk5_0,esk3_0,X1,k1_xboole_0) != k1_xboole_0
    | ~ v1_funct_2(X1,esk5_0,esk3_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_146]),c_0_57]),c_0_58]),c_0_59])]),c_0_32])).

cnf(c_0_152,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0) != esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_149,c_0_150])])).

cnf(c_0_153,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151,c_0_140]),c_0_29]),c_0_30]),c_0_31])]),c_0_152]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.10  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.30  % Computer   : n007.cluster.edu
% 0.11/0.30  % Model      : x86_64 x86_64
% 0.11/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.30  % Memory     : 8042.1875MB
% 0.11/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.30  % CPULimit   : 60
% 0.11/0.30  % WCLimit    : 600
% 0.11/0.30  % DateTime   : Tue Dec  1 17:42:36 EST 2020
% 0.11/0.30  % CPUTime    : 
% 0.11/0.30  # Version: 2.5pre002
% 0.11/0.30  # No SInE strategy applied
% 0.11/0.30  # Trying AutoSched0 for 299 seconds
% 0.70/0.88  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.70/0.88  # and selection function SelectCQIPrecWNTNp.
% 0.70/0.88  #
% 0.70/0.88  # Preprocessing time       : 0.026 s
% 0.70/0.88  # Presaturation interreduction done
% 0.70/0.88  
% 0.70/0.88  # Proof found!
% 0.70/0.88  # SZS status Theorem
% 0.70/0.88  # SZS output start CNFRefutation
% 0.70/0.88  fof(t6_tmap_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>(r1_subset_1(X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3)=X5)&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4)=X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 0.70/0.88  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.70/0.88  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.70/0.88  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.70/0.88  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 0.70/0.88  fof(t187_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_xboole_0(X2,k1_relat_1(X1))=>k7_relat_1(X1,X2)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 0.70/0.88  fof(redefinition_r1_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))=>(r1_subset_1(X1,X2)<=>r1_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 0.70/0.88  fof(dt_k1_tmap_1, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((((((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))&~(v1_xboole_0(X3)))&m1_subset_1(X3,k1_zfmisc_1(X1)))&~(v1_xboole_0(X4)))&m1_subset_1(X4,k1_zfmisc_1(X1)))&v1_funct_1(X5))&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2))&m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 0.70/0.88  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.70/0.88  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 0.70/0.88  fof(t162_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 0.70/0.88  fof(d1_tmap_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>(k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))=>![X7]:(((v1_funct_1(X7)&v1_funct_2(X7,k4_subset_1(X1,X3,X4),X2))&m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))))=>(X7=k1_tmap_1(X1,X2,X3,X4,X5,X6)<=>(k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X3)=X5&k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X4)=X6)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 0.70/0.88  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.70/0.88  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 0.70/0.88  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 0.70/0.88  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.70/0.88  fof(t1_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&r1_xboole_0(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 0.70/0.88  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.70/0.88  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.70/0.88  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.70/0.88  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 0.70/0.88  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.70/0.88  fof(c_0_22, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>(r1_subset_1(X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3)=X5)&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4)=X6))))))))), inference(assume_negation,[status(cth)],[t6_tmap_1])).
% 0.70/0.88  fof(c_0_23, plain, ![X40, X41, X42]:((v1_funct_1(X42)|(~v1_funct_1(X42)|~v1_funct_2(X42,X40,X41))|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|v1_xboole_0(X41))&(v1_partfun1(X42,X40)|(~v1_funct_1(X42)|~v1_funct_2(X42,X40,X41))|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|v1_xboole_0(X41))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.70/0.88  fof(c_0_24, negated_conjecture, (~v1_xboole_0(esk2_0)&(~v1_xboole_0(esk3_0)&((~v1_xboole_0(esk4_0)&m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)))&((~v1_xboole_0(esk5_0)&m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0)))&(r1_subset_1(esk4_0,esk5_0)&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk4_0,esk3_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))))&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk5_0,esk3_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0))))&(k2_partfun1(esk4_0,esk3_0,esk6_0,k9_subset_1(esk2_0,esk4_0,esk5_0))!=k2_partfun1(esk5_0,esk3_0,esk7_0,k9_subset_1(esk2_0,esk4_0,esk5_0))|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0)!=esk6_0|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0)!=esk7_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])).
% 0.70/0.88  fof(c_0_25, plain, ![X35, X36, X37]:((v4_relat_1(X37,X35)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))&(v5_relat_1(X37,X36)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.70/0.88  fof(c_0_26, plain, ![X32, X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|v1_relat_1(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.70/0.88  fof(c_0_27, plain, ![X43, X44]:((~v1_partfun1(X44,X43)|k1_relat_1(X44)=X43|(~v1_relat_1(X44)|~v4_relat_1(X44,X43)))&(k1_relat_1(X44)!=X43|v1_partfun1(X44,X43)|(~v1_relat_1(X44)|~v4_relat_1(X44,X43)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 0.70/0.88  cnf(c_0_28, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.70/0.88  cnf(c_0_29, negated_conjecture, (v1_funct_2(esk7_0,esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.70/0.88  cnf(c_0_30, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.70/0.88  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.70/0.88  cnf(c_0_32, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.70/0.88  cnf(c_0_33, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.70/0.88  cnf(c_0_34, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.70/0.88  fof(c_0_35, plain, ![X25, X26]:(~v1_relat_1(X25)|(~r1_xboole_0(X26,k1_relat_1(X25))|k7_relat_1(X25,X26)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t187_relat_1])])])).
% 0.70/0.88  cnf(c_0_36, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.70/0.88  cnf(c_0_37, negated_conjecture, (v1_partfun1(esk7_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31])]), c_0_32])).
% 0.70/0.88  cnf(c_0_38, negated_conjecture, (v4_relat_1(esk7_0,esk5_0)), inference(spm,[status(thm)],[c_0_33, c_0_31])).
% 0.70/0.88  cnf(c_0_39, negated_conjecture, (v1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_34, c_0_31])).
% 0.70/0.88  fof(c_0_40, plain, ![X30, X31]:((~r1_subset_1(X30,X31)|r1_xboole_0(X30,X31)|(v1_xboole_0(X30)|v1_xboole_0(X31)))&(~r1_xboole_0(X30,X31)|r1_subset_1(X30,X31)|(v1_xboole_0(X30)|v1_xboole_0(X31)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).
% 0.70/0.88  fof(c_0_41, plain, ![X56, X57, X58, X59, X60, X61]:(((v1_funct_1(k1_tmap_1(X56,X57,X58,X59,X60,X61))|(v1_xboole_0(X56)|v1_xboole_0(X57)|v1_xboole_0(X58)|~m1_subset_1(X58,k1_zfmisc_1(X56))|v1_xboole_0(X59)|~m1_subset_1(X59,k1_zfmisc_1(X56))|~v1_funct_1(X60)|~v1_funct_2(X60,X58,X57)|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X57)))|~v1_funct_1(X61)|~v1_funct_2(X61,X59,X57)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X57)))))&(v1_funct_2(k1_tmap_1(X56,X57,X58,X59,X60,X61),k4_subset_1(X56,X58,X59),X57)|(v1_xboole_0(X56)|v1_xboole_0(X57)|v1_xboole_0(X58)|~m1_subset_1(X58,k1_zfmisc_1(X56))|v1_xboole_0(X59)|~m1_subset_1(X59,k1_zfmisc_1(X56))|~v1_funct_1(X60)|~v1_funct_2(X60,X58,X57)|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X57)))|~v1_funct_1(X61)|~v1_funct_2(X61,X59,X57)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X57))))))&(m1_subset_1(k1_tmap_1(X56,X57,X58,X59,X60,X61),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X56,X58,X59),X57)))|(v1_xboole_0(X56)|v1_xboole_0(X57)|v1_xboole_0(X58)|~m1_subset_1(X58,k1_zfmisc_1(X56))|v1_xboole_0(X59)|~m1_subset_1(X59,k1_zfmisc_1(X56))|~v1_funct_1(X60)|~v1_funct_2(X60,X58,X57)|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X57)))|~v1_funct_1(X61)|~v1_funct_2(X61,X59,X57)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X57)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tmap_1])])])])).
% 0.70/0.88  fof(c_0_42, plain, ![X13, X14]:(~v1_xboole_0(X13)|(~m1_subset_1(X14,k1_zfmisc_1(X13))|v1_xboole_0(X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.70/0.88  cnf(c_0_43, plain, (k7_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.70/0.88  cnf(c_0_44, negated_conjecture, (k1_relat_1(esk7_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39])])).
% 0.70/0.88  cnf(c_0_45, plain, (r1_xboole_0(X1,X2)|v1_xboole_0(X1)|v1_xboole_0(X2)|~r1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.70/0.88  cnf(c_0_46, negated_conjecture, (r1_subset_1(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.70/0.88  cnf(c_0_47, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.70/0.88  cnf(c_0_48, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.70/0.88  cnf(c_0_49, plain, (m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2)))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.70/0.88  cnf(c_0_50, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.70/0.88  cnf(c_0_51, plain, (v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.70/0.88  fof(c_0_52, plain, ![X28, X29]:(~v1_relat_1(X29)|r1_tarski(k1_relat_1(k7_relat_1(X29,X28)),X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 0.70/0.88  cnf(c_0_53, negated_conjecture, (k7_relat_1(esk7_0,X1)=k1_xboole_0|~r1_xboole_0(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_39])])).
% 0.70/0.88  cnf(c_0_54, negated_conjecture, (r1_xboole_0(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47]), c_0_48])).
% 0.70/0.88  fof(c_0_55, plain, ![X22, X23, X24]:(~v1_relat_1(X22)|(~r1_tarski(X23,X24)|k9_relat_1(k7_relat_1(X22,X24),X23)=k9_relat_1(X22,X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).
% 0.70/0.88  cnf(c_0_56, plain, (m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2)))|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~v1_funct_2(X6,X4,X2)|~v1_funct_2(X5,X3,X2)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[c_0_49, c_0_50])).
% 0.70/0.88  cnf(c_0_57, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.70/0.88  cnf(c_0_58, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.70/0.88  cnf(c_0_59, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.70/0.88  cnf(c_0_60, plain, (v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~v1_funct_2(X6,X4,X2)|~v1_funct_2(X5,X3,X2)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[c_0_51, c_0_50])).
% 0.70/0.88  fof(c_0_61, plain, ![X49, X50, X51, X52, X53, X54, X55]:(((k2_partfun1(k4_subset_1(X49,X51,X52),X50,X55,X51)=X53|X55!=k1_tmap_1(X49,X50,X51,X52,X53,X54)|(~v1_funct_1(X55)|~v1_funct_2(X55,k4_subset_1(X49,X51,X52),X50)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X49,X51,X52),X50))))|k2_partfun1(X51,X50,X53,k9_subset_1(X49,X51,X52))!=k2_partfun1(X52,X50,X54,k9_subset_1(X49,X51,X52))|(~v1_funct_1(X54)|~v1_funct_2(X54,X52,X50)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X50))))|(~v1_funct_1(X53)|~v1_funct_2(X53,X51,X50)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X50))))|(v1_xboole_0(X52)|~m1_subset_1(X52,k1_zfmisc_1(X49)))|(v1_xboole_0(X51)|~m1_subset_1(X51,k1_zfmisc_1(X49)))|v1_xboole_0(X50)|v1_xboole_0(X49))&(k2_partfun1(k4_subset_1(X49,X51,X52),X50,X55,X52)=X54|X55!=k1_tmap_1(X49,X50,X51,X52,X53,X54)|(~v1_funct_1(X55)|~v1_funct_2(X55,k4_subset_1(X49,X51,X52),X50)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X49,X51,X52),X50))))|k2_partfun1(X51,X50,X53,k9_subset_1(X49,X51,X52))!=k2_partfun1(X52,X50,X54,k9_subset_1(X49,X51,X52))|(~v1_funct_1(X54)|~v1_funct_2(X54,X52,X50)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X50))))|(~v1_funct_1(X53)|~v1_funct_2(X53,X51,X50)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X50))))|(v1_xboole_0(X52)|~m1_subset_1(X52,k1_zfmisc_1(X49)))|(v1_xboole_0(X51)|~m1_subset_1(X51,k1_zfmisc_1(X49)))|v1_xboole_0(X50)|v1_xboole_0(X49)))&(k2_partfun1(k4_subset_1(X49,X51,X52),X50,X55,X51)!=X53|k2_partfun1(k4_subset_1(X49,X51,X52),X50,X55,X52)!=X54|X55=k1_tmap_1(X49,X50,X51,X52,X53,X54)|(~v1_funct_1(X55)|~v1_funct_2(X55,k4_subset_1(X49,X51,X52),X50)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X49,X51,X52),X50))))|k2_partfun1(X51,X50,X53,k9_subset_1(X49,X51,X52))!=k2_partfun1(X52,X50,X54,k9_subset_1(X49,X51,X52))|(~v1_funct_1(X54)|~v1_funct_2(X54,X52,X50)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X50))))|(~v1_funct_1(X53)|~v1_funct_2(X53,X51,X50)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X50))))|(v1_xboole_0(X52)|~m1_subset_1(X52,k1_zfmisc_1(X49)))|(v1_xboole_0(X51)|~m1_subset_1(X51,k1_zfmisc_1(X49)))|v1_xboole_0(X50)|v1_xboole_0(X49))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tmap_1])])])])])).
% 0.70/0.88  cnf(c_0_62, plain, (v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.70/0.88  cnf(c_0_63, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.70/0.88  cnf(c_0_64, negated_conjecture, (k7_relat_1(esk7_0,esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.70/0.88  cnf(c_0_65, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.70/0.88  fof(c_0_66, plain, ![X45, X46, X47, X48]:(~v1_funct_1(X47)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))|k2_partfun1(X45,X46,X47,X48)=k7_relat_1(X47,X48)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 0.70/0.88  fof(c_0_67, plain, ![X19]:(~v1_relat_1(X19)|k9_relat_1(X19,k1_relat_1(X19))=k2_relat_1(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.70/0.88  cnf(c_0_68, plain, (k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.70/0.88  fof(c_0_69, plain, ![X17, X18]:(~v1_relat_1(X17)|v1_relat_1(k7_relat_1(X17,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.70/0.88  fof(c_0_70, plain, ![X38]:((r2_hidden(esk1_1(X38),X38)|X38=k1_xboole_0)&(r1_xboole_0(esk1_1(X38),X38)|X38=k1_xboole_0)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_mcart_1])])])])).
% 0.70/0.88  cnf(c_0_71, negated_conjecture, (m1_subset_1(k1_tmap_1(X1,esk3_0,X2,esk4_0,X3,esk6_0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,esk4_0),esk3_0)))|v1_xboole_0(X2)|~v1_funct_2(X3,X2,esk3_0)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,esk3_0)))|~m1_subset_1(esk4_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58]), c_0_59])]), c_0_48]), c_0_32])).
% 0.70/0.88  cnf(c_0_72, negated_conjecture, (v1_funct_1(k1_tmap_1(X1,esk3_0,X2,esk4_0,X3,esk6_0))|v1_xboole_0(X2)|~v1_funct_2(X3,X2,esk3_0)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,esk3_0)))|~m1_subset_1(esk4_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_57]), c_0_58]), c_0_59])]), c_0_48]), c_0_32])).
% 0.70/0.88  cnf(c_0_73, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X3)=X6|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X4)|v1_xboole_0(X1)|X5!=k1_tmap_1(X1,X4,X2,X3,X7,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|k2_partfun1(X2,X4,X7,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_1(X6)|~v1_funct_2(X6,X3,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X7)|~v1_funct_2(X7,X2,X4)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.70/0.88  cnf(c_0_74, plain, (v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~v1_funct_2(X6,X4,X2)|~v1_funct_2(X5,X3,X2)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[c_0_62, c_0_50])).
% 0.70/0.88  cnf(c_0_75, negated_conjecture, (r1_tarski(k1_xboole_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65]), c_0_39])])).
% 0.70/0.88  cnf(c_0_76, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.70/0.88  cnf(c_0_77, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.70/0.88  cnf(c_0_78, plain, (k9_relat_1(k7_relat_1(X1,X2),k1_relat_1(k7_relat_1(X3,X2)))=k9_relat_1(X1,k1_relat_1(k7_relat_1(X3,X2)))|~v1_relat_1(X1)|~v1_relat_1(X3)), inference(spm,[status(thm)],[c_0_68, c_0_63])).
% 0.70/0.88  cnf(c_0_79, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.70/0.88  cnf(c_0_80, plain, (r1_xboole_0(esk1_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.70/0.88  cnf(c_0_81, negated_conjecture, (m1_subset_1(k1_tmap_1(X1,esk3_0,esk4_0,esk4_0,esk6_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,esk4_0,esk4_0),esk3_0)))|~m1_subset_1(esk4_0,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_57]), c_0_58]), c_0_59])]), c_0_48])).
% 0.70/0.88  cnf(c_0_82, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.70/0.88  cnf(c_0_83, negated_conjecture, (v1_funct_1(k1_tmap_1(X1,esk3_0,esk4_0,esk4_0,esk6_0,esk6_0))|~m1_subset_1(esk4_0,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_57]), c_0_58]), c_0_59])]), c_0_48])).
% 0.70/0.88  cnf(c_0_84, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X3)=X6|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_2(X5,X2,X4)|~v1_funct_2(X6,X3,X4)|~v1_funct_1(X5)|~v1_funct_1(X6)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_73, c_0_50])]), c_0_56]), c_0_60]), c_0_74])).
% 0.70/0.88  fof(c_0_85, plain, ![X20, X21]:(~v1_relat_1(X21)|k2_relat_1(k7_relat_1(X21,X20))=k9_relat_1(X21,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.70/0.88  cnf(c_0_86, negated_conjecture, (k9_relat_1(k7_relat_1(X1,esk4_0),k1_xboole_0)=k9_relat_1(X1,k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_68, c_0_75])).
% 0.70/0.88  cnf(c_0_87, negated_conjecture, (k7_relat_1(esk6_0,X1)=k2_partfun1(esk4_0,esk3_0,esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_59]), c_0_58])])).
% 0.70/0.88  cnf(c_0_88, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_34, c_0_59])).
% 0.70/0.88  cnf(c_0_89, plain, (k9_relat_1(X1,k1_relat_1(k7_relat_1(X1,X2)))=k2_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79])).
% 0.70/0.88  cnf(c_0_90, plain, (k7_relat_1(X1,esk1_1(k1_relat_1(X1)))=k1_xboole_0|k1_relat_1(X1)=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_43, c_0_80])).
% 0.70/0.88  cnf(c_0_91, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.70/0.88  fof(c_0_92, plain, ![X10, X11, X12]:(~m1_subset_1(X12,k1_zfmisc_1(X10))|k9_subset_1(X10,X11,X12)=k3_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.70/0.88  fof(c_0_93, plain, ![X15, X16]:k1_setfam_1(k2_tarski(X15,X16))=k3_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.70/0.88  cnf(c_0_94, negated_conjecture, (k7_relat_1(esk7_0,X1)=k2_partfun1(esk5_0,esk3_0,esk7_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_31]), c_0_30])])).
% 0.70/0.88  cnf(c_0_95, negated_conjecture, (v1_relat_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_64]), c_0_39])])).
% 0.70/0.88  cnf(c_0_96, negated_conjecture, (m1_subset_1(k1_tmap_1(esk2_0,esk3_0,esk4_0,esk4_0,esk6_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(esk2_0,esk4_0,esk4_0),esk3_0)))), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.70/0.88  cnf(c_0_97, negated_conjecture, (v1_funct_1(k1_tmap_1(esk2_0,esk3_0,esk4_0,esk4_0,esk6_0,esk6_0))), inference(spm,[status(thm)],[c_0_83, c_0_82])).
% 0.70/0.88  cnf(c_0_98, plain, (k2_partfun1(k4_subset_1(X1,X2,X2),X3,k1_tmap_1(X1,X3,X2,X2,X4,X4),X2)=X4|v1_xboole_0(X3)|v1_xboole_0(X2)|~v1_funct_2(X4,X2,X3)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(er,[status(thm)],[c_0_84])).
% 0.70/0.88  cnf(c_0_99, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.70/0.88  cnf(c_0_100, negated_conjecture, (k9_relat_1(k2_partfun1(esk4_0,esk3_0,esk6_0,esk4_0),k1_xboole_0)=k9_relat_1(esk6_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88])])).
% 0.70/0.88  cnf(c_0_101, negated_conjecture, (v1_relat_1(k2_partfun1(esk4_0,esk3_0,esk6_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_87]), c_0_88])])).
% 0.70/0.88  fof(c_0_102, plain, ![X27]:((k1_relat_1(X27)!=k1_xboole_0|X27=k1_xboole_0|~v1_relat_1(X27))&(k2_relat_1(X27)!=k1_xboole_0|X27=k1_xboole_0|~v1_relat_1(X27))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.70/0.88  cnf(c_0_103, plain, (k9_relat_1(X1,k1_xboole_0)=k1_xboole_0|k1_relat_1(X1)=k1_xboole_0|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_65]), c_0_91])).
% 0.70/0.88  cnf(c_0_104, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_92])).
% 0.70/0.88  cnf(c_0_105, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.70/0.88  fof(c_0_106, plain, ![X8, X9]:((~r1_xboole_0(X8,X9)|k3_xboole_0(X8,X9)=k1_xboole_0)&(k3_xboole_0(X8,X9)!=k1_xboole_0|r1_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.70/0.88  cnf(c_0_107, negated_conjecture, (k2_partfun1(esk5_0,esk3_0,esk7_0,esk4_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_64, c_0_94])).
% 0.70/0.88  cnf(c_0_108, plain, (k9_relat_1(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_65]), c_0_91]), c_0_95])])).
% 0.70/0.88  cnf(c_0_109, negated_conjecture, (k7_relat_1(k1_tmap_1(esk2_0,esk3_0,esk4_0,esk4_0,esk6_0,esk6_0),X1)=k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk4_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk4_0,esk6_0,esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_96]), c_0_97])])).
% 0.70/0.88  cnf(c_0_110, negated_conjecture, (v1_relat_1(k1_tmap_1(esk2_0,esk3_0,esk4_0,esk4_0,esk6_0,esk6_0))), inference(spm,[status(thm)],[c_0_34, c_0_96])).
% 0.70/0.88  cnf(c_0_111, negated_conjecture, (k2_partfun1(k4_subset_1(X1,esk4_0,esk4_0),esk3_0,k1_tmap_1(X1,esk3_0,esk4_0,esk4_0,esk6_0,esk6_0),esk4_0)=esk6_0|~m1_subset_1(esk4_0,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_57]), c_0_58]), c_0_59])]), c_0_32]), c_0_48])).
% 0.70/0.88  cnf(c_0_112, negated_conjecture, (k9_relat_1(esk6_0,k1_xboole_0)=k2_relat_1(k7_relat_1(k2_partfun1(esk4_0,esk3_0,esk6_0,esk4_0),k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_101])])).
% 0.70/0.88  cnf(c_0_113, negated_conjecture, (r1_tarski(k1_relat_1(k2_partfun1(esk5_0,esk3_0,esk7_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_94]), c_0_39])])).
% 0.70/0.88  cnf(c_0_114, plain, (X1=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_102])).
% 0.70/0.88  cnf(c_0_115, negated_conjecture, (k1_relat_1(k7_relat_1(X1,esk4_0))=k1_xboole_0|k9_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_103]), c_0_79])).
% 0.70/0.88  cnf(c_0_116, plain, (k9_subset_1(X2,X3,X1)=k1_setfam_1(k2_tarski(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_104, c_0_105])).
% 0.70/0.88  cnf(c_0_117, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.70/0.88  cnf(c_0_118, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_106])).
% 0.70/0.88  cnf(c_0_119, negated_conjecture, (k9_relat_1(esk7_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_94]), c_0_107]), c_0_108]), c_0_39])])).
% 0.70/0.88  cnf(c_0_120, plain, (X1=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_102])).
% 0.70/0.88  cnf(c_0_121, negated_conjecture, (k9_relat_1(X1,k1_xboole_0)=k2_relat_1(k7_relat_1(k7_relat_1(X1,esk4_0),k1_xboole_0))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_86]), c_0_79])).
% 0.70/0.88  cnf(c_0_122, negated_conjecture, (k9_relat_1(k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk4_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk4_0,esk6_0,esk6_0),esk4_0),k1_xboole_0)=k9_relat_1(k1_tmap_1(esk2_0,esk3_0,esk4_0,esk4_0,esk6_0,esk6_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_109]), c_0_110])])).
% 0.70/0.88  cnf(c_0_123, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk4_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk4_0,esk6_0,esk6_0),esk4_0)=esk6_0), inference(spm,[status(thm)],[c_0_111, c_0_82])).
% 0.70/0.88  cnf(c_0_124, negated_conjecture, (k2_relat_1(k7_relat_1(k2_partfun1(esk4_0,esk3_0,esk6_0,esk4_0),k1_xboole_0))=k2_relat_1(k2_partfun1(esk4_0,esk3_0,esk6_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_112]), c_0_87]), c_0_88])])).
% 0.70/0.88  cnf(c_0_125, negated_conjecture, (k9_relat_1(k7_relat_1(X1,X2),k1_relat_1(k2_partfun1(esk5_0,esk3_0,esk7_0,X2)))=k9_relat_1(X1,k1_relat_1(k2_partfun1(esk5_0,esk3_0,esk7_0,X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_68, c_0_113])).
% 0.70/0.88  cnf(c_0_126, negated_conjecture, (k9_relat_1(X1,k1_xboole_0)=k1_xboole_0|k7_relat_1(X1,esk4_0)=k1_xboole_0|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_115]), c_0_79])).
% 0.70/0.88  cnf(c_0_127, negated_conjecture, (k9_subset_1(esk2_0,X1,esk5_0)=k1_setfam_1(k2_tarski(X1,esk5_0))), inference(spm,[status(thm)],[c_0_116, c_0_117])).
% 0.70/0.88  cnf(c_0_128, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_118, c_0_105])).
% 0.70/0.88  cnf(c_0_129, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X2)=X6|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X4)|v1_xboole_0(X1)|X5!=k1_tmap_1(X1,X4,X2,X3,X6,X7)|~v1_funct_1(X5)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|k2_partfun1(X2,X4,X6,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X7,k9_subset_1(X1,X2,X3))|~v1_funct_1(X7)|~v1_funct_2(X7,X3,X4)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X6)|~v1_funct_2(X6,X2,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.70/0.88  cnf(c_0_130, negated_conjecture, (k2_relat_1(k2_partfun1(esk5_0,esk3_0,esk7_0,k1_xboole_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_119]), c_0_94]), c_0_39])])).
% 0.70/0.88  cnf(c_0_131, negated_conjecture, (v1_relat_1(k2_partfun1(esk5_0,esk3_0,esk7_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_94]), c_0_39])])).
% 0.70/0.88  cnf(c_0_132, negated_conjecture, (k7_relat_1(k7_relat_1(X1,esk4_0),k1_xboole_0)=k1_xboole_0|k9_relat_1(X1,k1_xboole_0)!=k1_xboole_0|~v1_relat_1(k7_relat_1(k7_relat_1(X1,esk4_0),k1_xboole_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_120, c_0_121])).
% 0.70/0.88  cnf(c_0_133, negated_conjecture, (k9_relat_1(k1_tmap_1(esk2_0,esk3_0,esk4_0,esk4_0,esk6_0,esk6_0),k1_xboole_0)=k2_relat_1(k2_partfun1(esk4_0,esk3_0,esk6_0,k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_122, c_0_123]), c_0_112]), c_0_124])).
% 0.70/0.88  cnf(c_0_134, negated_conjecture, (k9_relat_1(esk6_0,k1_xboole_0)=k2_relat_1(k2_partfun1(esk4_0,esk3_0,esk6_0,k1_xboole_0))), inference(rw,[status(thm)],[c_0_112, c_0_124])).
% 0.70/0.88  cnf(c_0_135, negated_conjecture, (k9_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_126]), c_0_107]), c_0_65]), c_0_108]), c_0_107]), c_0_65])])).
% 0.70/0.88  cnf(c_0_136, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,X1,esk5_0),X2,k1_tmap_1(esk2_0,X2,X1,esk5_0,X3,X4),esk5_0)=X4|v1_xboole_0(X2)|v1_xboole_0(X1)|k2_partfun1(X1,X2,X3,k1_setfam_1(k2_tarski(X1,esk5_0)))!=k2_partfun1(esk5_0,X2,X4,k1_setfam_1(k2_tarski(X1,esk5_0)))|~v1_funct_2(X4,esk5_0,X2)|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_127]), c_0_117])]), c_0_47])).
% 0.70/0.88  cnf(c_0_137, negated_conjecture, (k1_setfam_1(k2_tarski(esk4_0,esk5_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_128, c_0_54])).
% 0.70/0.88  cnf(c_0_138, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X2)=X5|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_2(X6,X3,X4)|~v1_funct_2(X5,X2,X4)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_129, c_0_50])]), c_0_56]), c_0_60]), c_0_74])).
% 0.70/0.88  cnf(c_0_139, negated_conjecture, (k2_partfun1(esk4_0,esk3_0,esk6_0,k9_subset_1(esk2_0,esk4_0,esk5_0))!=k2_partfun1(esk5_0,esk3_0,esk7_0,k9_subset_1(esk2_0,esk4_0,esk5_0))|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0)!=esk6_0|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0)!=esk7_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.70/0.88  cnf(c_0_140, negated_conjecture, (k2_partfun1(esk5_0,esk3_0,esk7_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_130]), c_0_131])])).
% 0.70/0.88  cnf(c_0_141, negated_conjecture, (k2_partfun1(esk4_0,esk3_0,esk6_0,k1_xboole_0)=k1_xboole_0|k2_relat_1(k2_partfun1(esk4_0,esk3_0,esk6_0,k1_xboole_0))!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_133]), c_0_109]), c_0_123]), c_0_87]), c_0_109]), c_0_123]), c_0_87]), c_0_101]), c_0_110])])).
% 0.70/0.88  cnf(c_0_142, negated_conjecture, (k2_relat_1(k2_partfun1(esk4_0,esk3_0,esk6_0,k1_xboole_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_135]), c_0_88])])).
% 0.70/0.88  cnf(c_0_143, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),X1,k1_tmap_1(esk2_0,X1,esk4_0,esk5_0,X2,X3),esk5_0)=X3|v1_xboole_0(X1)|k2_partfun1(esk4_0,X1,X2,k1_xboole_0)!=k2_partfun1(esk5_0,X1,X3,k1_xboole_0)|~v1_funct_2(X3,esk5_0,X1)|~v1_funct_2(X2,esk4_0,X1)|~v1_funct_1(X2)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_137]), c_0_82])]), c_0_48])).
% 0.70/0.88  cnf(c_0_144, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,X1,esk5_0),X2,k1_tmap_1(esk2_0,X2,X1,esk5_0,X3,X4),X1)=X3|v1_xboole_0(X2)|v1_xboole_0(X1)|k2_partfun1(X1,X2,X3,k1_setfam_1(k2_tarski(X1,esk5_0)))!=k2_partfun1(esk5_0,X2,X4,k1_setfam_1(k2_tarski(X1,esk5_0)))|~v1_funct_2(X4,esk5_0,X2)|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X4)|~v1_funct_1(X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_127]), c_0_117])]), c_0_47])).
% 0.70/0.88  cnf(c_0_145, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0)!=esk6_0|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0)!=esk7_0|k2_partfun1(esk4_0,esk3_0,esk6_0,k1_xboole_0)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_139, c_0_127]), c_0_137]), c_0_140]), c_0_127]), c_0_137])).
% 0.70/0.88  cnf(c_0_146, negated_conjecture, (k2_partfun1(esk4_0,esk3_0,esk6_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_141, c_0_142])])).
% 0.70/0.88  cnf(c_0_147, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,X1,esk7_0),esk5_0)=esk7_0|k2_partfun1(esk4_0,esk3_0,X1,k1_xboole_0)!=k1_xboole_0|~v1_funct_2(X1,esk4_0,esk3_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_140]), c_0_29]), c_0_30]), c_0_31])]), c_0_32])).
% 0.70/0.88  cnf(c_0_148, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),X1,k1_tmap_1(esk2_0,X1,esk4_0,esk5_0,X2,X3),esk4_0)=X2|v1_xboole_0(X1)|k2_partfun1(esk4_0,X1,X2,k1_xboole_0)!=k2_partfun1(esk5_0,X1,X3,k1_xboole_0)|~v1_funct_2(X3,esk5_0,X1)|~v1_funct_2(X2,esk4_0,X1)|~v1_funct_1(X3)|~v1_funct_1(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144, c_0_137]), c_0_82])]), c_0_48])).
% 0.70/0.88  cnf(c_0_149, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0)!=esk6_0|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0)!=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_145, c_0_146])])).
% 0.70/0.88  cnf(c_0_150, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0)=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147, c_0_146]), c_0_57]), c_0_58]), c_0_59])])).
% 0.70/0.88  cnf(c_0_151, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,X1),esk4_0)=esk6_0|k2_partfun1(esk5_0,esk3_0,X1,k1_xboole_0)!=k1_xboole_0|~v1_funct_2(X1,esk5_0,esk3_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_146]), c_0_57]), c_0_58]), c_0_59])]), c_0_32])).
% 0.70/0.88  cnf(c_0_152, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0)!=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_149, c_0_150])])).
% 0.70/0.88  cnf(c_0_153, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151, c_0_140]), c_0_29]), c_0_30]), c_0_31])]), c_0_152]), ['proof']).
% 0.70/0.88  # SZS output end CNFRefutation
% 0.70/0.88  # Proof object total steps             : 154
% 0.70/0.88  # Proof object clause steps            : 110
% 0.70/0.88  # Proof object formula steps           : 44
% 0.70/0.88  # Proof object conjectures             : 74
% 0.70/0.88  # Proof object clause conjectures      : 71
% 0.70/0.88  # Proof object formula conjectures     : 3
% 0.70/0.88  # Proof object initial clauses used    : 39
% 0.70/0.88  # Proof object initial formulas used   : 22
% 0.70/0.88  # Proof object generating inferences   : 57
% 0.70/0.88  # Proof object simplifying inferences  : 157
% 0.70/0.88  # Training examples: 0 positive, 0 negative
% 0.70/0.88  # Parsed axioms                        : 23
% 0.70/0.88  # Removed by relevancy pruning/SinE    : 0
% 0.70/0.88  # Initial clauses                      : 48
% 0.70/0.88  # Removed in clause preprocessing      : 2
% 0.70/0.88  # Initial clauses in saturation        : 46
% 0.70/0.88  # Processed clauses                    : 5502
% 0.70/0.88  # ...of these trivial                  : 267
% 0.70/0.88  # ...subsumed                          : 3762
% 0.70/0.88  # ...remaining for further processing  : 1473
% 0.70/0.88  # Other redundant clauses eliminated   : 5
% 0.70/0.88  # Clauses deleted for lack of memory   : 0
% 0.70/0.88  # Backward-subsumed                    : 89
% 0.70/0.88  # Backward-rewritten                   : 174
% 0.70/0.88  # Generated clauses                    : 27373
% 0.70/0.88  # ...of the previous two non-trivial   : 20605
% 0.70/0.88  # Contextual simplify-reflections      : 135
% 0.70/0.88  # Paramodulations                      : 27358
% 0.70/0.88  # Factorizations                       : 0
% 0.70/0.88  # Equation resolutions                 : 16
% 0.70/0.88  # Propositional unsat checks           : 0
% 0.70/0.88  #    Propositional check models        : 0
% 0.70/0.88  #    Propositional check unsatisfiable : 0
% 0.70/0.88  #    Propositional clauses             : 0
% 0.70/0.88  #    Propositional clauses after purity: 0
% 0.70/0.88  #    Propositional unsat core size     : 0
% 0.70/0.88  #    Propositional preprocessing time  : 0.000
% 0.70/0.88  #    Propositional encoding time       : 0.000
% 0.70/0.88  #    Propositional solver time         : 0.000
% 0.70/0.88  #    Success case prop preproc time    : 0.000
% 0.70/0.88  #    Success case prop encoding time   : 0.000
% 0.70/0.88  #    Success case prop solver time     : 0.000
% 0.70/0.88  # Current number of processed clauses  : 1160
% 0.70/0.88  #    Positive orientable unit clauses  : 240
% 0.70/0.88  #    Positive unorientable unit clauses: 2
% 0.70/0.88  #    Negative unit clauses             : 5
% 0.70/0.88  #    Non-unit-clauses                  : 913
% 0.70/0.88  # Current number of unprocessed clauses: 14299
% 0.70/0.88  # ...number of literals in the above   : 44542
% 0.70/0.88  # Current number of archived formulas  : 0
% 0.70/0.88  # Current number of archived clauses   : 310
% 0.70/0.88  # Clause-clause subsumption calls (NU) : 1202198
% 0.70/0.88  # Rec. Clause-clause subsumption calls : 494814
% 0.70/0.88  # Non-unit clause-clause subsumptions  : 3980
% 0.70/0.88  # Unit Clause-clause subsumption calls : 98725
% 0.70/0.88  # Rewrite failures with RHS unbound    : 0
% 0.70/0.88  # BW rewrite match attempts            : 2709
% 0.70/0.88  # BW rewrite match successes           : 73
% 0.70/0.88  # Condensation attempts                : 0
% 0.70/0.88  # Condensation successes               : 0
% 0.70/0.88  # Termbank termtop insertions          : 942235
% 0.70/0.88  
% 0.70/0.88  # -------------------------------------------------
% 0.70/0.88  # User time                : 0.568 s
% 0.70/0.88  # System time              : 0.013 s
% 0.70/0.88  # Total time               : 0.581 s
% 0.70/0.88  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
