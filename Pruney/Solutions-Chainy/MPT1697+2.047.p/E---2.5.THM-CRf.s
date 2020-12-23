%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:41 EST 2020

% Result     : Theorem 4.05s
% Output     : CNFRefutation 4.05s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 246 expanded)
%              Number of clauses        :   53 (  87 expanded)
%              Number of leaves         :   13 (  63 expanded)
%              Depth                    :    8
%              Number of atoms          :  420 (2456 expanded)
%              Number of equality atoms :   68 ( 390 expanded)
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

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t187_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_xboole_0(X2,k1_relat_1(X1))
         => k7_relat_1(X1,X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

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

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(redefinition_r1_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2) )
     => ( r1_subset_1(X1,X2)
      <=> r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(c_0_13,negated_conjecture,(
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

fof(c_0_14,plain,(
    ! [X45,X46,X47,X48,X49,X50,X51] :
      ( ( k2_partfun1(k4_subset_1(X45,X47,X48),X46,X51,X47) = X49
        | X51 != k1_tmap_1(X45,X46,X47,X48,X49,X50)
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,k4_subset_1(X45,X47,X48),X46)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X45,X47,X48),X46)))
        | k2_partfun1(X47,X46,X49,k9_subset_1(X45,X47,X48)) != k2_partfun1(X48,X46,X50,k9_subset_1(X45,X47,X48))
        | ~ v1_funct_1(X50)
        | ~ v1_funct_2(X50,X48,X46)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X46)))
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,X47,X46)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X46)))
        | v1_xboole_0(X48)
        | ~ m1_subset_1(X48,k1_zfmisc_1(X45))
        | v1_xboole_0(X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(X45))
        | v1_xboole_0(X46)
        | v1_xboole_0(X45) )
      & ( k2_partfun1(k4_subset_1(X45,X47,X48),X46,X51,X48) = X50
        | X51 != k1_tmap_1(X45,X46,X47,X48,X49,X50)
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,k4_subset_1(X45,X47,X48),X46)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X45,X47,X48),X46)))
        | k2_partfun1(X47,X46,X49,k9_subset_1(X45,X47,X48)) != k2_partfun1(X48,X46,X50,k9_subset_1(X45,X47,X48))
        | ~ v1_funct_1(X50)
        | ~ v1_funct_2(X50,X48,X46)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X46)))
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,X47,X46)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X46)))
        | v1_xboole_0(X48)
        | ~ m1_subset_1(X48,k1_zfmisc_1(X45))
        | v1_xboole_0(X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(X45))
        | v1_xboole_0(X46)
        | v1_xboole_0(X45) )
      & ( k2_partfun1(k4_subset_1(X45,X47,X48),X46,X51,X47) != X49
        | k2_partfun1(k4_subset_1(X45,X47,X48),X46,X51,X48) != X50
        | X51 = k1_tmap_1(X45,X46,X47,X48,X49,X50)
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,k4_subset_1(X45,X47,X48),X46)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X45,X47,X48),X46)))
        | k2_partfun1(X47,X46,X49,k9_subset_1(X45,X47,X48)) != k2_partfun1(X48,X46,X50,k9_subset_1(X45,X47,X48))
        | ~ v1_funct_1(X50)
        | ~ v1_funct_2(X50,X48,X46)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X46)))
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,X47,X46)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X46)))
        | v1_xboole_0(X48)
        | ~ m1_subset_1(X48,k1_zfmisc_1(X45))
        | v1_xboole_0(X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(X45))
        | v1_xboole_0(X46)
        | v1_xboole_0(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tmap_1])])])])])).

fof(c_0_15,plain,(
    ! [X52,X53,X54,X55,X56,X57] :
      ( ( v1_funct_1(k1_tmap_1(X52,X53,X54,X55,X56,X57))
        | v1_xboole_0(X52)
        | v1_xboole_0(X53)
        | v1_xboole_0(X54)
        | ~ m1_subset_1(X54,k1_zfmisc_1(X52))
        | v1_xboole_0(X55)
        | ~ m1_subset_1(X55,k1_zfmisc_1(X52))
        | ~ v1_funct_1(X56)
        | ~ v1_funct_2(X56,X54,X53)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X53)))
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,X55,X53)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X53))) )
      & ( v1_funct_2(k1_tmap_1(X52,X53,X54,X55,X56,X57),k4_subset_1(X52,X54,X55),X53)
        | v1_xboole_0(X52)
        | v1_xboole_0(X53)
        | v1_xboole_0(X54)
        | ~ m1_subset_1(X54,k1_zfmisc_1(X52))
        | v1_xboole_0(X55)
        | ~ m1_subset_1(X55,k1_zfmisc_1(X52))
        | ~ v1_funct_1(X56)
        | ~ v1_funct_2(X56,X54,X53)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X53)))
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,X55,X53)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X53))) )
      & ( m1_subset_1(k1_tmap_1(X52,X53,X54,X55,X56,X57),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X52,X54,X55),X53)))
        | v1_xboole_0(X52)
        | v1_xboole_0(X53)
        | v1_xboole_0(X54)
        | ~ m1_subset_1(X54,k1_zfmisc_1(X52))
        | v1_xboole_0(X55)
        | ~ m1_subset_1(X55,k1_zfmisc_1(X52))
        | ~ v1_funct_1(X56)
        | ~ v1_funct_2(X56,X54,X53)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X53)))
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,X55,X53)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X53))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tmap_1])])])])).

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
    ! [X12,X13] :
      ( ( ~ r1_xboole_0(X12,X13)
        | k3_xboole_0(X12,X13) = k1_xboole_0 )
      & ( k3_xboole_0(X12,X13) != k1_xboole_0
        | r1_xboole_0(X12,X13) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_19,plain,(
    ! [X24,X25] : k1_setfam_1(k2_tarski(X24,X25)) = k3_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_20,plain,(
    ! [X20] : k3_xboole_0(X20,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_21,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

cnf(c_0_22,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_26,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X26)
      | ~ r1_xboole_0(X27,k1_relat_1(X26))
      | k7_relat_1(X26,X27) = k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t187_relat_1])])])).

cnf(c_0_27,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( k2_partfun1(esk5_0,esk4_0,esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0)) != k2_partfun1(esk6_0,esk4_0,esk8_0,k9_subset_1(esk3_0,esk5_0,esk6_0))
    | k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk5_0) != esk7_0
    | k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk6_0) != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
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
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_22]),c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_2(esk7_0,esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_2(esk8_0,esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_42,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_43,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_44,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_45,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_46,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_47,plain,(
    ! [X41,X42,X43,X44] :
      ( ~ v1_funct_1(X43)
      | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
      | k2_partfun1(X41,X42,X43,X44) = k7_relat_1(X43,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

cnf(c_0_48,plain,
    ( k7_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_49,plain,
    ( r1_xboole_0(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_50,plain,(
    ! [X30,X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | v1_relat_1(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_51,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(X21))
      | k9_subset_1(X21,X22,X23) = k3_xboole_0(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_52,plain,
    ( r1_xboole_0(X1,X2)
    | k1_setfam_1(k2_tarski(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_53,plain,
    ( k1_setfam_1(k2_tarski(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_31,c_0_30])).

cnf(c_0_54,negated_conjecture,
    ( k2_partfun1(esk6_0,esk4_0,esk8_0,k9_subset_1(esk3_0,esk5_0,esk6_0)) != k2_partfun1(esk5_0,esk4_0,esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0))
    | k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk5_0) != esk7_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41])]),c_0_42]),c_0_43]),c_0_44]),c_0_45])).

cnf(c_0_55,plain,
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
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_46]),c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_56,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_57,plain,
    ( k7_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_58,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_59,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_60,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_61,plain,(
    ! [X28,X29] :
      ( ( ~ r1_subset_1(X28,X29)
        | r1_xboole_0(X28,X29)
        | v1_xboole_0(X28)
        | v1_xboole_0(X29) )
      & ( ~ r1_xboole_0(X28,X29)
        | r1_subset_1(X28,X29)
        | v1_xboole_0(X28)
        | v1_xboole_0(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_63,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_64,negated_conjecture,
    ( k2_partfun1(esk6_0,esk4_0,esk8_0,k9_subset_1(esk3_0,esk5_0,esk6_0)) != k2_partfun1(esk5_0,esk4_0,esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_35]),c_0_34]),c_0_37]),c_0_36]),c_0_39]),c_0_38]),c_0_40]),c_0_41])]),c_0_42]),c_0_43]),c_0_44]),c_0_45])).

cnf(c_0_65,plain,
    ( k2_partfun1(X1,X2,X3,X4) = k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X4) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])).

cnf(c_0_66,plain,
    ( k9_subset_1(X2,X3,X1) = k1_setfam_1(k2_tarski(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_59,c_0_30])).

cnf(c_0_67,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_60,c_0_30])).

cnf(c_0_68,plain,
    ( r1_xboole_0(X1,X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( r1_subset_1(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_70,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_71,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_72,negated_conjecture,
    ( k2_partfun1(esk5_0,esk4_0,esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0)) != k1_xboole_0
    | ~ v1_xboole_0(k9_subset_1(esk3_0,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_37]),c_0_39])])).

cnf(c_0_73,plain,
    ( k9_subset_1(X1,X2,X3) = k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_74,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_44]),c_0_43])).

cnf(c_0_75,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ r2_hidden(esk1_1(k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_76,negated_conjecture,
    ( ~ v1_xboole_0(k9_subset_1(esk3_0,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_65]),c_0_36]),c_0_38])])).

cnf(c_0_77,negated_conjecture,
    ( k9_subset_1(X1,esk5_0,esk6_0) = k1_xboole_0
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_78,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_71])).

cnf(c_0_79,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78]),c_0_40])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:17:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 4.05/4.26  # AutoSched0-Mode selected heuristic G_____0021_C18_F1_SE_CS_SP_S0Y
% 4.05/4.26  # and selection function SelectMaxLComplexAvoidPosPred.
% 4.05/4.26  #
% 4.05/4.26  # Preprocessing time       : 0.030 s
% 4.05/4.26  
% 4.05/4.26  # Proof found!
% 4.05/4.26  # SZS status Theorem
% 4.05/4.26  # SZS output start CNFRefutation
% 4.05/4.26  fof(t6_tmap_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>(r1_subset_1(X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3)=X5)&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4)=X6)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 4.05/4.26  fof(d1_tmap_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>(k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))=>![X7]:(((v1_funct_1(X7)&v1_funct_2(X7,k4_subset_1(X1,X3,X4),X2))&m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))))=>(X7=k1_tmap_1(X1,X2,X3,X4,X5,X6)<=>(k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X3)=X5&k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X4)=X6)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 4.05/4.26  fof(dt_k1_tmap_1, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((((((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))&~(v1_xboole_0(X3)))&m1_subset_1(X3,k1_zfmisc_1(X1)))&~(v1_xboole_0(X4)))&m1_subset_1(X4,k1_zfmisc_1(X1)))&v1_funct_1(X5))&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2))&m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 4.05/4.26  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.05/4.26  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.05/4.26  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.05/4.26  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.05/4.26  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 4.05/4.26  fof(t187_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_xboole_0(X2,k1_relat_1(X1))=>k7_relat_1(X1,X2)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 4.05/4.26  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 4.05/4.26  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.05/4.26  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.05/4.26  fof(redefinition_r1_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))=>(r1_subset_1(X1,X2)<=>r1_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 4.05/4.26  fof(c_0_13, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>(r1_subset_1(X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3)=X5)&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4)=X6))))))))), inference(assume_negation,[status(cth)],[t6_tmap_1])).
% 4.05/4.26  fof(c_0_14, plain, ![X45, X46, X47, X48, X49, X50, X51]:(((k2_partfun1(k4_subset_1(X45,X47,X48),X46,X51,X47)=X49|X51!=k1_tmap_1(X45,X46,X47,X48,X49,X50)|(~v1_funct_1(X51)|~v1_funct_2(X51,k4_subset_1(X45,X47,X48),X46)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X45,X47,X48),X46))))|k2_partfun1(X47,X46,X49,k9_subset_1(X45,X47,X48))!=k2_partfun1(X48,X46,X50,k9_subset_1(X45,X47,X48))|(~v1_funct_1(X50)|~v1_funct_2(X50,X48,X46)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X46))))|(~v1_funct_1(X49)|~v1_funct_2(X49,X47,X46)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X46))))|(v1_xboole_0(X48)|~m1_subset_1(X48,k1_zfmisc_1(X45)))|(v1_xboole_0(X47)|~m1_subset_1(X47,k1_zfmisc_1(X45)))|v1_xboole_0(X46)|v1_xboole_0(X45))&(k2_partfun1(k4_subset_1(X45,X47,X48),X46,X51,X48)=X50|X51!=k1_tmap_1(X45,X46,X47,X48,X49,X50)|(~v1_funct_1(X51)|~v1_funct_2(X51,k4_subset_1(X45,X47,X48),X46)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X45,X47,X48),X46))))|k2_partfun1(X47,X46,X49,k9_subset_1(X45,X47,X48))!=k2_partfun1(X48,X46,X50,k9_subset_1(X45,X47,X48))|(~v1_funct_1(X50)|~v1_funct_2(X50,X48,X46)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X46))))|(~v1_funct_1(X49)|~v1_funct_2(X49,X47,X46)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X46))))|(v1_xboole_0(X48)|~m1_subset_1(X48,k1_zfmisc_1(X45)))|(v1_xboole_0(X47)|~m1_subset_1(X47,k1_zfmisc_1(X45)))|v1_xboole_0(X46)|v1_xboole_0(X45)))&(k2_partfun1(k4_subset_1(X45,X47,X48),X46,X51,X47)!=X49|k2_partfun1(k4_subset_1(X45,X47,X48),X46,X51,X48)!=X50|X51=k1_tmap_1(X45,X46,X47,X48,X49,X50)|(~v1_funct_1(X51)|~v1_funct_2(X51,k4_subset_1(X45,X47,X48),X46)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X45,X47,X48),X46))))|k2_partfun1(X47,X46,X49,k9_subset_1(X45,X47,X48))!=k2_partfun1(X48,X46,X50,k9_subset_1(X45,X47,X48))|(~v1_funct_1(X50)|~v1_funct_2(X50,X48,X46)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X46))))|(~v1_funct_1(X49)|~v1_funct_2(X49,X47,X46)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X46))))|(v1_xboole_0(X48)|~m1_subset_1(X48,k1_zfmisc_1(X45)))|(v1_xboole_0(X47)|~m1_subset_1(X47,k1_zfmisc_1(X45)))|v1_xboole_0(X46)|v1_xboole_0(X45))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tmap_1])])])])])).
% 4.05/4.26  fof(c_0_15, plain, ![X52, X53, X54, X55, X56, X57]:(((v1_funct_1(k1_tmap_1(X52,X53,X54,X55,X56,X57))|(v1_xboole_0(X52)|v1_xboole_0(X53)|v1_xboole_0(X54)|~m1_subset_1(X54,k1_zfmisc_1(X52))|v1_xboole_0(X55)|~m1_subset_1(X55,k1_zfmisc_1(X52))|~v1_funct_1(X56)|~v1_funct_2(X56,X54,X53)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X53)))|~v1_funct_1(X57)|~v1_funct_2(X57,X55,X53)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X53)))))&(v1_funct_2(k1_tmap_1(X52,X53,X54,X55,X56,X57),k4_subset_1(X52,X54,X55),X53)|(v1_xboole_0(X52)|v1_xboole_0(X53)|v1_xboole_0(X54)|~m1_subset_1(X54,k1_zfmisc_1(X52))|v1_xboole_0(X55)|~m1_subset_1(X55,k1_zfmisc_1(X52))|~v1_funct_1(X56)|~v1_funct_2(X56,X54,X53)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X53)))|~v1_funct_1(X57)|~v1_funct_2(X57,X55,X53)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X53))))))&(m1_subset_1(k1_tmap_1(X52,X53,X54,X55,X56,X57),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X52,X54,X55),X53)))|(v1_xboole_0(X52)|v1_xboole_0(X53)|v1_xboole_0(X54)|~m1_subset_1(X54,k1_zfmisc_1(X52))|v1_xboole_0(X55)|~m1_subset_1(X55,k1_zfmisc_1(X52))|~v1_funct_1(X56)|~v1_funct_2(X56,X54,X53)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X53)))|~v1_funct_1(X57)|~v1_funct_2(X57,X55,X53)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X53)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tmap_1])])])])).
% 4.05/4.26  fof(c_0_16, plain, ![X8, X9, X10]:((~v1_xboole_0(X8)|~r2_hidden(X9,X8))&(r2_hidden(esk1_1(X10),X10)|v1_xboole_0(X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 4.05/4.26  fof(c_0_17, plain, ![X14, X15, X17, X18, X19]:(((r2_hidden(esk2_2(X14,X15),X14)|r1_xboole_0(X14,X15))&(r2_hidden(esk2_2(X14,X15),X15)|r1_xboole_0(X14,X15)))&(~r2_hidden(X19,X17)|~r2_hidden(X19,X18)|~r1_xboole_0(X17,X18))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 4.05/4.26  fof(c_0_18, plain, ![X12, X13]:((~r1_xboole_0(X12,X13)|k3_xboole_0(X12,X13)=k1_xboole_0)&(k3_xboole_0(X12,X13)!=k1_xboole_0|r1_xboole_0(X12,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 4.05/4.26  fof(c_0_19, plain, ![X24, X25]:k1_setfam_1(k2_tarski(X24,X25))=k3_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 4.05/4.26  fof(c_0_20, plain, ![X20]:k3_xboole_0(X20,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 4.05/4.26  fof(c_0_21, negated_conjecture, (~v1_xboole_0(esk3_0)&(~v1_xboole_0(esk4_0)&((~v1_xboole_0(esk5_0)&m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0)))&((~v1_xboole_0(esk6_0)&m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0)))&(r1_subset_1(esk5_0,esk6_0)&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk5_0,esk4_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0))))&(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk6_0,esk4_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk4_0))))&(k2_partfun1(esk5_0,esk4_0,esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0))!=k2_partfun1(esk6_0,esk4_0,esk8_0,k9_subset_1(esk3_0,esk5_0,esk6_0))|k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk5_0)!=esk7_0|k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk6_0)!=esk8_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 4.05/4.26  cnf(c_0_22, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X3)=X6|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X4)|v1_xboole_0(X1)|X5!=k1_tmap_1(X1,X4,X2,X3,X7,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|k2_partfun1(X2,X4,X7,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_1(X6)|~v1_funct_2(X6,X3,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X7)|~v1_funct_2(X7,X2,X4)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 4.05/4.26  cnf(c_0_23, plain, (m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2)))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 4.05/4.26  cnf(c_0_24, plain, (v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 4.05/4.26  cnf(c_0_25, plain, (v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 4.05/4.26  fof(c_0_26, plain, ![X26, X27]:(~v1_relat_1(X26)|(~r1_xboole_0(X27,k1_relat_1(X26))|k7_relat_1(X26,X27)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t187_relat_1])])])).
% 4.05/4.26  cnf(c_0_27, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 4.05/4.26  cnf(c_0_28, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 4.05/4.26  cnf(c_0_29, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 4.05/4.26  cnf(c_0_30, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 4.05/4.26  cnf(c_0_31, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 4.05/4.26  cnf(c_0_32, negated_conjecture, (k2_partfun1(esk5_0,esk4_0,esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0))!=k2_partfun1(esk6_0,esk4_0,esk8_0,k9_subset_1(esk3_0,esk5_0,esk6_0))|k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk5_0)!=esk7_0|k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk6_0)!=esk8_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.05/4.26  cnf(c_0_33, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X3)=X6|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_2(X5,X2,X4)|~v1_funct_2(X6,X3,X4)|~v1_funct_1(X5)|~v1_funct_1(X6)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_22]), c_0_23]), c_0_24]), c_0_25])).
% 4.05/4.26  cnf(c_0_34, negated_conjecture, (v1_funct_2(esk7_0,esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.05/4.26  cnf(c_0_35, negated_conjecture, (v1_funct_2(esk8_0,esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.05/4.26  cnf(c_0_36, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.05/4.26  cnf(c_0_37, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.05/4.26  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.05/4.26  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.05/4.26  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.05/4.26  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.05/4.26  cnf(c_0_42, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.05/4.26  cnf(c_0_43, negated_conjecture, (~v1_xboole_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.05/4.26  cnf(c_0_44, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.05/4.26  cnf(c_0_45, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.05/4.26  cnf(c_0_46, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X2)=X6|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X4)|v1_xboole_0(X1)|X5!=k1_tmap_1(X1,X4,X2,X3,X6,X7)|~v1_funct_1(X5)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|k2_partfun1(X2,X4,X6,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X7,k9_subset_1(X1,X2,X3))|~v1_funct_1(X7)|~v1_funct_2(X7,X3,X4)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X6)|~v1_funct_2(X6,X2,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 4.05/4.26  fof(c_0_47, plain, ![X41, X42, X43, X44]:(~v1_funct_1(X43)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|k2_partfun1(X41,X42,X43,X44)=k7_relat_1(X43,X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 4.05/4.26  cnf(c_0_48, plain, (k7_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 4.05/4.26  cnf(c_0_49, plain, (r1_xboole_0(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 4.05/4.26  fof(c_0_50, plain, ![X30, X31, X32]:(~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|v1_relat_1(X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 4.05/4.26  fof(c_0_51, plain, ![X21, X22, X23]:(~m1_subset_1(X23,k1_zfmisc_1(X21))|k9_subset_1(X21,X22,X23)=k3_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 4.05/4.26  cnf(c_0_52, plain, (r1_xboole_0(X1,X2)|k1_setfam_1(k2_tarski(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 4.05/4.26  cnf(c_0_53, plain, (k1_setfam_1(k2_tarski(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_31, c_0_30])).
% 4.05/4.26  cnf(c_0_54, negated_conjecture, (k2_partfun1(esk6_0,esk4_0,esk8_0,k9_subset_1(esk3_0,esk5_0,esk6_0))!=k2_partfun1(esk5_0,esk4_0,esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0))|k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk5_0)!=esk7_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41])]), c_0_42]), c_0_43]), c_0_44]), c_0_45])).
% 4.05/4.26  cnf(c_0_55, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X2)=X5|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_2(X6,X3,X4)|~v1_funct_2(X5,X2,X4)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_46]), c_0_23]), c_0_24]), c_0_25])).
% 4.05/4.26  cnf(c_0_56, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 4.05/4.26  cnf(c_0_57, plain, (k7_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 4.05/4.26  cnf(c_0_58, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 4.05/4.26  cnf(c_0_59, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 4.05/4.26  cnf(c_0_60, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 4.05/4.26  fof(c_0_61, plain, ![X28, X29]:((~r1_subset_1(X28,X29)|r1_xboole_0(X28,X29)|(v1_xboole_0(X28)|v1_xboole_0(X29)))&(~r1_xboole_0(X28,X29)|r1_subset_1(X28,X29)|(v1_xboole_0(X28)|v1_xboole_0(X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).
% 4.05/4.26  cnf(c_0_62, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 4.05/4.26  cnf(c_0_63, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 4.05/4.26  cnf(c_0_64, negated_conjecture, (k2_partfun1(esk6_0,esk4_0,esk8_0,k9_subset_1(esk3_0,esk5_0,esk6_0))!=k2_partfun1(esk5_0,esk4_0,esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_35]), c_0_34]), c_0_37]), c_0_36]), c_0_39]), c_0_38]), c_0_40]), c_0_41])]), c_0_42]), c_0_43]), c_0_44]), c_0_45])).
% 4.05/4.26  cnf(c_0_65, plain, (k2_partfun1(X1,X2,X3,X4)=k1_xboole_0|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_xboole_0(X4)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])).
% 4.05/4.26  cnf(c_0_66, plain, (k9_subset_1(X2,X3,X1)=k1_setfam_1(k2_tarski(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_59, c_0_30])).
% 4.05/4.26  cnf(c_0_67, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_60, c_0_30])).
% 4.05/4.26  cnf(c_0_68, plain, (r1_xboole_0(X1,X2)|v1_xboole_0(X1)|v1_xboole_0(X2)|~r1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 4.05/4.26  cnf(c_0_69, negated_conjecture, (r1_subset_1(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.05/4.26  cnf(c_0_70, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 4.05/4.26  cnf(c_0_71, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 4.05/4.26  cnf(c_0_72, negated_conjecture, (k2_partfun1(esk5_0,esk4_0,esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0))!=k1_xboole_0|~v1_xboole_0(k9_subset_1(esk3_0,esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_37]), c_0_39])])).
% 4.05/4.26  cnf(c_0_73, plain, (k9_subset_1(X1,X2,X3)=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(X1))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 4.05/4.26  cnf(c_0_74, negated_conjecture, (r1_xboole_0(esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_44]), c_0_43])).
% 4.05/4.26  cnf(c_0_75, plain, (v1_xboole_0(k1_xboole_0)|~r2_hidden(esk1_1(k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 4.05/4.26  cnf(c_0_76, negated_conjecture, (~v1_xboole_0(k9_subset_1(esk3_0,esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_65]), c_0_36]), c_0_38])])).
% 4.05/4.26  cnf(c_0_77, negated_conjecture, (k9_subset_1(X1,esk5_0,esk6_0)=k1_xboole_0|~m1_subset_1(esk6_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 4.05/4.26  cnf(c_0_78, plain, (v1_xboole_0(k1_xboole_0)), inference(spm,[status(thm)],[c_0_75, c_0_71])).
% 4.05/4.26  cnf(c_0_79, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78]), c_0_40])]), ['proof']).
% 4.05/4.26  # SZS output end CNFRefutation
% 4.05/4.26  # Proof object total steps             : 80
% 4.05/4.26  # Proof object clause steps            : 53
% 4.05/4.26  # Proof object formula steps           : 27
% 4.05/4.26  # Proof object conjectures             : 24
% 4.05/4.26  # Proof object clause conjectures      : 21
% 4.05/4.26  # Proof object formula conjectures     : 3
% 4.05/4.26  # Proof object initial clauses used    : 32
% 4.05/4.26  # Proof object initial formulas used   : 13
% 4.05/4.26  # Proof object generating inferences   : 15
% 4.05/4.26  # Proof object simplifying inferences  : 50
% 4.05/4.26  # Training examples: 0 positive, 0 negative
% 4.05/4.26  # Parsed axioms                        : 16
% 4.05/4.26  # Removed by relevancy pruning/SinE    : 0
% 4.05/4.26  # Initial clauses                      : 41
% 4.05/4.26  # Removed in clause preprocessing      : 2
% 4.05/4.26  # Initial clauses in saturation        : 39
% 4.05/4.26  # Processed clauses                    : 9785
% 4.05/4.26  # ...of these trivial                  : 0
% 4.05/4.26  # ...subsumed                          : 7891
% 4.05/4.26  # ...remaining for further processing  : 1894
% 4.05/4.26  # Other redundant clauses eliminated   : 6937
% 4.05/4.26  # Clauses deleted for lack of memory   : 0
% 4.05/4.26  # Backward-subsumed                    : 432
% 4.05/4.26  # Backward-rewritten                   : 8
% 4.05/4.26  # Generated clauses                    : 40882
% 4.05/4.26  # ...of the previous two non-trivial   : 26918
% 4.05/4.26  # Contextual simplify-reflections      : 323
% 4.05/4.26  # Paramodulations                      : 33898
% 4.05/4.26  # Factorizations                       : 0
% 4.05/4.26  # Equation resolutions                 : 6985
% 4.05/4.26  # Propositional unsat checks           : 0
% 4.05/4.26  #    Propositional check models        : 0
% 4.05/4.26  #    Propositional check unsatisfiable : 0
% 4.05/4.26  #    Propositional clauses             : 0
% 4.05/4.26  #    Propositional clauses after purity: 0
% 4.05/4.26  #    Propositional unsat core size     : 0
% 4.05/4.26  #    Propositional preprocessing time  : 0.000
% 4.05/4.26  #    Propositional encoding time       : 0.000
% 4.05/4.26  #    Propositional solver time         : 0.000
% 4.05/4.26  #    Success case prop preproc time    : 0.000
% 4.05/4.26  #    Success case prop encoding time   : 0.000
% 4.05/4.26  #    Success case prop solver time     : 0.000
% 4.05/4.26  # Current number of processed clauses  : 1450
% 4.05/4.26  #    Positive orientable unit clauses  : 35
% 4.05/4.26  #    Positive unorientable unit clauses: 0
% 4.05/4.26  #    Negative unit clauses             : 7
% 4.05/4.26  #    Non-unit-clauses                  : 1408
% 4.05/4.26  # Current number of unprocessed clauses: 16795
% 4.05/4.26  # ...number of literals in the above   : 439551
% 4.05/4.26  # Current number of archived formulas  : 0
% 4.05/4.26  # Current number of archived clauses   : 441
% 4.05/4.26  # Clause-clause subsumption calls (NU) : 2865341
% 4.05/4.26  # Rec. Clause-clause subsumption calls : 51786
% 4.05/4.26  # Non-unit clause-clause subsumptions  : 8007
% 4.05/4.26  # Unit Clause-clause subsumption calls : 677
% 4.05/4.26  # Rewrite failures with RHS unbound    : 0
% 4.05/4.26  # BW rewrite match attempts            : 8
% 4.05/4.26  # BW rewrite match successes           : 8
% 4.05/4.26  # Condensation attempts                : 0
% 4.05/4.26  # Condensation successes               : 0
% 4.05/4.26  # Termbank termtop insertions          : 3398956
% 4.05/4.27  
% 4.05/4.27  # -------------------------------------------------
% 4.05/4.27  # User time                : 3.895 s
% 4.05/4.27  # System time              : 0.024 s
% 4.05/4.27  # Total time               : 3.919 s
% 4.05/4.27  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
