%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:35 EST 2020

% Result     : Theorem 10.60s
% Output     : CNFRefutation 10.60s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 479 expanded)
%              Number of clauses        :   75 ( 176 expanded)
%              Number of leaves         :   19 ( 122 expanded)
%              Depth                    :   13
%              Number of atoms          :  554 (4226 expanded)
%              Number of equality atoms :   95 ( 705 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal clause size      :   55 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(cc3_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_funct_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

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

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(t68_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( ( k1_relat_1(X2) = k3_xboole_0(k1_relat_1(X3),X1)
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X2))
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) )
           => X2 = k7_relat_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_funct_1)).

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(redefinition_r1_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2) )
     => ( r1_subset_1(X1,X2)
      <=> r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(c_0_19,plain,(
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

fof(c_0_20,plain,(
    ! [X22,X23] :
      ( ~ v1_xboole_0(X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(X22))
      | v1_xboole_0(X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

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
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_27,plain,(
    ! [X27,X28] :
      ( ~ v1_relat_1(X27)
      | ~ v1_funct_1(X27)
      | ~ m1_subset_1(X28,k1_zfmisc_1(X27))
      | v1_funct_1(X28) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_funct_1])])])).

fof(c_0_28,plain,(
    ! [X21] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X21)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_29,plain,(
    ! [X35,X36,X37] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | v1_relat_1(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_30,negated_conjecture,
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

cnf(c_0_31,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | m1_subset_1(k1_tmap_1(X4,X1,X2,X3,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X4,X2,X3),X1)))
    | ~ v1_funct_2(X6,X3,X1)
    | ~ v1_funct_2(X5,X2,X1)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(csr,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_33,plain,
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
    inference(csr,[status(thm)],[c_0_25,c_0_24])).

cnf(c_0_34,plain,
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
    inference(csr,[status(thm)],[c_0_26,c_0_24])).

cnf(c_0_35,plain,
    ( v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_39,plain,(
    ! [X10,X11,X13,X14,X15] :
      ( ( r1_xboole_0(X10,X11)
        | r2_hidden(esk1_2(X10,X11),k3_xboole_0(X10,X11)) )
      & ( ~ r2_hidden(X15,k3_xboole_0(X13,X14))
        | ~ r1_xboole_0(X13,X14) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_40,plain,(
    ! [X16] : k3_xboole_0(X16,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_41,plain,(
    ! [X17] : r1_xboole_0(X17,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_42,plain,(
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

fof(c_0_43,plain,(
    ! [X38,X39,X40] :
      ( ( v4_relat_1(X40,X38)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( v5_relat_1(X40,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_44,negated_conjecture,
    ( k2_partfun1(esk5_0,esk4_0,esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0)) != k2_partfun1(esk6_0,esk4_0,esk8_0,k9_subset_1(esk3_0,esk5_0,esk6_0))
    | k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk5_0) != esk7_0
    | k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk6_0) != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_45,plain,
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
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_31,c_0_24])]),c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_2(esk7_0,esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_2(esk8_0,esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_49,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_53,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_54,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_55,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_56,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_57,plain,(
    ! [X46,X47,X48,X49] :
      ( ~ v1_funct_1(X48)
      | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))
      | k2_partfun1(X46,X47,X48,X49) = k7_relat_1(X48,X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

fof(c_0_58,plain,(
    ! [X31,X32,X33] :
      ( ( r2_hidden(esk2_3(X31,X32,X33),k1_relat_1(X32))
        | k1_relat_1(X32) != k3_xboole_0(k1_relat_1(X33),X31)
        | X32 = k7_relat_1(X33,X31)
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( k1_funct_1(X32,esk2_3(X31,X32,X33)) != k1_funct_1(X33,esk2_3(X31,X32,X33))
        | k1_relat_1(X32) != k3_xboole_0(k1_relat_1(X33),X31)
        | X32 = k7_relat_1(X33,X31)
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t68_funct_1])])])])])).

cnf(c_0_59,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_60,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_61,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_62,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_63,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_64,plain,(
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

cnf(c_0_65,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_66,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_67,negated_conjecture,
    ( k2_partfun1(esk6_0,esk4_0,esk8_0,k9_subset_1(esk3_0,esk5_0,esk6_0)) != k2_partfun1(esk5_0,esk4_0,esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0))
    | k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk5_0) != esk7_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47]),c_0_48]),c_0_49]),c_0_50]),c_0_38]),c_0_51]),c_0_52])]),c_0_53]),c_0_54]),c_0_55])).

cnf(c_0_68,plain,
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
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_56,c_0_24])]),c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_69,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_70,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X2))
    | X2 = k7_relat_1(X3,X1)
    | k1_relat_1(X2) != k3_xboole_0(k1_relat_1(X3),X1)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_71,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_72,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_49])])).

cnf(c_0_73,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_36])).

cnf(c_0_74,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])])).

cnf(c_0_75,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_76,negated_conjecture,
    ( v1_partfun1(esk8_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_38]),c_0_47]),c_0_49])]),c_0_53])).

cnf(c_0_77,negated_conjecture,
    ( v4_relat_1(esk8_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_38])).

cnf(c_0_78,negated_conjecture,
    ( v1_partfun1(esk7_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_50]),c_0_46]),c_0_48])]),c_0_53])).

cnf(c_0_79,negated_conjecture,
    ( v4_relat_1(esk7_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_50])).

cnf(c_0_80,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_50])).

cnf(c_0_81,negated_conjecture,
    ( k2_partfun1(esk6_0,esk4_0,esk8_0,k9_subset_1(esk3_0,esk5_0,esk6_0)) != k2_partfun1(esk5_0,esk4_0,esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_47]),c_0_46]),c_0_49]),c_0_48]),c_0_38]),c_0_50]),c_0_51]),c_0_52])]),c_0_53]),c_0_54]),c_0_55])).

cnf(c_0_82,plain,
    ( k2_partfun1(X1,X2,X3,X4) = k2_partfun1(X5,X6,X3,X4)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_69])).

cnf(c_0_83,plain,
    ( k7_relat_1(X1,X2) = k1_xboole_0
    | k3_xboole_0(k1_relat_1(X1),X2) != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72]),c_0_73])]),c_0_74])).

cnf(c_0_84,negated_conjecture,
    ( k1_relat_1(esk8_0) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77]),c_0_60])])).

cnf(c_0_85,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_78]),c_0_79]),c_0_80])])).

cnf(c_0_86,negated_conjecture,
    ( k2_partfun1(X1,X2,esk8_0,k9_subset_1(esk3_0,esk5_0,esk6_0)) != k2_partfun1(esk5_0,esk4_0,esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0))
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_49]),c_0_38])])).

fof(c_0_87,plain,(
    ! [X29,X30] :
      ( ( ~ r1_subset_1(X29,X30)
        | r1_xboole_0(X29,X30)
        | v1_xboole_0(X29)
        | v1_xboole_0(X30) )
      & ( ~ r1_xboole_0(X29,X30)
        | r1_subset_1(X29,X30)
        | v1_xboole_0(X29)
        | v1_xboole_0(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).

cnf(c_0_88,negated_conjecture,
    ( k7_relat_1(esk8_0,X1) = k1_xboole_0
    | k3_xboole_0(esk6_0,X1) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_49]),c_0_60])])).

cnf(c_0_89,negated_conjecture,
    ( k7_relat_1(esk7_0,X1) = k1_xboole_0
    | k3_xboole_0(esk5_0,X1) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_85]),c_0_48]),c_0_80])])).

cnf(c_0_90,negated_conjecture,
    ( k2_partfun1(X1,X2,esk8_0,k9_subset_1(esk3_0,esk5_0,esk6_0)) != k2_partfun1(X3,X4,esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0))
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_82]),c_0_48]),c_0_50])])).

fof(c_0_91,plain,(
    ! [X8,X9] :
      ( ( ~ r1_xboole_0(X8,X9)
        | k3_xboole_0(X8,X9) = k1_xboole_0 )
      & ( k3_xboole_0(X8,X9) != k1_xboole_0
        | r1_xboole_0(X8,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_92,plain,
    ( r1_xboole_0(X1,X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_93,negated_conjecture,
    ( r1_subset_1(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_94,negated_conjecture,
    ( k2_partfun1(X1,X2,esk8_0,X3) = k1_xboole_0
    | k3_xboole_0(esk6_0,X3) != k1_xboole_0
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_88]),c_0_49])])).

cnf(c_0_95,negated_conjecture,
    ( k2_partfun1(X1,X2,esk7_0,X3) = k1_xboole_0
    | k3_xboole_0(esk5_0,X3) != k1_xboole_0
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_89]),c_0_48])])).

cnf(c_0_96,negated_conjecture,
    ( k2_partfun1(X1,X2,esk8_0,k9_subset_1(esk3_0,esk5_0,esk6_0)) != k7_relat_1(esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0))
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_69]),c_0_48])])).

fof(c_0_97,plain,(
    ! [X18,X19,X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(X18))
      | k9_subset_1(X18,X19,X20) = k3_xboole_0(X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_98,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_99,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_55]),c_0_54])).

cnf(c_0_100,negated_conjecture,
    ( k2_partfun1(X1,X2,esk8_0,k1_xboole_0) = k1_xboole_0
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_94,c_0_62])).

cnf(c_0_101,negated_conjecture,
    ( k2_partfun1(X1,X2,esk7_0,k1_xboole_0) = k1_xboole_0
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_95,c_0_62])).

cnf(c_0_102,negated_conjecture,
    ( k2_partfun1(X1,X2,esk8_0,k9_subset_1(esk3_0,esk5_0,esk6_0)) != k7_relat_1(esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0))
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_96,c_0_50])).

cnf(c_0_103,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_104,negated_conjecture,
    ( k3_xboole_0(esk5_0,esk6_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_105,negated_conjecture,
    ( k7_relat_1(esk8_0,k1_xboole_0) = k1_xboole_0
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_100]),c_0_49])])).

cnf(c_0_106,negated_conjecture,
    ( k7_relat_1(esk7_0,k1_xboole_0) = k1_xboole_0
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_101]),c_0_48])])).

cnf(c_0_107,negated_conjecture,
    ( k7_relat_1(esk8_0,k9_subset_1(esk3_0,esk5_0,esk6_0)) != k7_relat_1(esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0))
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_69]),c_0_49])])).

cnf(c_0_108,negated_conjecture,
    ( k9_subset_1(X1,esk5_0,esk6_0) = k1_xboole_0
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_109,negated_conjecture,
    ( k7_relat_1(esk8_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_105,c_0_38])).

cnf(c_0_110,negated_conjecture,
    ( k7_relat_1(esk7_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_106,c_0_50])).

cnf(c_0_111,negated_conjecture,
    ( ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_109]),c_0_110]),c_0_51])])).

cnf(c_0_112,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_38,c_0_111]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:22:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 10.60/10.77  # AutoSched0-Mode selected heuristic G_____0021_C18_F1_SE_CS_SP_S0Y
% 10.60/10.77  # and selection function SelectMaxLComplexAvoidPosPred.
% 10.60/10.77  #
% 10.60/10.77  # Preprocessing time       : 0.030 s
% 10.60/10.77  
% 10.60/10.77  # Proof found!
% 10.60/10.77  # SZS status Theorem
% 10.60/10.77  # SZS output start CNFRefutation
% 10.60/10.77  fof(dt_k1_tmap_1, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((((((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))&~(v1_xboole_0(X3)))&m1_subset_1(X3,k1_zfmisc_1(X1)))&~(v1_xboole_0(X4)))&m1_subset_1(X4,k1_zfmisc_1(X1)))&v1_funct_1(X5))&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2))&m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 10.60/10.77  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 10.60/10.77  fof(t6_tmap_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>(r1_subset_1(X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3)=X5)&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4)=X6)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 10.60/10.77  fof(d1_tmap_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>(k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))=>![X7]:(((v1_funct_1(X7)&v1_funct_2(X7,k4_subset_1(X1,X3,X4),X2))&m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))))=>(X7=k1_tmap_1(X1,X2,X3,X4,X5,X6)<=>(k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X3)=X5&k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X4)=X6)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 10.60/10.77  fof(cc3_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_funct_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_funct_1)).
% 10.60/10.77  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 10.60/10.77  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.60/10.77  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 10.60/10.77  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 10.60/10.77  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 10.60/10.77  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 10.60/10.77  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.60/10.77  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 10.60/10.77  fof(t68_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X2)=k3_xboole_0(k1_relat_1(X3),X1)&![X4]:(r2_hidden(X4,k1_relat_1(X2))=>k1_funct_1(X2,X4)=k1_funct_1(X3,X4)))=>X2=k7_relat_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_funct_1)).
% 10.60/10.77  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 10.60/10.77  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 10.60/10.77  fof(redefinition_r1_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))=>(r1_subset_1(X1,X2)<=>r1_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 10.60/10.77  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 10.60/10.77  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 10.60/10.77  fof(c_0_19, plain, ![X57, X58, X59, X60, X61, X62]:(((v1_funct_1(k1_tmap_1(X57,X58,X59,X60,X61,X62))|(v1_xboole_0(X57)|v1_xboole_0(X58)|v1_xboole_0(X59)|~m1_subset_1(X59,k1_zfmisc_1(X57))|v1_xboole_0(X60)|~m1_subset_1(X60,k1_zfmisc_1(X57))|~v1_funct_1(X61)|~v1_funct_2(X61,X59,X58)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X58)))|~v1_funct_1(X62)|~v1_funct_2(X62,X60,X58)|~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X58)))))&(v1_funct_2(k1_tmap_1(X57,X58,X59,X60,X61,X62),k4_subset_1(X57,X59,X60),X58)|(v1_xboole_0(X57)|v1_xboole_0(X58)|v1_xboole_0(X59)|~m1_subset_1(X59,k1_zfmisc_1(X57))|v1_xboole_0(X60)|~m1_subset_1(X60,k1_zfmisc_1(X57))|~v1_funct_1(X61)|~v1_funct_2(X61,X59,X58)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X58)))|~v1_funct_1(X62)|~v1_funct_2(X62,X60,X58)|~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X58))))))&(m1_subset_1(k1_tmap_1(X57,X58,X59,X60,X61,X62),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X57,X59,X60),X58)))|(v1_xboole_0(X57)|v1_xboole_0(X58)|v1_xboole_0(X59)|~m1_subset_1(X59,k1_zfmisc_1(X57))|v1_xboole_0(X60)|~m1_subset_1(X60,k1_zfmisc_1(X57))|~v1_funct_1(X61)|~v1_funct_2(X61,X59,X58)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X58)))|~v1_funct_1(X62)|~v1_funct_2(X62,X60,X58)|~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X58)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tmap_1])])])])).
% 10.60/10.77  fof(c_0_20, plain, ![X22, X23]:(~v1_xboole_0(X22)|(~m1_subset_1(X23,k1_zfmisc_1(X22))|v1_xboole_0(X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 10.60/10.77  fof(c_0_21, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>(r1_subset_1(X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3)=X5)&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4)=X6))))))))), inference(assume_negation,[status(cth)],[t6_tmap_1])).
% 10.60/10.77  fof(c_0_22, plain, ![X50, X51, X52, X53, X54, X55, X56]:(((k2_partfun1(k4_subset_1(X50,X52,X53),X51,X56,X52)=X54|X56!=k1_tmap_1(X50,X51,X52,X53,X54,X55)|(~v1_funct_1(X56)|~v1_funct_2(X56,k4_subset_1(X50,X52,X53),X51)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X50,X52,X53),X51))))|k2_partfun1(X52,X51,X54,k9_subset_1(X50,X52,X53))!=k2_partfun1(X53,X51,X55,k9_subset_1(X50,X52,X53))|(~v1_funct_1(X55)|~v1_funct_2(X55,X53,X51)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X51))))|(~v1_funct_1(X54)|~v1_funct_2(X54,X52,X51)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X51))))|(v1_xboole_0(X53)|~m1_subset_1(X53,k1_zfmisc_1(X50)))|(v1_xboole_0(X52)|~m1_subset_1(X52,k1_zfmisc_1(X50)))|v1_xboole_0(X51)|v1_xboole_0(X50))&(k2_partfun1(k4_subset_1(X50,X52,X53),X51,X56,X53)=X55|X56!=k1_tmap_1(X50,X51,X52,X53,X54,X55)|(~v1_funct_1(X56)|~v1_funct_2(X56,k4_subset_1(X50,X52,X53),X51)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X50,X52,X53),X51))))|k2_partfun1(X52,X51,X54,k9_subset_1(X50,X52,X53))!=k2_partfun1(X53,X51,X55,k9_subset_1(X50,X52,X53))|(~v1_funct_1(X55)|~v1_funct_2(X55,X53,X51)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X51))))|(~v1_funct_1(X54)|~v1_funct_2(X54,X52,X51)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X51))))|(v1_xboole_0(X53)|~m1_subset_1(X53,k1_zfmisc_1(X50)))|(v1_xboole_0(X52)|~m1_subset_1(X52,k1_zfmisc_1(X50)))|v1_xboole_0(X51)|v1_xboole_0(X50)))&(k2_partfun1(k4_subset_1(X50,X52,X53),X51,X56,X52)!=X54|k2_partfun1(k4_subset_1(X50,X52,X53),X51,X56,X53)!=X55|X56=k1_tmap_1(X50,X51,X52,X53,X54,X55)|(~v1_funct_1(X56)|~v1_funct_2(X56,k4_subset_1(X50,X52,X53),X51)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X50,X52,X53),X51))))|k2_partfun1(X52,X51,X54,k9_subset_1(X50,X52,X53))!=k2_partfun1(X53,X51,X55,k9_subset_1(X50,X52,X53))|(~v1_funct_1(X55)|~v1_funct_2(X55,X53,X51)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X51))))|(~v1_funct_1(X54)|~v1_funct_2(X54,X52,X51)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X51))))|(v1_xboole_0(X53)|~m1_subset_1(X53,k1_zfmisc_1(X50)))|(v1_xboole_0(X52)|~m1_subset_1(X52,k1_zfmisc_1(X50)))|v1_xboole_0(X51)|v1_xboole_0(X50))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tmap_1])])])])])).
% 10.60/10.77  cnf(c_0_23, plain, (m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2)))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 10.60/10.77  cnf(c_0_24, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 10.60/10.77  cnf(c_0_25, plain, (v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 10.60/10.77  cnf(c_0_26, plain, (v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 10.60/10.77  fof(c_0_27, plain, ![X27, X28]:(~v1_relat_1(X27)|~v1_funct_1(X27)|(~m1_subset_1(X28,k1_zfmisc_1(X27))|v1_funct_1(X28))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_funct_1])])])).
% 10.60/10.77  fof(c_0_28, plain, ![X21]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X21)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 10.60/10.77  fof(c_0_29, plain, ![X35, X36, X37]:(~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|v1_relat_1(X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 10.60/10.77  fof(c_0_30, negated_conjecture, (~v1_xboole_0(esk3_0)&(~v1_xboole_0(esk4_0)&((~v1_xboole_0(esk5_0)&m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0)))&((~v1_xboole_0(esk6_0)&m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0)))&(r1_subset_1(esk5_0,esk6_0)&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk5_0,esk4_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0))))&(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk6_0,esk4_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk4_0))))&(k2_partfun1(esk5_0,esk4_0,esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0))!=k2_partfun1(esk6_0,esk4_0,esk8_0,k9_subset_1(esk3_0,esk5_0,esk6_0))|k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk5_0)!=esk7_0|k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk6_0)!=esk8_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).
% 10.60/10.77  cnf(c_0_31, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X3)=X6|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X4)|v1_xboole_0(X1)|X5!=k1_tmap_1(X1,X4,X2,X3,X7,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|k2_partfun1(X2,X4,X7,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_1(X6)|~v1_funct_2(X6,X3,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X7)|~v1_funct_2(X7,X2,X4)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 10.60/10.77  cnf(c_0_32, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|m1_subset_1(k1_tmap_1(X4,X1,X2,X3,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X4,X2,X3),X1)))|~v1_funct_2(X6,X3,X1)|~v1_funct_2(X5,X2,X1)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~m1_subset_1(X3,k1_zfmisc_1(X4))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(csr,[status(thm)],[c_0_23, c_0_24])).
% 10.60/10.77  cnf(c_0_33, plain, (v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~v1_funct_2(X6,X4,X2)|~v1_funct_2(X5,X3,X2)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[c_0_25, c_0_24])).
% 10.60/10.77  cnf(c_0_34, plain, (v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~v1_funct_2(X6,X4,X2)|~v1_funct_2(X5,X3,X2)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[c_0_26, c_0_24])).
% 10.60/10.77  cnf(c_0_35, plain, (v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 10.60/10.77  cnf(c_0_36, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 10.60/10.77  cnf(c_0_37, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 10.60/10.77  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 10.60/10.77  fof(c_0_39, plain, ![X10, X11, X13, X14, X15]:((r1_xboole_0(X10,X11)|r2_hidden(esk1_2(X10,X11),k3_xboole_0(X10,X11)))&(~r2_hidden(X15,k3_xboole_0(X13,X14))|~r1_xboole_0(X13,X14))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 10.60/10.77  fof(c_0_40, plain, ![X16]:k3_xboole_0(X16,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 10.60/10.77  fof(c_0_41, plain, ![X17]:r1_xboole_0(X17,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 10.60/10.77  fof(c_0_42, plain, ![X41, X42, X43]:((v1_funct_1(X43)|(~v1_funct_1(X43)|~v1_funct_2(X43,X41,X42))|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|v1_xboole_0(X42))&(v1_partfun1(X43,X41)|(~v1_funct_1(X43)|~v1_funct_2(X43,X41,X42))|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|v1_xboole_0(X42))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 10.60/10.77  fof(c_0_43, plain, ![X38, X39, X40]:((v4_relat_1(X40,X38)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))&(v5_relat_1(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 10.60/10.77  cnf(c_0_44, negated_conjecture, (k2_partfun1(esk5_0,esk4_0,esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0))!=k2_partfun1(esk6_0,esk4_0,esk8_0,k9_subset_1(esk3_0,esk5_0,esk6_0))|k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk5_0)!=esk7_0|k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk6_0)!=esk8_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 10.60/10.77  cnf(c_0_45, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X3)=X6|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_2(X5,X2,X4)|~v1_funct_2(X6,X3,X4)|~v1_funct_1(X5)|~v1_funct_1(X6)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_31, c_0_24])]), c_0_32]), c_0_33]), c_0_34])).
% 10.60/10.77  cnf(c_0_46, negated_conjecture, (v1_funct_2(esk7_0,esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 10.60/10.77  cnf(c_0_47, negated_conjecture, (v1_funct_2(esk8_0,esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 10.60/10.77  cnf(c_0_48, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 10.60/10.77  cnf(c_0_49, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 10.60/10.77  cnf(c_0_50, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 10.60/10.77  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 10.60/10.77  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 10.60/10.77  cnf(c_0_53, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 10.60/10.77  cnf(c_0_54, negated_conjecture, (~v1_xboole_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 10.60/10.77  cnf(c_0_55, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 10.60/10.77  cnf(c_0_56, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X2)=X6|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X4)|v1_xboole_0(X1)|X5!=k1_tmap_1(X1,X4,X2,X3,X6,X7)|~v1_funct_1(X5)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|k2_partfun1(X2,X4,X6,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X7,k9_subset_1(X1,X2,X3))|~v1_funct_1(X7)|~v1_funct_2(X7,X3,X4)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X6)|~v1_funct_2(X6,X2,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 10.60/10.77  fof(c_0_57, plain, ![X46, X47, X48, X49]:(~v1_funct_1(X48)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))|k2_partfun1(X46,X47,X48,X49)=k7_relat_1(X48,X49)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 10.60/10.77  fof(c_0_58, plain, ![X31, X32, X33]:((r2_hidden(esk2_3(X31,X32,X33),k1_relat_1(X32))|k1_relat_1(X32)!=k3_xboole_0(k1_relat_1(X33),X31)|X32=k7_relat_1(X33,X31)|(~v1_relat_1(X33)|~v1_funct_1(X33))|(~v1_relat_1(X32)|~v1_funct_1(X32)))&(k1_funct_1(X32,esk2_3(X31,X32,X33))!=k1_funct_1(X33,esk2_3(X31,X32,X33))|k1_relat_1(X32)!=k3_xboole_0(k1_relat_1(X33),X31)|X32=k7_relat_1(X33,X31)|(~v1_relat_1(X33)|~v1_funct_1(X33))|(~v1_relat_1(X32)|~v1_funct_1(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t68_funct_1])])])])])).
% 10.60/10.77  cnf(c_0_59, plain, (v1_funct_1(k1_xboole_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 10.60/10.77  cnf(c_0_60, negated_conjecture, (v1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 10.60/10.77  cnf(c_0_61, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 10.60/10.77  cnf(c_0_62, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 10.60/10.77  cnf(c_0_63, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 10.60/10.77  fof(c_0_64, plain, ![X44, X45]:((~v1_partfun1(X45,X44)|k1_relat_1(X45)=X44|(~v1_relat_1(X45)|~v4_relat_1(X45,X44)))&(k1_relat_1(X45)!=X44|v1_partfun1(X45,X44)|(~v1_relat_1(X45)|~v4_relat_1(X45,X44)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 10.60/10.77  cnf(c_0_65, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 10.60/10.77  cnf(c_0_66, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 10.60/10.77  cnf(c_0_67, negated_conjecture, (k2_partfun1(esk6_0,esk4_0,esk8_0,k9_subset_1(esk3_0,esk5_0,esk6_0))!=k2_partfun1(esk5_0,esk4_0,esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0))|k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk5_0)!=esk7_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_47]), c_0_48]), c_0_49]), c_0_50]), c_0_38]), c_0_51]), c_0_52])]), c_0_53]), c_0_54]), c_0_55])).
% 10.60/10.77  cnf(c_0_68, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X2)=X5|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_2(X6,X3,X4)|~v1_funct_2(X5,X2,X4)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_56, c_0_24])]), c_0_32]), c_0_33]), c_0_34])).
% 10.60/10.77  cnf(c_0_69, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 10.60/10.77  cnf(c_0_70, plain, (r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X2))|X2=k7_relat_1(X3,X1)|k1_relat_1(X2)!=k3_xboole_0(k1_relat_1(X3),X1)|~v1_relat_1(X3)|~v1_funct_1(X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 10.60/10.77  cnf(c_0_71, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 10.60/10.77  cnf(c_0_72, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_49])])).
% 10.60/10.77  cnf(c_0_73, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_37, c_0_36])).
% 10.60/10.77  cnf(c_0_74, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])])).
% 10.60/10.77  cnf(c_0_75, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 10.60/10.77  cnf(c_0_76, negated_conjecture, (v1_partfun1(esk8_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_38]), c_0_47]), c_0_49])]), c_0_53])).
% 10.60/10.77  cnf(c_0_77, negated_conjecture, (v4_relat_1(esk8_0,esk6_0)), inference(spm,[status(thm)],[c_0_66, c_0_38])).
% 10.60/10.77  cnf(c_0_78, negated_conjecture, (v1_partfun1(esk7_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_50]), c_0_46]), c_0_48])]), c_0_53])).
% 10.60/10.77  cnf(c_0_79, negated_conjecture, (v4_relat_1(esk7_0,esk5_0)), inference(spm,[status(thm)],[c_0_66, c_0_50])).
% 10.60/10.77  cnf(c_0_80, negated_conjecture, (v1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_37, c_0_50])).
% 10.60/10.77  cnf(c_0_81, negated_conjecture, (k2_partfun1(esk6_0,esk4_0,esk8_0,k9_subset_1(esk3_0,esk5_0,esk6_0))!=k2_partfun1(esk5_0,esk4_0,esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_47]), c_0_46]), c_0_49]), c_0_48]), c_0_38]), c_0_50]), c_0_51]), c_0_52])]), c_0_53]), c_0_54]), c_0_55])).
% 10.60/10.77  cnf(c_0_82, plain, (k2_partfun1(X1,X2,X3,X4)=k2_partfun1(X5,X6,X3,X4)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(spm,[status(thm)],[c_0_69, c_0_69])).
% 10.60/10.77  cnf(c_0_83, plain, (k7_relat_1(X1,X2)=k1_xboole_0|k3_xboole_0(k1_relat_1(X1),X2)!=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72]), c_0_73])]), c_0_74])).
% 10.60/10.77  cnf(c_0_84, negated_conjecture, (k1_relat_1(esk8_0)=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77]), c_0_60])])).
% 10.60/10.77  cnf(c_0_85, negated_conjecture, (k1_relat_1(esk7_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_78]), c_0_79]), c_0_80])])).
% 10.60/10.77  cnf(c_0_86, negated_conjecture, (k2_partfun1(X1,X2,esk8_0,k9_subset_1(esk3_0,esk5_0,esk6_0))!=k2_partfun1(esk5_0,esk4_0,esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0))|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_49]), c_0_38])])).
% 10.60/10.77  fof(c_0_87, plain, ![X29, X30]:((~r1_subset_1(X29,X30)|r1_xboole_0(X29,X30)|(v1_xboole_0(X29)|v1_xboole_0(X30)))&(~r1_xboole_0(X29,X30)|r1_subset_1(X29,X30)|(v1_xboole_0(X29)|v1_xboole_0(X30)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).
% 10.60/10.77  cnf(c_0_88, negated_conjecture, (k7_relat_1(esk8_0,X1)=k1_xboole_0|k3_xboole_0(esk6_0,X1)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_49]), c_0_60])])).
% 10.60/10.77  cnf(c_0_89, negated_conjecture, (k7_relat_1(esk7_0,X1)=k1_xboole_0|k3_xboole_0(esk5_0,X1)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_85]), c_0_48]), c_0_80])])).
% 10.60/10.77  cnf(c_0_90, negated_conjecture, (k2_partfun1(X1,X2,esk8_0,k9_subset_1(esk3_0,esk5_0,esk6_0))!=k2_partfun1(X3,X4,esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0))|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_82]), c_0_48]), c_0_50])])).
% 10.60/10.77  fof(c_0_91, plain, ![X8, X9]:((~r1_xboole_0(X8,X9)|k3_xboole_0(X8,X9)=k1_xboole_0)&(k3_xboole_0(X8,X9)!=k1_xboole_0|r1_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 10.60/10.77  cnf(c_0_92, plain, (r1_xboole_0(X1,X2)|v1_xboole_0(X1)|v1_xboole_0(X2)|~r1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 10.60/10.77  cnf(c_0_93, negated_conjecture, (r1_subset_1(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 10.60/10.77  cnf(c_0_94, negated_conjecture, (k2_partfun1(X1,X2,esk8_0,X3)=k1_xboole_0|k3_xboole_0(esk6_0,X3)!=k1_xboole_0|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_88]), c_0_49])])).
% 10.60/10.77  cnf(c_0_95, negated_conjecture, (k2_partfun1(X1,X2,esk7_0,X3)=k1_xboole_0|k3_xboole_0(esk5_0,X3)!=k1_xboole_0|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_89]), c_0_48])])).
% 10.60/10.77  cnf(c_0_96, negated_conjecture, (k2_partfun1(X1,X2,esk8_0,k9_subset_1(esk3_0,esk5_0,esk6_0))!=k7_relat_1(esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0))|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_69]), c_0_48])])).
% 10.60/10.77  fof(c_0_97, plain, ![X18, X19, X20]:(~m1_subset_1(X20,k1_zfmisc_1(X18))|k9_subset_1(X18,X19,X20)=k3_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 10.60/10.77  cnf(c_0_98, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_91])).
% 10.60/10.77  cnf(c_0_99, negated_conjecture, (r1_xboole_0(esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_55]), c_0_54])).
% 10.60/10.77  cnf(c_0_100, negated_conjecture, (k2_partfun1(X1,X2,esk8_0,k1_xboole_0)=k1_xboole_0|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_94, c_0_62])).
% 10.60/10.77  cnf(c_0_101, negated_conjecture, (k2_partfun1(X1,X2,esk7_0,k1_xboole_0)=k1_xboole_0|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_95, c_0_62])).
% 10.60/10.77  cnf(c_0_102, negated_conjecture, (k2_partfun1(X1,X2,esk8_0,k9_subset_1(esk3_0,esk5_0,esk6_0))!=k7_relat_1(esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0))|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_96, c_0_50])).
% 10.60/10.77  cnf(c_0_103, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_97])).
% 10.60/10.77  cnf(c_0_104, negated_conjecture, (k3_xboole_0(esk5_0,esk6_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 10.60/10.77  cnf(c_0_105, negated_conjecture, (k7_relat_1(esk8_0,k1_xboole_0)=k1_xboole_0|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_100]), c_0_49])])).
% 10.60/10.77  cnf(c_0_106, negated_conjecture, (k7_relat_1(esk7_0,k1_xboole_0)=k1_xboole_0|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_101]), c_0_48])])).
% 10.60/10.77  cnf(c_0_107, negated_conjecture, (k7_relat_1(esk8_0,k9_subset_1(esk3_0,esk5_0,esk6_0))!=k7_relat_1(esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0))|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_69]), c_0_49])])).
% 10.60/10.77  cnf(c_0_108, negated_conjecture, (k9_subset_1(X1,esk5_0,esk6_0)=k1_xboole_0|~m1_subset_1(esk6_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 10.60/10.77  cnf(c_0_109, negated_conjecture, (k7_relat_1(esk8_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_105, c_0_38])).
% 10.60/10.77  cnf(c_0_110, negated_conjecture, (k7_relat_1(esk7_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_106, c_0_50])).
% 10.60/10.77  cnf(c_0_111, negated_conjecture, (~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_109]), c_0_110]), c_0_51])])).
% 10.60/10.77  cnf(c_0_112, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_38, c_0_111]), ['proof']).
% 10.60/10.77  # SZS output end CNFRefutation
% 10.60/10.77  # Proof object total steps             : 113
% 10.60/10.77  # Proof object clause steps            : 75
% 10.60/10.77  # Proof object formula steps           : 38
% 10.60/10.77  # Proof object conjectures             : 47
% 10.60/10.77  # Proof object clause conjectures      : 44
% 10.60/10.77  # Proof object formula conjectures     : 3
% 10.60/10.77  # Proof object initial clauses used    : 34
% 10.60/10.77  # Proof object initial formulas used   : 19
% 10.60/10.77  # Proof object generating inferences   : 35
% 10.60/10.77  # Proof object simplifying inferences  : 90
% 10.60/10.77  # Training examples: 0 positive, 0 negative
% 10.60/10.77  # Parsed axioms                        : 20
% 10.60/10.77  # Removed by relevancy pruning/SinE    : 0
% 10.60/10.77  # Initial clauses                      : 45
% 10.60/10.77  # Removed in clause preprocessing      : 1
% 10.60/10.77  # Initial clauses in saturation        : 44
% 10.60/10.77  # Processed clauses                    : 42434
% 10.60/10.77  # ...of these trivial                  : 44
% 10.60/10.77  # ...subsumed                          : 31900
% 10.60/10.77  # ...remaining for further processing  : 10490
% 10.60/10.77  # Other redundant clauses eliminated   : 6800
% 10.60/10.77  # Clauses deleted for lack of memory   : 0
% 10.60/10.77  # Backward-subsumed                    : 1908
% 10.60/10.77  # Backward-rewritten                   : 10
% 10.60/10.77  # Generated clauses                    : 95818
% 10.60/10.77  # ...of the previous two non-trivial   : 87261
% 10.60/10.77  # Contextual simplify-reflections      : 1661
% 10.60/10.77  # Paramodulations                      : 88888
% 10.60/10.77  # Factorizations                       : 0
% 10.60/10.77  # Equation resolutions                 : 6930
% 10.60/10.77  # Propositional unsat checks           : 0
% 10.60/10.77  #    Propositional check models        : 0
% 10.60/10.77  #    Propositional check unsatisfiable : 0
% 10.60/10.77  #    Propositional clauses             : 0
% 10.60/10.77  #    Propositional clauses after purity: 0
% 10.60/10.77  #    Propositional unsat core size     : 0
% 10.60/10.77  #    Propositional preprocessing time  : 0.000
% 10.60/10.77  #    Propositional encoding time       : 0.000
% 10.60/10.77  #    Propositional solver time         : 0.000
% 10.60/10.77  #    Success case prop preproc time    : 0.000
% 10.60/10.77  #    Success case prop encoding time   : 0.000
% 10.60/10.77  #    Success case prop solver time     : 0.000
% 10.60/10.77  # Current number of processed clauses  : 8567
% 10.60/10.77  #    Positive orientable unit clauses  : 36
% 10.60/10.77  #    Positive unorientable unit clauses: 0
% 10.60/10.77  #    Negative unit clauses             : 7
% 10.60/10.77  #    Non-unit-clauses                  : 8524
% 10.60/10.77  # Current number of unprocessed clauses: 43005
% 10.60/10.77  # ...number of literals in the above   : 931662
% 10.60/10.77  # Current number of archived formulas  : 0
% 10.60/10.77  # Current number of archived clauses   : 1919
% 10.60/10.77  # Clause-clause subsumption calls (NU) : 18216700
% 10.60/10.77  # Rec. Clause-clause subsumption calls : 121458
% 10.60/10.77  # Non-unit clause-clause subsumptions  : 35422
% 10.60/10.77  # Unit Clause-clause subsumption calls : 3330
% 10.60/10.77  # Rewrite failures with RHS unbound    : 0
% 10.60/10.77  # BW rewrite match attempts            : 22
% 10.60/10.77  # BW rewrite match successes           : 4
% 10.60/10.77  # Condensation attempts                : 0
% 10.60/10.77  # Condensation successes               : 0
% 10.60/10.77  # Termbank termtop insertions          : 7452350
% 10.60/10.78  
% 10.60/10.78  # -------------------------------------------------
% 10.60/10.78  # User time                : 10.348 s
% 10.60/10.78  # System time              : 0.082 s
% 10.60/10.78  # Total time               : 10.431 s
% 10.60/10.78  # Maximum resident set size: 1612 pages
%------------------------------------------------------------------------------
