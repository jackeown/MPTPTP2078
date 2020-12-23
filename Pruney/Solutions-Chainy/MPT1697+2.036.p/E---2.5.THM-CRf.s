%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:40 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 493 expanded)
%              Number of clauses        :   59 ( 194 expanded)
%              Number of leaves         :   14 ( 123 expanded)
%              Depth                    :   11
%              Number of atoms          :  485 (3938 expanded)
%              Number of equality atoms :   67 ( 617 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal clause size      :   55 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

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

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

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

fof(c_0_14,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v1_xboole_0(X8)
        | ~ r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_1(X10),X10)
        | v1_xboole_0(X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_15,plain,(
    ! [X14,X15,X17,X18,X19] :
      ( ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_xboole_0(X14,X15) )
      & ( r2_hidden(esk2_2(X14,X15),X15)
        | r1_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X19,X17)
        | ~ r2_hidden(X19,X18)
        | ~ r1_xboole_0(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_16,plain,(
    ! [X12,X13] :
      ( ~ r1_xboole_0(X12,X13)
      | r1_xboole_0(X13,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_17,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

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
    ! [X51,X52,X53,X54,X55,X56] :
      ( ( v1_funct_1(k1_tmap_1(X51,X52,X53,X54,X55,X56))
        | v1_xboole_0(X51)
        | v1_xboole_0(X52)
        | v1_xboole_0(X53)
        | ~ m1_subset_1(X53,k1_zfmisc_1(X51))
        | v1_xboole_0(X54)
        | ~ m1_subset_1(X54,k1_zfmisc_1(X51))
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,X53,X52)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X52)))
        | ~ v1_funct_1(X56)
        | ~ v1_funct_2(X56,X54,X52)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X52))) )
      & ( v1_funct_2(k1_tmap_1(X51,X52,X53,X54,X55,X56),k4_subset_1(X51,X53,X54),X52)
        | v1_xboole_0(X51)
        | v1_xboole_0(X52)
        | v1_xboole_0(X53)
        | ~ m1_subset_1(X53,k1_zfmisc_1(X51))
        | v1_xboole_0(X54)
        | ~ m1_subset_1(X54,k1_zfmisc_1(X51))
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,X53,X52)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X52)))
        | ~ v1_funct_1(X56)
        | ~ v1_funct_2(X56,X54,X52)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X52))) )
      & ( m1_subset_1(k1_tmap_1(X51,X52,X53,X54,X55,X56),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X51,X53,X54),X52)))
        | v1_xboole_0(X51)
        | v1_xboole_0(X52)
        | v1_xboole_0(X53)
        | ~ m1_subset_1(X53,k1_zfmisc_1(X51))
        | v1_xboole_0(X54)
        | ~ m1_subset_1(X54,k1_zfmisc_1(X51))
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,X53,X52)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X52)))
        | ~ v1_funct_1(X56)
        | ~ v1_funct_2(X56,X54,X52)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X52))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tmap_1])])])])).

fof(c_0_21,plain,(
    ! [X31,X32] :
      ( ~ v1_xboole_0(X31)
      | ~ m1_subset_1(X32,k1_zfmisc_1(X31))
      | v1_xboole_0(X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

fof(c_0_22,plain,(
    ! [X33,X34] :
      ( ~ v1_relat_1(X33)
      | ~ r1_xboole_0(X34,k1_relat_1(X33))
      | k7_relat_1(X33,X34) = k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t187_relat_1])])])).

cnf(c_0_23,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( r1_xboole_0(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_25,plain,(
    ! [X40,X41,X42,X43] :
      ( ~ v1_funct_1(X42)
      | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
      | k2_partfun1(X40,X41,X42,X43) = k7_relat_1(X42,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

fof(c_0_26,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0)
    & ~ v1_xboole_0(esk5_0)
    & ~ v1_xboole_0(esk6_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(esk4_0))
    & ~ v1_xboole_0(esk7_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(esk4_0))
    & r1_subset_1(esk6_0,esk7_0)
    & v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,esk6_0,esk5_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0)))
    & v1_funct_1(esk9_0)
    & v1_funct_2(esk9_0,esk7_0,esk5_0)
    & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk5_0)))
    & ( k2_partfun1(esk6_0,esk5_0,esk8_0,k9_subset_1(esk4_0,esk6_0,esk7_0)) != k2_partfun1(esk7_0,esk5_0,esk9_0,k9_subset_1(esk4_0,esk6_0,esk7_0))
      | k2_partfun1(k4_subset_1(esk4_0,esk6_0,esk7_0),esk5_0,k1_tmap_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk6_0) != esk8_0
      | k2_partfun1(k4_subset_1(esk4_0,esk6_0,esk7_0),esk5_0,k1_tmap_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk7_0) != esk9_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).

fof(c_0_27,plain,(
    ! [X37,X38,X39] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
      | v1_relat_1(X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_28,plain,(
    ! [X20,X21,X23,X24,X25] :
      ( ( r1_xboole_0(X20,X21)
        | r2_hidden(esk3_2(X20,X21),k3_xboole_0(X20,X21)) )
      & ( ~ r2_hidden(X25,k3_xboole_0(X23,X24))
        | ~ r1_xboole_0(X23,X24) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_29,plain,(
    ! [X26,X27] : k4_xboole_0(X26,k4_xboole_0(X26,X27)) = k3_xboole_0(X26,X27) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_30,plain,(
    ! [X44,X45,X46,X47,X48,X49,X50] :
      ( ( k2_partfun1(k4_subset_1(X44,X46,X47),X45,X50,X46) = X48
        | X50 != k1_tmap_1(X44,X45,X46,X47,X48,X49)
        | ~ v1_funct_1(X50)
        | ~ v1_funct_2(X50,k4_subset_1(X44,X46,X47),X45)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X44,X46,X47),X45)))
        | k2_partfun1(X46,X45,X48,k9_subset_1(X44,X46,X47)) != k2_partfun1(X47,X45,X49,k9_subset_1(X44,X46,X47))
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,X47,X45)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X45)))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,X46,X45)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X45)))
        | v1_xboole_0(X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(X44))
        | v1_xboole_0(X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(X44))
        | v1_xboole_0(X45)
        | v1_xboole_0(X44) )
      & ( k2_partfun1(k4_subset_1(X44,X46,X47),X45,X50,X47) = X49
        | X50 != k1_tmap_1(X44,X45,X46,X47,X48,X49)
        | ~ v1_funct_1(X50)
        | ~ v1_funct_2(X50,k4_subset_1(X44,X46,X47),X45)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X44,X46,X47),X45)))
        | k2_partfun1(X46,X45,X48,k9_subset_1(X44,X46,X47)) != k2_partfun1(X47,X45,X49,k9_subset_1(X44,X46,X47))
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,X47,X45)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X45)))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,X46,X45)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X45)))
        | v1_xboole_0(X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(X44))
        | v1_xboole_0(X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(X44))
        | v1_xboole_0(X45)
        | v1_xboole_0(X44) )
      & ( k2_partfun1(k4_subset_1(X44,X46,X47),X45,X50,X46) != X48
        | k2_partfun1(k4_subset_1(X44,X46,X47),X45,X50,X47) != X49
        | X50 = k1_tmap_1(X44,X45,X46,X47,X48,X49)
        | ~ v1_funct_1(X50)
        | ~ v1_funct_2(X50,k4_subset_1(X44,X46,X47),X45)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X44,X46,X47),X45)))
        | k2_partfun1(X46,X45,X48,k9_subset_1(X44,X46,X47)) != k2_partfun1(X47,X45,X49,k9_subset_1(X44,X46,X47))
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,X47,X45)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X45)))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,X46,X45)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X45)))
        | v1_xboole_0(X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(X44))
        | v1_xboole_0(X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(X44))
        | v1_xboole_0(X45)
        | v1_xboole_0(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tmap_1])])])])])).

cnf(c_0_31,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_34,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_35,plain,
    ( k7_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,plain,
    ( r1_xboole_0(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_37,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_40,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_43,plain,(
    ! [X28,X29,X30] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(X28))
      | k9_subset_1(X28,X29,X30) = k3_xboole_0(X29,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_46,plain,(
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

cnf(c_0_47,plain,
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

cnf(c_0_48,plain,
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
    inference(csr,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_49,plain,
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
    inference(csr,[status(thm)],[c_0_33,c_0_32])).

cnf(c_0_50,plain,
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
    inference(csr,[status(thm)],[c_0_34,c_0_32])).

cnf(c_0_51,plain,
    ( k7_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_52,negated_conjecture,
    ( k7_relat_1(esk9_0,X1) = k2_partfun1(esk7_0,esk5_0,esk9_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

cnf(c_0_53,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_38])).

cnf(c_0_54,negated_conjecture,
    ( k7_relat_1(esk8_0,X1) = k2_partfun1(esk6_0,esk5_0,esk8_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_41]),c_0_42])])).

cnf(c_0_55,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_56,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_57,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_58,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_59,plain,
    ( r1_xboole_0(X1,X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_60,negated_conjecture,
    ( r1_subset_1(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_61,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_62,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_63,plain,
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
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_47,c_0_32])]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_64,negated_conjecture,
    ( k2_partfun1(esk7_0,esk5_0,esk9_0,X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])])).

cnf(c_0_65,negated_conjecture,
    ( v1_funct_2(esk9_0,esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_66,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_67,plain,
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

cnf(c_0_68,negated_conjecture,
    ( k2_partfun1(esk6_0,esk5_0,esk8_0,k9_subset_1(esk4_0,esk6_0,esk7_0)) != k2_partfun1(esk7_0,esk5_0,esk9_0,k9_subset_1(esk4_0,esk6_0,esk7_0))
    | k2_partfun1(k4_subset_1(esk4_0,esk6_0,esk7_0),esk5_0,k1_tmap_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk6_0) != esk8_0
    | k2_partfun1(k4_subset_1(esk4_0,esk6_0,esk7_0),esk5_0,k1_tmap_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk7_0) != esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_69,negated_conjecture,
    ( k2_partfun1(esk6_0,esk5_0,esk8_0,X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_54]),c_0_55])])).

cnf(c_0_70,plain,
    ( k9_subset_1(X2,X3,X1) = k4_xboole_0(X3,k4_xboole_0(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_56,c_0_45])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_72,plain,
    ( v1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_73,negated_conjecture,
    ( r1_xboole_0(esk6_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_62])).

cnf(c_0_74,negated_conjecture,
    ( k2_partfun1(k4_subset_1(X1,X2,esk7_0),esk5_0,k1_tmap_1(X1,esk5_0,X2,esk7_0,X3,esk9_0),esk7_0) = esk9_0
    | v1_xboole_0(X2)
    | k2_partfun1(X2,esk5_0,X3,k9_subset_1(X1,X2,esk7_0)) != k1_xboole_0
    | ~ v1_funct_2(X3,X2,esk5_0)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,esk5_0)))
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(k9_subset_1(X1,X2,esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),c_0_39]),c_0_38])]),c_0_61]),c_0_66])).

cnf(c_0_75,negated_conjecture,
    ( v1_funct_2(esk8_0,esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_76,plain,
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
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_67,c_0_32])]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_77,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk4_0,esk6_0,esk7_0),esk5_0,k1_tmap_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk6_0) != esk8_0
    | k2_partfun1(k4_subset_1(esk4_0,esk6_0,esk7_0),esk5_0,k1_tmap_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk7_0) != esk9_0
    | ~ v1_xboole_0(k9_subset_1(esk4_0,esk6_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_64])).

cnf(c_0_78,negated_conjecture,
    ( k9_subset_1(esk4_0,X1,esk7_0) = k4_xboole_0(X1,k4_xboole_0(X1,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_79,negated_conjecture,
    ( v1_xboole_0(k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_80,negated_conjecture,
    ( k2_partfun1(k4_subset_1(X1,esk6_0,esk7_0),esk5_0,k1_tmap_1(X1,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk7_0) = esk9_0
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(k9_subset_1(X1,esk6_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_69]),c_0_75]),c_0_42]),c_0_41])]),c_0_62])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_82,negated_conjecture,
    ( k2_partfun1(k4_subset_1(X1,X2,esk7_0),esk5_0,k1_tmap_1(X1,esk5_0,X2,esk7_0,X3,esk9_0),X2) = X3
    | v1_xboole_0(X2)
    | k2_partfun1(X2,esk5_0,X3,k9_subset_1(X1,X2,esk7_0)) != k1_xboole_0
    | ~ v1_funct_2(X3,X2,esk5_0)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,esk5_0)))
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(k9_subset_1(X1,X2,esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_64]),c_0_65]),c_0_39]),c_0_38])]),c_0_61]),c_0_66])).

cnf(c_0_83,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk4_0,esk6_0,esk7_0),esk5_0,k1_tmap_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk6_0) != esk8_0
    | k2_partfun1(k4_subset_1(esk4_0,esk6_0,esk7_0),esk5_0,k1_tmap_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk7_0) != esk9_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_78]),c_0_79])])).

cnf(c_0_84,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk4_0,esk6_0,esk7_0),esk5_0,k1_tmap_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk7_0) = esk9_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_71]),c_0_81]),c_0_78]),c_0_79])])).

cnf(c_0_85,negated_conjecture,
    ( k2_partfun1(k4_subset_1(X1,esk6_0,esk7_0),esk5_0,k1_tmap_1(X1,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk6_0) = esk8_0
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(k9_subset_1(X1,esk6_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_69]),c_0_75]),c_0_42]),c_0_41])]),c_0_62])).

cnf(c_0_86,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk4_0,esk6_0,esk7_0),esk5_0,k1_tmap_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk6_0) != esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_84])])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_71]),c_0_81]),c_0_78]),c_0_79])]),c_0_86]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:43:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.44  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.19/0.44  # and selection function SelectCQIPrecWNTNp.
% 0.19/0.44  #
% 0.19/0.44  # Preprocessing time       : 0.029 s
% 0.19/0.44  # Presaturation interreduction done
% 0.19/0.44  
% 0.19/0.44  # Proof found!
% 0.19/0.44  # SZS status Theorem
% 0.19/0.44  # SZS output start CNFRefutation
% 0.19/0.44  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.44  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.19/0.44  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.19/0.44  fof(t6_tmap_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>(r1_subset_1(X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3)=X5)&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4)=X6)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 0.19/0.44  fof(dt_k1_tmap_1, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((((((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))&~(v1_xboole_0(X3)))&m1_subset_1(X3,k1_zfmisc_1(X1)))&~(v1_xboole_0(X4)))&m1_subset_1(X4,k1_zfmisc_1(X1)))&v1_funct_1(X5))&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2))&m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 0.19/0.44  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.19/0.44  fof(t187_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_xboole_0(X2,k1_relat_1(X1))=>k7_relat_1(X1,X2)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 0.19/0.44  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 0.19/0.44  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.44  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.19/0.44  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.44  fof(d1_tmap_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>(k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))=>![X7]:(((v1_funct_1(X7)&v1_funct_2(X7,k4_subset_1(X1,X3,X4),X2))&m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))))=>(X7=k1_tmap_1(X1,X2,X3,X4,X5,X6)<=>(k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X3)=X5&k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X4)=X6)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 0.19/0.44  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.19/0.44  fof(redefinition_r1_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))=>(r1_subset_1(X1,X2)<=>r1_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 0.19/0.44  fof(c_0_14, plain, ![X8, X9, X10]:((~v1_xboole_0(X8)|~r2_hidden(X9,X8))&(r2_hidden(esk1_1(X10),X10)|v1_xboole_0(X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.44  fof(c_0_15, plain, ![X14, X15, X17, X18, X19]:(((r2_hidden(esk2_2(X14,X15),X14)|r1_xboole_0(X14,X15))&(r2_hidden(esk2_2(X14,X15),X15)|r1_xboole_0(X14,X15)))&(~r2_hidden(X19,X17)|~r2_hidden(X19,X18)|~r1_xboole_0(X17,X18))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.19/0.44  fof(c_0_16, plain, ![X12, X13]:(~r1_xboole_0(X12,X13)|r1_xboole_0(X13,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.19/0.44  cnf(c_0_17, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.44  cnf(c_0_18, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.44  fof(c_0_19, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>(r1_subset_1(X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3)=X5)&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4)=X6))))))))), inference(assume_negation,[status(cth)],[t6_tmap_1])).
% 0.19/0.44  fof(c_0_20, plain, ![X51, X52, X53, X54, X55, X56]:(((v1_funct_1(k1_tmap_1(X51,X52,X53,X54,X55,X56))|(v1_xboole_0(X51)|v1_xboole_0(X52)|v1_xboole_0(X53)|~m1_subset_1(X53,k1_zfmisc_1(X51))|v1_xboole_0(X54)|~m1_subset_1(X54,k1_zfmisc_1(X51))|~v1_funct_1(X55)|~v1_funct_2(X55,X53,X52)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X52)))|~v1_funct_1(X56)|~v1_funct_2(X56,X54,X52)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X52)))))&(v1_funct_2(k1_tmap_1(X51,X52,X53,X54,X55,X56),k4_subset_1(X51,X53,X54),X52)|(v1_xboole_0(X51)|v1_xboole_0(X52)|v1_xboole_0(X53)|~m1_subset_1(X53,k1_zfmisc_1(X51))|v1_xboole_0(X54)|~m1_subset_1(X54,k1_zfmisc_1(X51))|~v1_funct_1(X55)|~v1_funct_2(X55,X53,X52)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X52)))|~v1_funct_1(X56)|~v1_funct_2(X56,X54,X52)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X52))))))&(m1_subset_1(k1_tmap_1(X51,X52,X53,X54,X55,X56),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X51,X53,X54),X52)))|(v1_xboole_0(X51)|v1_xboole_0(X52)|v1_xboole_0(X53)|~m1_subset_1(X53,k1_zfmisc_1(X51))|v1_xboole_0(X54)|~m1_subset_1(X54,k1_zfmisc_1(X51))|~v1_funct_1(X55)|~v1_funct_2(X55,X53,X52)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X52)))|~v1_funct_1(X56)|~v1_funct_2(X56,X54,X52)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X52)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tmap_1])])])])).
% 0.19/0.44  fof(c_0_21, plain, ![X31, X32]:(~v1_xboole_0(X31)|(~m1_subset_1(X32,k1_zfmisc_1(X31))|v1_xboole_0(X32))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.19/0.44  fof(c_0_22, plain, ![X33, X34]:(~v1_relat_1(X33)|(~r1_xboole_0(X34,k1_relat_1(X33))|k7_relat_1(X33,X34)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t187_relat_1])])])).
% 0.19/0.44  cnf(c_0_23, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.44  cnf(c_0_24, plain, (r1_xboole_0(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.44  fof(c_0_25, plain, ![X40, X41, X42, X43]:(~v1_funct_1(X42)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|k2_partfun1(X40,X41,X42,X43)=k7_relat_1(X42,X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 0.19/0.44  fof(c_0_26, negated_conjecture, (~v1_xboole_0(esk4_0)&(~v1_xboole_0(esk5_0)&((~v1_xboole_0(esk6_0)&m1_subset_1(esk6_0,k1_zfmisc_1(esk4_0)))&((~v1_xboole_0(esk7_0)&m1_subset_1(esk7_0,k1_zfmisc_1(esk4_0)))&(r1_subset_1(esk6_0,esk7_0)&(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk6_0,esk5_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0))))&(((v1_funct_1(esk9_0)&v1_funct_2(esk9_0,esk7_0,esk5_0))&m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk5_0))))&(k2_partfun1(esk6_0,esk5_0,esk8_0,k9_subset_1(esk4_0,esk6_0,esk7_0))!=k2_partfun1(esk7_0,esk5_0,esk9_0,k9_subset_1(esk4_0,esk6_0,esk7_0))|k2_partfun1(k4_subset_1(esk4_0,esk6_0,esk7_0),esk5_0,k1_tmap_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk6_0)!=esk8_0|k2_partfun1(k4_subset_1(esk4_0,esk6_0,esk7_0),esk5_0,k1_tmap_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk7_0)!=esk9_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).
% 0.19/0.44  fof(c_0_27, plain, ![X37, X38, X39]:(~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))|v1_relat_1(X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.44  fof(c_0_28, plain, ![X20, X21, X23, X24, X25]:((r1_xboole_0(X20,X21)|r2_hidden(esk3_2(X20,X21),k3_xboole_0(X20,X21)))&(~r2_hidden(X25,k3_xboole_0(X23,X24))|~r1_xboole_0(X23,X24))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.19/0.44  fof(c_0_29, plain, ![X26, X27]:k4_xboole_0(X26,k4_xboole_0(X26,X27))=k3_xboole_0(X26,X27), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.44  fof(c_0_30, plain, ![X44, X45, X46, X47, X48, X49, X50]:(((k2_partfun1(k4_subset_1(X44,X46,X47),X45,X50,X46)=X48|X50!=k1_tmap_1(X44,X45,X46,X47,X48,X49)|(~v1_funct_1(X50)|~v1_funct_2(X50,k4_subset_1(X44,X46,X47),X45)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X44,X46,X47),X45))))|k2_partfun1(X46,X45,X48,k9_subset_1(X44,X46,X47))!=k2_partfun1(X47,X45,X49,k9_subset_1(X44,X46,X47))|(~v1_funct_1(X49)|~v1_funct_2(X49,X47,X45)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X45))))|(~v1_funct_1(X48)|~v1_funct_2(X48,X46,X45)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X45))))|(v1_xboole_0(X47)|~m1_subset_1(X47,k1_zfmisc_1(X44)))|(v1_xboole_0(X46)|~m1_subset_1(X46,k1_zfmisc_1(X44)))|v1_xboole_0(X45)|v1_xboole_0(X44))&(k2_partfun1(k4_subset_1(X44,X46,X47),X45,X50,X47)=X49|X50!=k1_tmap_1(X44,X45,X46,X47,X48,X49)|(~v1_funct_1(X50)|~v1_funct_2(X50,k4_subset_1(X44,X46,X47),X45)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X44,X46,X47),X45))))|k2_partfun1(X46,X45,X48,k9_subset_1(X44,X46,X47))!=k2_partfun1(X47,X45,X49,k9_subset_1(X44,X46,X47))|(~v1_funct_1(X49)|~v1_funct_2(X49,X47,X45)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X45))))|(~v1_funct_1(X48)|~v1_funct_2(X48,X46,X45)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X45))))|(v1_xboole_0(X47)|~m1_subset_1(X47,k1_zfmisc_1(X44)))|(v1_xboole_0(X46)|~m1_subset_1(X46,k1_zfmisc_1(X44)))|v1_xboole_0(X45)|v1_xboole_0(X44)))&(k2_partfun1(k4_subset_1(X44,X46,X47),X45,X50,X46)!=X48|k2_partfun1(k4_subset_1(X44,X46,X47),X45,X50,X47)!=X49|X50=k1_tmap_1(X44,X45,X46,X47,X48,X49)|(~v1_funct_1(X50)|~v1_funct_2(X50,k4_subset_1(X44,X46,X47),X45)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X44,X46,X47),X45))))|k2_partfun1(X46,X45,X48,k9_subset_1(X44,X46,X47))!=k2_partfun1(X47,X45,X49,k9_subset_1(X44,X46,X47))|(~v1_funct_1(X49)|~v1_funct_2(X49,X47,X45)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X45))))|(~v1_funct_1(X48)|~v1_funct_2(X48,X46,X45)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X45))))|(v1_xboole_0(X47)|~m1_subset_1(X47,k1_zfmisc_1(X44)))|(v1_xboole_0(X46)|~m1_subset_1(X46,k1_zfmisc_1(X44)))|v1_xboole_0(X45)|v1_xboole_0(X44))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tmap_1])])])])])).
% 0.19/0.44  cnf(c_0_31, plain, (m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2)))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.44  cnf(c_0_32, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.44  cnf(c_0_33, plain, (v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.44  cnf(c_0_34, plain, (v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.44  cnf(c_0_35, plain, (k7_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.44  cnf(c_0_36, plain, (r1_xboole_0(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.44  cnf(c_0_37, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.44  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.44  cnf(c_0_39, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.44  cnf(c_0_40, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.44  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.44  cnf(c_0_42, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.44  fof(c_0_43, plain, ![X28, X29, X30]:(~m1_subset_1(X30,k1_zfmisc_1(X28))|k9_subset_1(X28,X29,X30)=k3_xboole_0(X29,X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.19/0.44  cnf(c_0_44, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.44  cnf(c_0_45, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.44  fof(c_0_46, plain, ![X35, X36]:((~r1_subset_1(X35,X36)|r1_xboole_0(X35,X36)|(v1_xboole_0(X35)|v1_xboole_0(X36)))&(~r1_xboole_0(X35,X36)|r1_subset_1(X35,X36)|(v1_xboole_0(X35)|v1_xboole_0(X36)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).
% 0.19/0.44  cnf(c_0_47, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X3)=X6|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X4)|v1_xboole_0(X1)|X5!=k1_tmap_1(X1,X4,X2,X3,X7,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|k2_partfun1(X2,X4,X7,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_1(X6)|~v1_funct_2(X6,X3,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X7)|~v1_funct_2(X7,X2,X4)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.44  cnf(c_0_48, plain, (m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2)))|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~v1_funct_2(X6,X4,X2)|~v1_funct_2(X5,X3,X2)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.44  cnf(c_0_49, plain, (v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~v1_funct_2(X6,X4,X2)|~v1_funct_2(X5,X3,X2)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[c_0_33, c_0_32])).
% 0.19/0.44  cnf(c_0_50, plain, (v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~v1_funct_2(X6,X4,X2)|~v1_funct_2(X5,X3,X2)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[c_0_34, c_0_32])).
% 0.19/0.44  cnf(c_0_51, plain, (k7_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.44  cnf(c_0_52, negated_conjecture, (k7_relat_1(esk9_0,X1)=k2_partfun1(esk7_0,esk5_0,esk9_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])])).
% 0.19/0.44  cnf(c_0_53, negated_conjecture, (v1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_40, c_0_38])).
% 0.19/0.44  cnf(c_0_54, negated_conjecture, (k7_relat_1(esk8_0,X1)=k2_partfun1(esk6_0,esk5_0,esk8_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_41]), c_0_42])])).
% 0.19/0.44  cnf(c_0_55, negated_conjecture, (v1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.44  cnf(c_0_56, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.44  cnf(c_0_57, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.44  cnf(c_0_58, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.44  cnf(c_0_59, plain, (r1_xboole_0(X1,X2)|v1_xboole_0(X1)|v1_xboole_0(X2)|~r1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.44  cnf(c_0_60, negated_conjecture, (r1_subset_1(esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.44  cnf(c_0_61, negated_conjecture, (~v1_xboole_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.44  cnf(c_0_62, negated_conjecture, (~v1_xboole_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.44  cnf(c_0_63, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X3)=X6|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_2(X5,X2,X4)|~v1_funct_2(X6,X3,X4)|~v1_funct_1(X5)|~v1_funct_1(X6)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_47, c_0_32])]), c_0_48]), c_0_49]), c_0_50])).
% 0.19/0.44  cnf(c_0_64, negated_conjecture, (k2_partfun1(esk7_0,esk5_0,esk9_0,X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])])).
% 0.19/0.44  cnf(c_0_65, negated_conjecture, (v1_funct_2(esk9_0,esk7_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.44  cnf(c_0_66, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.44  cnf(c_0_67, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X2)=X6|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X4)|v1_xboole_0(X1)|X5!=k1_tmap_1(X1,X4,X2,X3,X6,X7)|~v1_funct_1(X5)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|k2_partfun1(X2,X4,X6,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X7,k9_subset_1(X1,X2,X3))|~v1_funct_1(X7)|~v1_funct_2(X7,X3,X4)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X6)|~v1_funct_2(X6,X2,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.44  cnf(c_0_68, negated_conjecture, (k2_partfun1(esk6_0,esk5_0,esk8_0,k9_subset_1(esk4_0,esk6_0,esk7_0))!=k2_partfun1(esk7_0,esk5_0,esk9_0,k9_subset_1(esk4_0,esk6_0,esk7_0))|k2_partfun1(k4_subset_1(esk4_0,esk6_0,esk7_0),esk5_0,k1_tmap_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk6_0)!=esk8_0|k2_partfun1(k4_subset_1(esk4_0,esk6_0,esk7_0),esk5_0,k1_tmap_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk7_0)!=esk9_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.44  cnf(c_0_69, negated_conjecture, (k2_partfun1(esk6_0,esk5_0,esk8_0,X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_54]), c_0_55])])).
% 0.19/0.44  cnf(c_0_70, plain, (k9_subset_1(X2,X3,X1)=k4_xboole_0(X3,k4_xboole_0(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_56, c_0_45])).
% 0.19/0.44  cnf(c_0_71, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.44  cnf(c_0_72, plain, (v1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.19/0.44  cnf(c_0_73, negated_conjecture, (r1_xboole_0(esk6_0,esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61]), c_0_62])).
% 0.19/0.44  cnf(c_0_74, negated_conjecture, (k2_partfun1(k4_subset_1(X1,X2,esk7_0),esk5_0,k1_tmap_1(X1,esk5_0,X2,esk7_0,X3,esk9_0),esk7_0)=esk9_0|v1_xboole_0(X2)|k2_partfun1(X2,esk5_0,X3,k9_subset_1(X1,X2,esk7_0))!=k1_xboole_0|~v1_funct_2(X3,X2,esk5_0)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,esk5_0)))|~m1_subset_1(esk7_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_xboole_0(k9_subset_1(X1,X2,esk7_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65]), c_0_39]), c_0_38])]), c_0_61]), c_0_66])).
% 0.19/0.44  cnf(c_0_75, negated_conjecture, (v1_funct_2(esk8_0,esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.44  cnf(c_0_76, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X2)=X5|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_2(X6,X3,X4)|~v1_funct_2(X5,X2,X4)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_67, c_0_32])]), c_0_48]), c_0_49]), c_0_50])).
% 0.19/0.44  cnf(c_0_77, negated_conjecture, (k2_partfun1(k4_subset_1(esk4_0,esk6_0,esk7_0),esk5_0,k1_tmap_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk6_0)!=esk8_0|k2_partfun1(k4_subset_1(esk4_0,esk6_0,esk7_0),esk5_0,k1_tmap_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk7_0)!=esk9_0|~v1_xboole_0(k9_subset_1(esk4_0,esk6_0,esk7_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_64])).
% 0.19/0.44  cnf(c_0_78, negated_conjecture, (k9_subset_1(esk4_0,X1,esk7_0)=k4_xboole_0(X1,k4_xboole_0(X1,esk7_0))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.19/0.44  cnf(c_0_79, negated_conjecture, (v1_xboole_0(k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk7_0)))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.19/0.44  cnf(c_0_80, negated_conjecture, (k2_partfun1(k4_subset_1(X1,esk6_0,esk7_0),esk5_0,k1_tmap_1(X1,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk7_0)=esk9_0|~m1_subset_1(esk7_0,k1_zfmisc_1(X1))|~m1_subset_1(esk6_0,k1_zfmisc_1(X1))|~v1_xboole_0(k9_subset_1(X1,esk6_0,esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_69]), c_0_75]), c_0_42]), c_0_41])]), c_0_62])).
% 0.19/0.44  cnf(c_0_81, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.44  cnf(c_0_82, negated_conjecture, (k2_partfun1(k4_subset_1(X1,X2,esk7_0),esk5_0,k1_tmap_1(X1,esk5_0,X2,esk7_0,X3,esk9_0),X2)=X3|v1_xboole_0(X2)|k2_partfun1(X2,esk5_0,X3,k9_subset_1(X1,X2,esk7_0))!=k1_xboole_0|~v1_funct_2(X3,X2,esk5_0)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,esk5_0)))|~m1_subset_1(esk7_0,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~v1_xboole_0(k9_subset_1(X1,X2,esk7_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_64]), c_0_65]), c_0_39]), c_0_38])]), c_0_61]), c_0_66])).
% 0.19/0.44  cnf(c_0_83, negated_conjecture, (k2_partfun1(k4_subset_1(esk4_0,esk6_0,esk7_0),esk5_0,k1_tmap_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk6_0)!=esk8_0|k2_partfun1(k4_subset_1(esk4_0,esk6_0,esk7_0),esk5_0,k1_tmap_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk7_0)!=esk9_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_78]), c_0_79])])).
% 0.19/0.44  cnf(c_0_84, negated_conjecture, (k2_partfun1(k4_subset_1(esk4_0,esk6_0,esk7_0),esk5_0,k1_tmap_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk7_0)=esk9_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_71]), c_0_81]), c_0_78]), c_0_79])])).
% 0.19/0.44  cnf(c_0_85, negated_conjecture, (k2_partfun1(k4_subset_1(X1,esk6_0,esk7_0),esk5_0,k1_tmap_1(X1,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk6_0)=esk8_0|~m1_subset_1(esk7_0,k1_zfmisc_1(X1))|~m1_subset_1(esk6_0,k1_zfmisc_1(X1))|~v1_xboole_0(k9_subset_1(X1,esk6_0,esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_69]), c_0_75]), c_0_42]), c_0_41])]), c_0_62])).
% 0.19/0.44  cnf(c_0_86, negated_conjecture, (k2_partfun1(k4_subset_1(esk4_0,esk6_0,esk7_0),esk5_0,k1_tmap_1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),esk6_0)!=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_84])])).
% 0.19/0.44  cnf(c_0_87, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_71]), c_0_81]), c_0_78]), c_0_79])]), c_0_86]), ['proof']).
% 0.19/0.44  # SZS output end CNFRefutation
% 0.19/0.44  # Proof object total steps             : 88
% 0.19/0.44  # Proof object clause steps            : 59
% 0.19/0.44  # Proof object formula steps           : 29
% 0.19/0.44  # Proof object conjectures             : 34
% 0.19/0.44  # Proof object clause conjectures      : 31
% 0.19/0.44  # Proof object formula conjectures     : 3
% 0.19/0.44  # Proof object initial clauses used    : 30
% 0.19/0.44  # Proof object initial formulas used   : 14
% 0.19/0.44  # Proof object generating inferences   : 20
% 0.19/0.44  # Proof object simplifying inferences  : 62
% 0.19/0.44  # Training examples: 0 positive, 0 negative
% 0.19/0.44  # Parsed axioms                        : 14
% 0.19/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.44  # Initial clauses                      : 36
% 0.19/0.44  # Removed in clause preprocessing      : 1
% 0.19/0.44  # Initial clauses in saturation        : 35
% 0.19/0.44  # Processed clauses                    : 905
% 0.19/0.44  # ...of these trivial                  : 19
% 0.19/0.44  # ...subsumed                          : 426
% 0.19/0.44  # ...remaining for further processing  : 460
% 0.19/0.44  # Other redundant clauses eliminated   : 4
% 0.19/0.44  # Clauses deleted for lack of memory   : 0
% 0.19/0.44  # Backward-subsumed                    : 6
% 0.19/0.44  # Backward-rewritten                   : 5
% 0.19/0.44  # Generated clauses                    : 2129
% 0.19/0.44  # ...of the previous two non-trivial   : 1885
% 0.19/0.44  # Contextual simplify-reflections      : 13
% 0.19/0.44  # Paramodulations                      : 2121
% 0.19/0.44  # Factorizations                       : 0
% 0.19/0.44  # Equation resolutions                 : 9
% 0.19/0.44  # Propositional unsat checks           : 0
% 0.19/0.44  #    Propositional check models        : 0
% 0.19/0.44  #    Propositional check unsatisfiable : 0
% 0.19/0.44  #    Propositional clauses             : 0
% 0.19/0.44  #    Propositional clauses after purity: 0
% 0.19/0.44  #    Propositional unsat core size     : 0
% 0.19/0.44  #    Propositional preprocessing time  : 0.000
% 0.19/0.44  #    Propositional encoding time       : 0.000
% 0.19/0.44  #    Propositional solver time         : 0.000
% 0.19/0.44  #    Success case prop preproc time    : 0.000
% 0.19/0.44  #    Success case prop encoding time   : 0.000
% 0.19/0.44  #    Success case prop solver time     : 0.000
% 0.19/0.44  # Current number of processed clauses  : 411
% 0.19/0.44  #    Positive orientable unit clauses  : 100
% 0.19/0.44  #    Positive unorientable unit clauses: 2
% 0.19/0.44  #    Negative unit clauses             : 5
% 0.19/0.44  #    Non-unit-clauses                  : 304
% 0.19/0.44  # Current number of unprocessed clauses: 1050
% 0.19/0.44  # ...number of literals in the above   : 2577
% 0.19/0.44  # Current number of archived formulas  : 0
% 0.19/0.44  # Current number of archived clauses   : 47
% 0.19/0.44  # Clause-clause subsumption calls (NU) : 38520
% 0.19/0.44  # Rec. Clause-clause subsumption calls : 15912
% 0.19/0.44  # Non-unit clause-clause subsumptions  : 407
% 0.19/0.44  # Unit Clause-clause subsumption calls : 1694
% 0.19/0.44  # Rewrite failures with RHS unbound    : 0
% 0.19/0.44  # BW rewrite match attempts            : 480
% 0.19/0.44  # BW rewrite match successes           : 6
% 0.19/0.44  # Condensation attempts                : 0
% 0.19/0.44  # Condensation successes               : 0
% 0.19/0.44  # Termbank termtop insertions          : 56516
% 0.19/0.44  
% 0.19/0.44  # -------------------------------------------------
% 0.19/0.44  # User time                : 0.103 s
% 0.19/0.44  # System time              : 0.006 s
% 0.19/0.44  # Total time               : 0.109 s
% 0.19/0.44  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
