%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:41 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 564 expanded)
%              Number of clauses        :   63 ( 227 expanded)
%              Number of leaves         :   13 ( 139 expanded)
%              Depth                    :   12
%              Number of atoms          :  472 (4372 expanded)
%              Number of equality atoms :   84 ( 760 expanded)
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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

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

fof(c_0_13,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(X16,X17)
        | X16 != X17 )
      & ( r1_tarski(X17,X16)
        | X16 != X17 )
      & ( ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X17,X16)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_14,negated_conjecture,(
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

fof(c_0_15,plain,(
    ! [X22,X23] :
      ( ( ~ m1_subset_1(X22,k1_zfmisc_1(X23))
        | r1_tarski(X22,X23) )
      & ( ~ r1_tarski(X22,X23)
        | m1_subset_1(X22,k1_zfmisc_1(X23)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X10,X11,X13,X14,X15] :
      ( ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_2(X10,X11),X11)
        | r1_xboole_0(X10,X11) )
      & ( ~ r2_hidden(X15,X13)
        | ~ r2_hidden(X15,X14)
        | ~ r1_xboole_0(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_18,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(X19))
      | k9_subset_1(X19,X20,X21) = k3_xboole_0(X20,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_19,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

cnf(c_0_20,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X26,X27] :
      ( ( ~ r1_subset_1(X26,X27)
        | r1_xboole_0(X26,X27)
        | v1_xboole_0(X26)
        | v1_xboole_0(X27) )
      & ( ~ r1_xboole_0(X26,X27)
        | r1_subset_1(X26,X27)
        | v1_xboole_0(X26)
        | v1_xboole_0(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_25,plain,(
    ! [X8,X9] :
      ( ( ~ r1_xboole_0(X8,X9)
        | k3_xboole_0(X8,X9) = k1_xboole_0 )
      & ( k3_xboole_0(X8,X9) != k1_xboole_0
        | r1_xboole_0(X8,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_26,plain,(
    ! [X18] : k3_xboole_0(X18,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_27,plain,(
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

fof(c_0_28,plain,(
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

cnf(c_0_29,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_32,plain,
    ( r1_xboole_0(X1,X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( r1_subset_1(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_34,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_35,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_36,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_37,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_38,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_40,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_41,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_43,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_44,negated_conjecture,
    ( k9_subset_1(esk2_0,X1,esk5_0) = k3_xboole_0(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,X2) = k9_subset_1(X2,X1,X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_31])).

cnf(c_0_46,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_47,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35])).

fof(c_0_48,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X24)
      | ~ r1_xboole_0(X25,k1_relat_1(X24))
      | k7_relat_1(X24,X25) = k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t187_relat_1])])])).

cnf(c_0_49,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_50,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_51,plain,(
    ! [X39,X40,X41,X42] :
      ( ~ v1_funct_1(X41)
      | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
      | k2_partfun1(X39,X40,X41,X42) = k7_relat_1(X41,X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

fof(c_0_52,plain,(
    ! [X28,X29,X30] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | v1_relat_1(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_53,plain,
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
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_40]),c_0_41]),c_0_42]),c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( k9_subset_1(esk2_0,X1,esk5_0) = k9_subset_1(esk5_0,X1,esk5_0) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_56,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_57,plain,
    ( k7_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_58,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_59,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_61,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_62,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_63,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_65,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_66,negated_conjecture,
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
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_30])]),c_0_55]),c_0_34])).

cnf(c_0_67,negated_conjecture,
    ( k9_subset_1(esk5_0,esk4_0,esk5_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_56,c_0_45])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_69,plain,
    ( k7_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_70,negated_conjecture,
    ( k7_relat_1(esk7_0,X1) = k2_partfun1(esk5_0,esk3_0,esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])])).

cnf(c_0_71,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_60])).

cnf(c_0_72,plain,
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
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_63]),c_0_41]),c_0_42]),c_0_43])).

cnf(c_0_73,negated_conjecture,
    ( k7_relat_1(esk6_0,X1) = k2_partfun1(esk4_0,esk3_0,esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_64]),c_0_65])])).

cnf(c_0_74,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_64])).

cnf(c_0_75,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),X1,k1_tmap_1(esk2_0,X1,esk4_0,esk5_0,X2,X3),esk4_0) = X2
    | v1_xboole_0(X1)
    | k2_partfun1(esk4_0,X1,X2,k1_xboole_0) != k2_partfun1(esk5_0,X1,X3,k1_xboole_0)
    | ~ v1_funct_2(X3,esk5_0,X1)
    | ~ v1_funct_2(X2,esk4_0,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])]),c_0_35])).

cnf(c_0_76,negated_conjecture,
    ( k2_partfun1(esk5_0,esk3_0,esk7_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])])).

cnf(c_0_77,negated_conjecture,
    ( v1_funct_2(esk7_0,esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_78,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_79,negated_conjecture,
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
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_54]),c_0_30])]),c_0_55]),c_0_34])).

cnf(c_0_80,negated_conjecture,
    ( k2_partfun1(esk4_0,esk3_0,esk6_0,k9_subset_1(esk2_0,esk4_0,esk5_0)) != k2_partfun1(esk5_0,esk3_0,esk7_0,k9_subset_1(esk2_0,esk4_0,esk5_0))
    | k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0) != esk6_0
    | k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0) != esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_81,negated_conjecture,
    ( k2_partfun1(esk4_0,esk3_0,esk6_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_73]),c_0_74])])).

cnf(c_0_82,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,X1,esk7_0),esk4_0) = X1
    | k2_partfun1(esk4_0,esk3_0,X1,k1_xboole_0) != k1_xboole_0
    | ~ v1_funct_2(X1,esk4_0,esk3_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77]),c_0_61]),c_0_60])]),c_0_78])).

cnf(c_0_83,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_84,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),X1,k1_tmap_1(esk2_0,X1,esk4_0,esk5_0,X2,X3),esk5_0) = X3
    | v1_xboole_0(X1)
    | k2_partfun1(esk4_0,X1,X2,k1_xboole_0) != k2_partfun1(esk5_0,X1,X3,k1_xboole_0)
    | ~ v1_funct_2(X3,esk5_0,X1)
    | ~ v1_funct_2(X2,esk4_0,X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_67]),c_0_68])]),c_0_35])).

cnf(c_0_85,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0) != esk6_0
    | k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0) != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_44]),c_0_56]),c_0_81]),c_0_44]),c_0_56]),c_0_76])])).

cnf(c_0_86,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_81]),c_0_83]),c_0_65]),c_0_64])])).

cnf(c_0_87,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,X1),esk5_0) = X1
    | k2_partfun1(esk5_0,esk3_0,X1,k1_xboole_0) != k1_xboole_0
    | ~ v1_funct_2(X1,esk5_0,esk3_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_81]),c_0_83]),c_0_65]),c_0_64])]),c_0_78])).

cnf(c_0_88,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0) != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_86])])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_76]),c_0_77]),c_0_61]),c_0_60])]),c_0_88]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 21:01:30 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.19/0.45  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.19/0.45  # and selection function SelectCQIPrecWNTNp.
% 0.19/0.45  #
% 0.19/0.45  # Preprocessing time       : 0.030 s
% 0.19/0.45  # Presaturation interreduction done
% 0.19/0.45  
% 0.19/0.45  # Proof found!
% 0.19/0.45  # SZS status Theorem
% 0.19/0.45  # SZS output start CNFRefutation
% 0.19/0.45  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.45  fof(t6_tmap_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>(r1_subset_1(X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3)=X5)&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4)=X6)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tmap_1)).
% 0.19/0.45  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.45  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.19/0.45  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.19/0.45  fof(redefinition_r1_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))=>(r1_subset_1(X1,X2)<=>r1_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 0.19/0.45  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.19/0.45  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.19/0.45  fof(d1_tmap_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>(k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))=>![X7]:(((v1_funct_1(X7)&v1_funct_2(X7,k4_subset_1(X1,X3,X4),X2))&m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))))=>(X7=k1_tmap_1(X1,X2,X3,X4,X5,X6)<=>(k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X3)=X5&k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X4)=X6)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tmap_1)).
% 0.19/0.45  fof(dt_k1_tmap_1, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((((((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))&~(v1_xboole_0(X3)))&m1_subset_1(X3,k1_zfmisc_1(X1)))&~(v1_xboole_0(X4)))&m1_subset_1(X4,k1_zfmisc_1(X1)))&v1_funct_1(X5))&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2))&m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 0.19/0.45  fof(t187_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_xboole_0(X2,k1_relat_1(X1))=>k7_relat_1(X1,X2)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 0.19/0.45  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 0.19/0.45  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.45  fof(c_0_13, plain, ![X16, X17]:(((r1_tarski(X16,X17)|X16!=X17)&(r1_tarski(X17,X16)|X16!=X17))&(~r1_tarski(X16,X17)|~r1_tarski(X17,X16)|X16=X17)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.45  fof(c_0_14, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>(r1_subset_1(X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3)=X5)&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4)=X6))))))))), inference(assume_negation,[status(cth)],[t6_tmap_1])).
% 0.19/0.45  fof(c_0_15, plain, ![X22, X23]:((~m1_subset_1(X22,k1_zfmisc_1(X23))|r1_tarski(X22,X23))&(~r1_tarski(X22,X23)|m1_subset_1(X22,k1_zfmisc_1(X23)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.45  cnf(c_0_16, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.45  fof(c_0_17, plain, ![X10, X11, X13, X14, X15]:(((r2_hidden(esk1_2(X10,X11),X10)|r1_xboole_0(X10,X11))&(r2_hidden(esk1_2(X10,X11),X11)|r1_xboole_0(X10,X11)))&(~r2_hidden(X15,X13)|~r2_hidden(X15,X14)|~r1_xboole_0(X13,X14))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.19/0.45  fof(c_0_18, plain, ![X19, X20, X21]:(~m1_subset_1(X21,k1_zfmisc_1(X19))|k9_subset_1(X19,X20,X21)=k3_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.19/0.45  fof(c_0_19, negated_conjecture, (~v1_xboole_0(esk2_0)&(~v1_xboole_0(esk3_0)&((~v1_xboole_0(esk4_0)&m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)))&((~v1_xboole_0(esk5_0)&m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0)))&(r1_subset_1(esk4_0,esk5_0)&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk4_0,esk3_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))))&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk5_0,esk3_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0))))&(k2_partfun1(esk4_0,esk3_0,esk6_0,k9_subset_1(esk2_0,esk4_0,esk5_0))!=k2_partfun1(esk5_0,esk3_0,esk7_0,k9_subset_1(esk2_0,esk4_0,esk5_0))|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0)!=esk6_0|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0)!=esk7_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.19/0.45  cnf(c_0_20, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.45  cnf(c_0_21, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_16])).
% 0.19/0.45  fof(c_0_22, plain, ![X26, X27]:((~r1_subset_1(X26,X27)|r1_xboole_0(X26,X27)|(v1_xboole_0(X26)|v1_xboole_0(X27)))&(~r1_xboole_0(X26,X27)|r1_subset_1(X26,X27)|(v1_xboole_0(X26)|v1_xboole_0(X27)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).
% 0.19/0.45  cnf(c_0_23, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.45  cnf(c_0_24, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.45  fof(c_0_25, plain, ![X8, X9]:((~r1_xboole_0(X8,X9)|k3_xboole_0(X8,X9)=k1_xboole_0)&(k3_xboole_0(X8,X9)!=k1_xboole_0|r1_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.19/0.45  fof(c_0_26, plain, ![X18]:k3_xboole_0(X18,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.19/0.45  fof(c_0_27, plain, ![X43, X44, X45, X46, X47, X48, X49]:(((k2_partfun1(k4_subset_1(X43,X45,X46),X44,X49,X45)=X47|X49!=k1_tmap_1(X43,X44,X45,X46,X47,X48)|(~v1_funct_1(X49)|~v1_funct_2(X49,k4_subset_1(X43,X45,X46),X44)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X43,X45,X46),X44))))|k2_partfun1(X45,X44,X47,k9_subset_1(X43,X45,X46))!=k2_partfun1(X46,X44,X48,k9_subset_1(X43,X45,X46))|(~v1_funct_1(X48)|~v1_funct_2(X48,X46,X44)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X44))))|(~v1_funct_1(X47)|~v1_funct_2(X47,X45,X44)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X44))))|(v1_xboole_0(X46)|~m1_subset_1(X46,k1_zfmisc_1(X43)))|(v1_xboole_0(X45)|~m1_subset_1(X45,k1_zfmisc_1(X43)))|v1_xboole_0(X44)|v1_xboole_0(X43))&(k2_partfun1(k4_subset_1(X43,X45,X46),X44,X49,X46)=X48|X49!=k1_tmap_1(X43,X44,X45,X46,X47,X48)|(~v1_funct_1(X49)|~v1_funct_2(X49,k4_subset_1(X43,X45,X46),X44)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X43,X45,X46),X44))))|k2_partfun1(X45,X44,X47,k9_subset_1(X43,X45,X46))!=k2_partfun1(X46,X44,X48,k9_subset_1(X43,X45,X46))|(~v1_funct_1(X48)|~v1_funct_2(X48,X46,X44)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X44))))|(~v1_funct_1(X47)|~v1_funct_2(X47,X45,X44)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X44))))|(v1_xboole_0(X46)|~m1_subset_1(X46,k1_zfmisc_1(X43)))|(v1_xboole_0(X45)|~m1_subset_1(X45,k1_zfmisc_1(X43)))|v1_xboole_0(X44)|v1_xboole_0(X43)))&(k2_partfun1(k4_subset_1(X43,X45,X46),X44,X49,X45)!=X47|k2_partfun1(k4_subset_1(X43,X45,X46),X44,X49,X46)!=X48|X49=k1_tmap_1(X43,X44,X45,X46,X47,X48)|(~v1_funct_1(X49)|~v1_funct_2(X49,k4_subset_1(X43,X45,X46),X44)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X43,X45,X46),X44))))|k2_partfun1(X45,X44,X47,k9_subset_1(X43,X45,X46))!=k2_partfun1(X46,X44,X48,k9_subset_1(X43,X45,X46))|(~v1_funct_1(X48)|~v1_funct_2(X48,X46,X44)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X44))))|(~v1_funct_1(X47)|~v1_funct_2(X47,X45,X44)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X44))))|(v1_xboole_0(X46)|~m1_subset_1(X46,k1_zfmisc_1(X43)))|(v1_xboole_0(X45)|~m1_subset_1(X45,k1_zfmisc_1(X43)))|v1_xboole_0(X44)|v1_xboole_0(X43))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tmap_1])])])])])).
% 0.19/0.45  fof(c_0_28, plain, ![X50, X51, X52, X53, X54, X55]:(((v1_funct_1(k1_tmap_1(X50,X51,X52,X53,X54,X55))|(v1_xboole_0(X50)|v1_xboole_0(X51)|v1_xboole_0(X52)|~m1_subset_1(X52,k1_zfmisc_1(X50))|v1_xboole_0(X53)|~m1_subset_1(X53,k1_zfmisc_1(X50))|~v1_funct_1(X54)|~v1_funct_2(X54,X52,X51)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X51)))|~v1_funct_1(X55)|~v1_funct_2(X55,X53,X51)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X51)))))&(v1_funct_2(k1_tmap_1(X50,X51,X52,X53,X54,X55),k4_subset_1(X50,X52,X53),X51)|(v1_xboole_0(X50)|v1_xboole_0(X51)|v1_xboole_0(X52)|~m1_subset_1(X52,k1_zfmisc_1(X50))|v1_xboole_0(X53)|~m1_subset_1(X53,k1_zfmisc_1(X50))|~v1_funct_1(X54)|~v1_funct_2(X54,X52,X51)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X51)))|~v1_funct_1(X55)|~v1_funct_2(X55,X53,X51)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X51))))))&(m1_subset_1(k1_tmap_1(X50,X51,X52,X53,X54,X55),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X50,X52,X53),X51)))|(v1_xboole_0(X50)|v1_xboole_0(X51)|v1_xboole_0(X52)|~m1_subset_1(X52,k1_zfmisc_1(X50))|v1_xboole_0(X53)|~m1_subset_1(X53,k1_zfmisc_1(X50))|~v1_funct_1(X54)|~v1_funct_2(X54,X52,X51)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X51)))|~v1_funct_1(X55)|~v1_funct_2(X55,X53,X51)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X51)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tmap_1])])])])).
% 0.19/0.45  cnf(c_0_29, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.45  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.45  cnf(c_0_31, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.45  cnf(c_0_32, plain, (r1_xboole_0(X1,X2)|v1_xboole_0(X1)|v1_xboole_0(X2)|~r1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.45  cnf(c_0_33, negated_conjecture, (r1_subset_1(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.45  cnf(c_0_34, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.45  cnf(c_0_35, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.45  cnf(c_0_36, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.45  cnf(c_0_37, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.45  cnf(c_0_38, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.45  cnf(c_0_39, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.45  cnf(c_0_40, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X2)=X6|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X4)|v1_xboole_0(X1)|X5!=k1_tmap_1(X1,X4,X2,X3,X6,X7)|~v1_funct_1(X5)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|k2_partfun1(X2,X4,X6,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X7,k9_subset_1(X1,X2,X3))|~v1_funct_1(X7)|~v1_funct_2(X7,X3,X4)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X6)|~v1_funct_2(X6,X2,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.45  cnf(c_0_41, plain, (m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2)))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.45  cnf(c_0_42, plain, (v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.45  cnf(c_0_43, plain, (v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.45  cnf(c_0_44, negated_conjecture, (k9_subset_1(esk2_0,X1,esk5_0)=k3_xboole_0(X1,esk5_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.45  cnf(c_0_45, plain, (k3_xboole_0(X1,X2)=k9_subset_1(X2,X1,X2)), inference(spm,[status(thm)],[c_0_29, c_0_31])).
% 0.19/0.45  cnf(c_0_46, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.45  cnf(c_0_47, negated_conjecture, (r1_xboole_0(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35])).
% 0.19/0.45  fof(c_0_48, plain, ![X24, X25]:(~v1_relat_1(X24)|(~r1_xboole_0(X25,k1_relat_1(X24))|k7_relat_1(X24,X25)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t187_relat_1])])])).
% 0.19/0.45  cnf(c_0_49, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.45  cnf(c_0_50, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.45  fof(c_0_51, plain, ![X39, X40, X41, X42]:(~v1_funct_1(X41)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|k2_partfun1(X39,X40,X41,X42)=k7_relat_1(X41,X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 0.19/0.45  fof(c_0_52, plain, ![X28, X29, X30]:(~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|v1_relat_1(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.45  cnf(c_0_53, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X2)=X5|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_2(X6,X3,X4)|~v1_funct_2(X5,X2,X4)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_40]), c_0_41]), c_0_42]), c_0_43])).
% 0.19/0.45  cnf(c_0_54, negated_conjecture, (k9_subset_1(esk2_0,X1,esk5_0)=k9_subset_1(esk5_0,X1,esk5_0)), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.45  cnf(c_0_55, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.45  cnf(c_0_56, negated_conjecture, (k3_xboole_0(esk4_0,esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.45  cnf(c_0_57, plain, (k7_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.45  cnf(c_0_58, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.45  cnf(c_0_59, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.45  cnf(c_0_60, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.45  cnf(c_0_61, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.45  cnf(c_0_62, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.45  cnf(c_0_63, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X3)=X6|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X4)|v1_xboole_0(X1)|X5!=k1_tmap_1(X1,X4,X2,X3,X7,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|k2_partfun1(X2,X4,X7,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_1(X6)|~v1_funct_2(X6,X3,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X7)|~v1_funct_2(X7,X2,X4)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.45  cnf(c_0_64, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.45  cnf(c_0_65, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.45  cnf(c_0_66, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,X1,esk5_0),X2,k1_tmap_1(esk2_0,X2,X1,esk5_0,X3,X4),X1)=X3|v1_xboole_0(X2)|v1_xboole_0(X1)|k2_partfun1(X1,X2,X3,k9_subset_1(esk5_0,X1,esk5_0))!=k2_partfun1(esk5_0,X2,X4,k9_subset_1(esk5_0,X1,esk5_0))|~v1_funct_2(X4,esk5_0,X2)|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X4)|~v1_funct_1(X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_30])]), c_0_55]), c_0_34])).
% 0.19/0.45  cnf(c_0_67, negated_conjecture, (k9_subset_1(esk5_0,esk4_0,esk5_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_56, c_0_45])).
% 0.19/0.45  cnf(c_0_68, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.45  cnf(c_0_69, plain, (k7_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.19/0.45  cnf(c_0_70, negated_conjecture, (k7_relat_1(esk7_0,X1)=k2_partfun1(esk5_0,esk3_0,esk7_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])])).
% 0.19/0.45  cnf(c_0_71, negated_conjecture, (v1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_62, c_0_60])).
% 0.19/0.45  cnf(c_0_72, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X3)=X6|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_2(X5,X2,X4)|~v1_funct_2(X6,X3,X4)|~v1_funct_1(X5)|~v1_funct_1(X6)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_63]), c_0_41]), c_0_42]), c_0_43])).
% 0.19/0.45  cnf(c_0_73, negated_conjecture, (k7_relat_1(esk6_0,X1)=k2_partfun1(esk4_0,esk3_0,esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_64]), c_0_65])])).
% 0.19/0.45  cnf(c_0_74, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_62, c_0_64])).
% 0.19/0.45  cnf(c_0_75, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),X1,k1_tmap_1(esk2_0,X1,esk4_0,esk5_0,X2,X3),esk4_0)=X2|v1_xboole_0(X1)|k2_partfun1(esk4_0,X1,X2,k1_xboole_0)!=k2_partfun1(esk5_0,X1,X3,k1_xboole_0)|~v1_funct_2(X3,esk5_0,X1)|~v1_funct_2(X2,esk4_0,X1)|~v1_funct_1(X3)|~v1_funct_1(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68])]), c_0_35])).
% 0.19/0.45  cnf(c_0_76, negated_conjecture, (k2_partfun1(esk5_0,esk3_0,esk7_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])])).
% 0.19/0.45  cnf(c_0_77, negated_conjecture, (v1_funct_2(esk7_0,esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.45  cnf(c_0_78, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.45  cnf(c_0_79, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,X1,esk5_0),X2,k1_tmap_1(esk2_0,X2,X1,esk5_0,X3,X4),esk5_0)=X4|v1_xboole_0(X2)|v1_xboole_0(X1)|k2_partfun1(X1,X2,X3,k9_subset_1(esk5_0,X1,esk5_0))!=k2_partfun1(esk5_0,X2,X4,k9_subset_1(esk5_0,X1,esk5_0))|~v1_funct_2(X4,esk5_0,X2)|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_54]), c_0_30])]), c_0_55]), c_0_34])).
% 0.19/0.45  cnf(c_0_80, negated_conjecture, (k2_partfun1(esk4_0,esk3_0,esk6_0,k9_subset_1(esk2_0,esk4_0,esk5_0))!=k2_partfun1(esk5_0,esk3_0,esk7_0,k9_subset_1(esk2_0,esk4_0,esk5_0))|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0)!=esk6_0|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0)!=esk7_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.45  cnf(c_0_81, negated_conjecture, (k2_partfun1(esk4_0,esk3_0,esk6_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_73]), c_0_74])])).
% 0.19/0.45  cnf(c_0_82, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,X1,esk7_0),esk4_0)=X1|k2_partfun1(esk4_0,esk3_0,X1,k1_xboole_0)!=k1_xboole_0|~v1_funct_2(X1,esk4_0,esk3_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77]), c_0_61]), c_0_60])]), c_0_78])).
% 0.19/0.45  cnf(c_0_83, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.45  cnf(c_0_84, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),X1,k1_tmap_1(esk2_0,X1,esk4_0,esk5_0,X2,X3),esk5_0)=X3|v1_xboole_0(X1)|k2_partfun1(esk4_0,X1,X2,k1_xboole_0)!=k2_partfun1(esk5_0,X1,X3,k1_xboole_0)|~v1_funct_2(X3,esk5_0,X1)|~v1_funct_2(X2,esk4_0,X1)|~v1_funct_1(X2)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_67]), c_0_68])]), c_0_35])).
% 0.19/0.45  cnf(c_0_85, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0)!=esk6_0|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0)!=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_44]), c_0_56]), c_0_81]), c_0_44]), c_0_56]), c_0_76])])).
% 0.19/0.45  cnf(c_0_86, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0)=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_81]), c_0_83]), c_0_65]), c_0_64])])).
% 0.19/0.45  cnf(c_0_87, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,X1),esk5_0)=X1|k2_partfun1(esk5_0,esk3_0,X1,k1_xboole_0)!=k1_xboole_0|~v1_funct_2(X1,esk5_0,esk3_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_81]), c_0_83]), c_0_65]), c_0_64])]), c_0_78])).
% 0.19/0.45  cnf(c_0_88, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0)!=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_86])])).
% 0.19/0.45  cnf(c_0_89, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_76]), c_0_77]), c_0_61]), c_0_60])]), c_0_88]), ['proof']).
% 0.19/0.45  # SZS output end CNFRefutation
% 0.19/0.45  # Proof object total steps             : 90
% 0.19/0.45  # Proof object clause steps            : 63
% 0.19/0.45  # Proof object formula steps           : 27
% 0.19/0.45  # Proof object conjectures             : 38
% 0.19/0.45  # Proof object clause conjectures      : 35
% 0.19/0.45  # Proof object formula conjectures     : 3
% 0.19/0.45  # Proof object initial clauses used    : 32
% 0.19/0.45  # Proof object initial formulas used   : 13
% 0.19/0.45  # Proof object generating inferences   : 24
% 0.19/0.45  # Proof object simplifying inferences  : 63
% 0.19/0.45  # Training examples: 0 positive, 0 negative
% 0.19/0.45  # Parsed axioms                        : 16
% 0.19/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.45  # Initial clauses                      : 43
% 0.19/0.45  # Removed in clause preprocessing      : 1
% 0.19/0.45  # Initial clauses in saturation        : 42
% 0.19/0.45  # Processed clauses                    : 570
% 0.19/0.45  # ...of these trivial                  : 10
% 0.19/0.45  # ...subsumed                          : 21
% 0.19/0.45  # ...remaining for further processing  : 539
% 0.19/0.45  # Other redundant clauses eliminated   : 7
% 0.19/0.45  # Clauses deleted for lack of memory   : 0
% 0.19/0.45  # Backward-subsumed                    : 2
% 0.19/0.45  # Backward-rewritten                   : 36
% 0.19/0.45  # Generated clauses                    : 702
% 0.19/0.45  # ...of the previous two non-trivial   : 659
% 0.19/0.45  # Contextual simplify-reflections      : 6
% 0.19/0.45  # Paramodulations                      : 687
% 0.19/0.45  # Factorizations                       : 0
% 0.19/0.45  # Equation resolutions                 : 16
% 0.19/0.45  # Propositional unsat checks           : 0
% 0.19/0.45  #    Propositional check models        : 0
% 0.19/0.45  #    Propositional check unsatisfiable : 0
% 0.19/0.45  #    Propositional clauses             : 0
% 0.19/0.45  #    Propositional clauses after purity: 0
% 0.19/0.45  #    Propositional unsat core size     : 0
% 0.19/0.45  #    Propositional preprocessing time  : 0.000
% 0.19/0.45  #    Propositional encoding time       : 0.000
% 0.19/0.45  #    Propositional solver time         : 0.000
% 0.19/0.45  #    Success case prop preproc time    : 0.000
% 0.19/0.45  #    Success case prop encoding time   : 0.000
% 0.19/0.45  #    Success case prop solver time     : 0.000
% 0.19/0.45  # Current number of processed clauses  : 454
% 0.19/0.45  #    Positive orientable unit clauses  : 135
% 0.19/0.45  #    Positive unorientable unit clauses: 0
% 0.19/0.45  #    Negative unit clauses             : 5
% 0.19/0.45  #    Non-unit-clauses                  : 314
% 0.19/0.45  # Current number of unprocessed clauses: 163
% 0.19/0.45  # ...number of literals in the above   : 1460
% 0.19/0.45  # Current number of archived formulas  : 0
% 0.19/0.45  # Current number of archived clauses   : 79
% 0.19/0.45  # Clause-clause subsumption calls (NU) : 46604
% 0.19/0.45  # Rec. Clause-clause subsumption calls : 7724
% 0.19/0.45  # Non-unit clause-clause subsumptions  : 29
% 0.19/0.45  # Unit Clause-clause subsumption calls : 5760
% 0.19/0.45  # Rewrite failures with RHS unbound    : 0
% 0.19/0.45  # BW rewrite match attempts            : 191
% 0.19/0.45  # BW rewrite match successes           : 34
% 0.19/0.45  # Condensation attempts                : 0
% 0.19/0.45  # Condensation successes               : 0
% 0.19/0.45  # Termbank termtop insertions          : 51507
% 0.19/0.45  
% 0.19/0.45  # -------------------------------------------------
% 0.19/0.45  # User time                : 0.111 s
% 0.19/0.45  # System time              : 0.011 s
% 0.19/0.45  # Total time               : 0.122 s
% 0.19/0.45  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
