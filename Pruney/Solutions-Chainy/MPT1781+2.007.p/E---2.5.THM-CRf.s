%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:09 EST 2020

% Result     : Theorem 0.54s
% Output     : CNFRefutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  135 (30940 expanded)
%              Number of clauses        :  104 (9976 expanded)
%              Number of leaves         :   15 (7650 expanded)
%              Depth                    :   29
%              Number of atoms          :  860 (251413 expanded)
%              Number of equality atoms :   77 (19035 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal clause size      :   48 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t96_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
             => ( ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_hidden(X4,u1_struct_0(X2))
                     => X4 = k1_funct_1(X3,X4) ) )
               => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k4_tmap_1(X1,X2),X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_tmap_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(d5_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ! [X4] :
                  ( m1_pre_topc(X4,X1)
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                     => ( m1_pre_topc(X4,X3)
                       => k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

fof(t7_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X2)
             => m1_pre_topc(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

fof(d4_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( m1_pre_topc(X4,X1)
                 => k2_tmap_1(X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(dt_k3_tmap_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & v2_pre_topc(X2)
        & l1_pre_topc(X2)
        & m1_pre_topc(X3,X1)
        & m1_pre_topc(X4,X1)
        & v1_funct_1(X5)
        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
     => ( v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))
        & v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))
        & m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).

fof(dt_k4_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_funct_1(k4_tmap_1(X1,X2))
        & v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
        & m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_tmap_1)).

fof(t59_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X2) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) )
                     => ( ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X2))
                           => ( r2_hidden(X6,u1_struct_0(X3))
                             => k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) ) )
                       => r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_tmap_1)).

fof(d9_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( r2_funct_2(X1,X2,X3,X4)
          <=> ! [X5] :
                ( m1_subset_1(X5,X1)
               => k1_funct_1(X3,X5) = k1_funct_1(X4,X5) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_2)).

fof(t74_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                 => r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),X4,k3_tmap_1(X1,X2,X3,X3,X4)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tmap_1)).

fof(t55_pre_topc,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

fof(t95_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(X3,u1_struct_0(X2))
               => k1_funct_1(k4_tmap_1(X1,X2),X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_tmap_1)).

fof(t72_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                     => ( m1_pre_topc(X3,X4)
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X4))
                           => ( r2_hidden(X6,u1_struct_0(X3))
                             => k3_funct_2(u1_struct_0(X4),u1_struct_0(X2),X5,X6) = k1_funct_1(k3_tmap_1(X1,X2,X4,X3,X5),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_tmap_1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_hidden(X4,u1_struct_0(X2))
                       => X4 = k1_funct_1(X3,X4) ) )
                 => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k4_tmap_1(X1,X2),X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t96_tmap_1])).

fof(c_0_16,plain,(
    ! [X15,X16] :
      ( ~ l1_pre_topc(X15)
      | ~ m1_pre_topc(X16,X15)
      | l1_pre_topc(X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_17,negated_conjecture,(
    ! [X62] :
      ( ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & ~ v2_struct_0(esk4_0)
      & m1_pre_topc(esk4_0,esk3_0)
      & v1_funct_1(esk5_0)
      & v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0))
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))
      & ( ~ m1_subset_1(X62,u1_struct_0(esk3_0))
        | ~ r2_hidden(X62,u1_struct_0(esk4_0))
        | X62 = k1_funct_1(esk5_0,X62) )
      & ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),esk5_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])).

fof(c_0_18,plain,(
    ! [X13,X14] :
      ( ~ v2_pre_topc(X13)
      | ~ l1_pre_topc(X13)
      | ~ m1_pre_topc(X14,X13)
      | v2_pre_topc(X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

fof(c_0_19,plain,(
    ! [X24,X25,X26,X27,X28] :
      ( v2_struct_0(X24)
      | ~ v2_pre_topc(X24)
      | ~ l1_pre_topc(X24)
      | v2_struct_0(X25)
      | ~ v2_pre_topc(X25)
      | ~ l1_pre_topc(X25)
      | ~ m1_pre_topc(X26,X24)
      | ~ m1_pre_topc(X27,X24)
      | ~ v1_funct_1(X28)
      | ~ v1_funct_2(X28,u1_struct_0(X26),u1_struct_0(X25))
      | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X25))))
      | ~ m1_pre_topc(X27,X26)
      | k3_tmap_1(X24,X25,X26,X27,X28) = k2_partfun1(u1_struct_0(X26),u1_struct_0(X25),X28,u1_struct_0(X27)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).

fof(c_0_20,plain,(
    ! [X53,X54,X55] :
      ( ~ v2_pre_topc(X53)
      | ~ l1_pre_topc(X53)
      | ~ m1_pre_topc(X54,X53)
      | ~ m1_pre_topc(X55,X54)
      | m1_pre_topc(X55,X53) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

fof(c_0_21,plain,(
    ! [X20,X21,X22,X23] :
      ( v2_struct_0(X20)
      | ~ v2_pre_topc(X20)
      | ~ l1_pre_topc(X20)
      | v2_struct_0(X21)
      | ~ v2_pre_topc(X21)
      | ~ l1_pre_topc(X21)
      | ~ v1_funct_1(X22)
      | ~ v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))
      | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21))))
      | ~ m1_pre_topc(X23,X20)
      | k2_tmap_1(X20,X21,X22,X23) = k2_partfun1(u1_struct_0(X20),u1_struct_0(X21),X22,u1_struct_0(X23)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_22,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_tmap_1(X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_31,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_32,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_23]),c_0_24]),c_0_26])])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_35,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_37,plain,(
    ! [X36] :
      ( ~ l1_pre_topc(X36)
      | m1_pre_topc(X36,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_38,plain,
    ( k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X5) ),
    inference(csr,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0,u1_struct_0(X1)) = k2_tmap_1(esk4_0,esk3_0,esk5_0,X1)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_24]),c_0_31]),c_0_26]),c_0_32]),c_0_33]),c_0_34])]),c_0_35]),c_0_36])).

cnf(c_0_40,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( k3_tmap_1(X1,esk3_0,esk4_0,X2,esk5_0) = k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk4_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_30]),c_0_24]),c_0_26]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0,u1_struct_0(esk4_0)) = k2_tmap_1(esk4_0,esk3_0,esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_31])])).

fof(c_0_43,plain,(
    ! [X29,X30,X31,X32,X33] :
      ( ( v1_funct_1(k3_tmap_1(X29,X30,X31,X32,X33))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30)
        | ~ m1_pre_topc(X31,X29)
        | ~ m1_pre_topc(X32,X29)
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,u1_struct_0(X31),u1_struct_0(X30))
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X30)))) )
      & ( v1_funct_2(k3_tmap_1(X29,X30,X31,X32,X33),u1_struct_0(X32),u1_struct_0(X30))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30)
        | ~ m1_pre_topc(X31,X29)
        | ~ m1_pre_topc(X32,X29)
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,u1_struct_0(X31),u1_struct_0(X30))
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X30)))) )
      & ( m1_subset_1(k3_tmap_1(X29,X30,X31,X32,X33),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X30))))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30)
        | ~ m1_pre_topc(X31,X29)
        | ~ m1_pre_topc(X32,X29)
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,u1_struct_0(X31),u1_struct_0(X30))
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X30)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_tmap_1])])])])).

fof(c_0_44,plain,(
    ! [X34,X35] :
      ( ( v1_funct_1(k4_tmap_1(X34,X35))
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34)
        | ~ m1_pre_topc(X35,X34) )
      & ( v1_funct_2(k4_tmap_1(X34,X35),u1_struct_0(X35),u1_struct_0(X34))
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34)
        | ~ m1_pre_topc(X35,X34) )
      & ( m1_subset_1(k4_tmap_1(X34,X35),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X35),u1_struct_0(X34))))
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34)
        | ~ m1_pre_topc(X35,X34) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_tmap_1])])])])).

cnf(c_0_45,negated_conjecture,
    ( k3_tmap_1(X1,esk3_0,esk4_0,esk4_0,esk5_0) = k2_tmap_1(esk4_0,esk3_0,esk5_0,esk4_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_40]),c_0_42]),c_0_31])])).

cnf(c_0_46,plain,
    ( m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_47,plain,(
    ! [X37,X38,X39,X40,X41] :
      ( ( m1_subset_1(esk2_5(X37,X38,X39,X40,X41),u1_struct_0(X38))
        | r2_funct_2(u1_struct_0(X39),u1_struct_0(X37),k2_tmap_1(X38,X37,X40,X39),X41)
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X37))
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X37))))
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,u1_struct_0(X38),u1_struct_0(X37))
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(X37))))
        | v2_struct_0(X39)
        | ~ m1_pre_topc(X39,X38)
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38)
        | v2_struct_0(X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) )
      & ( r2_hidden(esk2_5(X37,X38,X39,X40,X41),u1_struct_0(X39))
        | r2_funct_2(u1_struct_0(X39),u1_struct_0(X37),k2_tmap_1(X38,X37,X40,X39),X41)
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X37))
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X37))))
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,u1_struct_0(X38),u1_struct_0(X37))
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(X37))))
        | v2_struct_0(X39)
        | ~ m1_pre_topc(X39,X38)
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38)
        | v2_struct_0(X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) )
      & ( k3_funct_2(u1_struct_0(X38),u1_struct_0(X37),X40,esk2_5(X37,X38,X39,X40,X41)) != k1_funct_1(X41,esk2_5(X37,X38,X39,X40,X41))
        | r2_funct_2(u1_struct_0(X39),u1_struct_0(X37),k2_tmap_1(X38,X37,X40,X39),X41)
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X37))
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X37))))
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,u1_struct_0(X38),u1_struct_0(X37))
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(X37))))
        | v2_struct_0(X39)
        | ~ m1_pre_topc(X39,X38)
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38)
        | v2_struct_0(X37)
        | ~ v2_pre_topc(X37)
        | ~ l1_pre_topc(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t59_tmap_1])])])])])])).

cnf(c_0_48,plain,
    ( m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_49,plain,
    ( v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,plain,
    ( v1_funct_1(k4_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( k2_tmap_1(esk4_0,esk3_0,esk5_0,esk4_0) = k3_tmap_1(esk4_0,esk3_0,esk4_0,esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_40]),c_0_31]),c_0_32])]),c_0_36])).

cnf(c_0_52,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(k3_tmap_1(X1,esk3_0,esk4_0,X2,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk3_0))))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_30]),c_0_24]),c_0_26]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_53,plain,
    ( v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,plain,
    ( v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_55,plain,
    ( m1_subset_1(esk2_5(X1,X2,X3,X4,X5),u1_struct_0(X2))
    | r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(k4_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_23]),c_0_24]),c_0_26])]),c_0_35])).

cnf(c_0_57,negated_conjecture,
    ( v1_funct_2(k4_tmap_1(esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_23]),c_0_24]),c_0_26])]),c_0_35])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_1(k4_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_23]),c_0_24]),c_0_26])]),c_0_35])).

cnf(c_0_59,negated_conjecture,
    ( k3_tmap_1(X1,esk3_0,esk4_0,esk4_0,esk5_0) = k3_tmap_1(esk4_0,esk3_0,esk4_0,esk4_0,esk5_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(rw,[status(thm)],[c_0_45,c_0_51])).

fof(c_0_60,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r2_funct_2(X7,X8,X9,X10)
        | ~ m1_subset_1(X11,X7)
        | k1_funct_1(X9,X11) = k1_funct_1(X10,X11)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X7,X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,X7,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) )
      & ( m1_subset_1(esk1_4(X7,X8,X9,X10),X7)
        | r2_funct_2(X7,X8,X9,X10)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X7,X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,X7,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) )
      & ( k1_funct_1(X9,esk1_4(X7,X8,X9,X10)) != k1_funct_1(X10,esk1_4(X7,X8,X9,X10))
        | r2_funct_2(X7,X8,X9,X10)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X7,X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,X7,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_2])])])])])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,X1,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0))))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_23]),c_0_24]),c_0_26])]),c_0_35])).

cnf(c_0_62,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_1(k3_tmap_1(X1,esk3_0,esk4_0,X2,esk5_0))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_30]),c_0_24]),c_0_26]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_63,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_2(k3_tmap_1(X1,esk3_0,esk4_0,X2,esk5_0),u1_struct_0(X2),u1_struct_0(esk3_0))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_30]),c_0_24]),c_0_26]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_64,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(X1,esk3_0,X2,esk4_0),k4_tmap_1(esk3_0,esk4_0))
    | m1_subset_1(esk2_5(esk3_0,X1,esk4_0,X2,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(X1))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0))))
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_24]),c_0_26]),c_0_57]),c_0_58])]),c_0_36]),c_0_35])).

cnf(c_0_65,negated_conjecture,
    ( k3_tmap_1(esk4_0,esk3_0,esk4_0,esk4_0,esk5_0) = k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_23]),c_0_24]),c_0_26])]),c_0_35])).

cnf(c_0_66,plain,
    ( k1_funct_1(X3,X5) = k1_funct_1(X4,X5)
    | ~ r2_funct_2(X1,X2,X3,X4)
    | ~ m1_subset_1(X5,X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_23])).

cnf(c_0_68,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(esk4_0,esk3_0,esk4_0,X1,esk5_0))
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_40]),c_0_31]),c_0_32])]),c_0_36])).

cnf(c_0_69,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(esk4_0,esk3_0,esk4_0,X1,esk5_0),u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_40]),c_0_31]),c_0_32])]),c_0_36])).

fof(c_0_70,plain,(
    ! [X49,X50,X51,X52] :
      ( v2_struct_0(X49)
      | ~ v2_pre_topc(X49)
      | ~ l1_pre_topc(X49)
      | v2_struct_0(X50)
      | ~ v2_pre_topc(X50)
      | ~ l1_pre_topc(X50)
      | v2_struct_0(X51)
      | ~ m1_pre_topc(X51,X49)
      | ~ v1_funct_1(X52)
      | ~ v1_funct_2(X52,u1_struct_0(X51),u1_struct_0(X50))
      | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X51),u1_struct_0(X50))))
      | r2_funct_2(u1_struct_0(X51),u1_struct_0(X50),X52,k3_tmap_1(X49,X50,X51,X51,X52)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t74_tmap_1])])])])).

cnf(c_0_71,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),k4_tmap_1(esk3_0,esk4_0))
    | m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk4_0))
    | ~ m1_pre_topc(esk4_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_30]),c_0_51]),c_0_65]),c_0_31]),c_0_32]),c_0_33]),c_0_34])]),c_0_36])).

cnf(c_0_72,negated_conjecture,
    ( k1_funct_1(X1,X2) = k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),X2)
    | ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),X1,k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | ~ v1_funct_2(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))
    | ~ v1_funct_2(X1,u1_struct_0(esk4_0),u1_struct_0(esk3_0))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0))
    | ~ v1_funct_1(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0))
    | ~ m1_pre_topc(esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_65])).

cnf(c_0_74,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))
    | ~ m1_pre_topc(esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_65])).

cnf(c_0_75,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),X4,k3_tmap_1(X1,X2,X3,X3,X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_76,negated_conjecture,
    ( k1_funct_1(X1,X2) = k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X2)
    | ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),X1,k4_tmap_1(esk3_0,esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | ~ v1_funct_2(X1,u1_struct_0(esk4_0),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_56]),c_0_57]),c_0_58])])).

cnf(c_0_77,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),k4_tmap_1(esk3_0,esk4_0))
    | m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_40]),c_0_31])])).

cnf(c_0_78,negated_conjecture,
    ( k1_funct_1(X1,X2) = k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),X2)
    | ~ m1_pre_topc(esk4_0,esk4_0)
    | ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),X1,k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | ~ v1_funct_2(X1,u1_struct_0(esk4_0),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74])).

cnf(c_0_79,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0,k3_tmap_1(X1,esk3_0,esk4_0,esk4_0,esk5_0))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_30]),c_0_24]),c_0_26]),c_0_33]),c_0_34])]),c_0_36]),c_0_35])).

cnf(c_0_80,plain,
    ( m1_subset_1(esk1_4(X1,X2,X3,X4),X1)
    | r2_funct_2(X1,X2,X3,X4)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_81,negated_conjecture,
    ( k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),X1) = k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1)
    | m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ v1_funct_2(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_67])])).

cnf(c_0_82,negated_conjecture,
    ( k1_funct_1(X1,X2) = k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),X2)
    | ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),X1,k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | ~ v1_funct_2(X1,u1_struct_0(esk4_0),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_40]),c_0_31])])).

cnf(c_0_83,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0,k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_23]),c_0_24]),c_0_26])]),c_0_35])).

cnf(c_0_84,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),X1,esk5_0)
    | m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),X1,esk5_0),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))
    | ~ v1_funct_2(X1,u1_struct_0(esk4_0),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_30]),c_0_33]),c_0_34])])).

cnf(c_0_85,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_86,negated_conjecture,
    ( k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),X1) = k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1)
    | m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk4_0))
    | ~ m1_pre_topc(esk4_0,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_73]),c_0_74])).

cnf(c_0_87,negated_conjecture,
    ( k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),X1) = k1_funct_1(esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_30]),c_0_33]),c_0_34])])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_56]),c_0_57]),c_0_58])]),c_0_85])).

cnf(c_0_89,plain,
    ( r2_funct_2(X2,X3,X1,X4)
    | k1_funct_1(X1,esk1_4(X2,X3,X1,X4)) != k1_funct_1(X4,esk1_4(X2,X3,X1,X4))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_90,plain,
    ( r2_hidden(esk2_5(X1,X2,X3,X4,X5),u1_struct_0(X3))
    | r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_91,plain,(
    ! [X17,X18,X19] :
      ( v2_struct_0(X17)
      | ~ l1_pre_topc(X17)
      | v2_struct_0(X18)
      | ~ m1_pre_topc(X18,X17)
      | ~ m1_subset_1(X19,u1_struct_0(X18))
      | m1_subset_1(X19,u1_struct_0(X17)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).

cnf(c_0_92,negated_conjecture,
    ( k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),X1) = k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1)
    | m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_40]),c_0_31])])).

cnf(c_0_93,negated_conjecture,
    ( k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),esk5_0)) = k1_funct_1(esk5_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_94,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),esk5_0)) != k1_funct_1(esk5_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_89]),c_0_30]),c_0_56]),c_0_33]),c_0_57]),c_0_34]),c_0_58])])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(esk2_5(esk3_0,X1,esk4_0,X2,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk4_0))
    | v2_struct_0(X1)
    | r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(X1,esk3_0,X2,esk4_0),k4_tmap_1(esk3_0,esk4_0))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0))))
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_56]),c_0_24]),c_0_26]),c_0_57]),c_0_58])]),c_0_36]),c_0_35])).

cnf(c_0_96,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_97,negated_conjecture,
    ( m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_88]),c_0_93]),c_0_94])).

fof(c_0_98,plain,(
    ! [X56,X57,X58] :
      ( v2_struct_0(X56)
      | ~ v2_pre_topc(X56)
      | ~ l1_pre_topc(X56)
      | v2_struct_0(X57)
      | ~ m1_pre_topc(X57,X56)
      | ~ m1_subset_1(X58,u1_struct_0(X56))
      | ~ r2_hidden(X58,u1_struct_0(X57))
      | k1_funct_1(k4_tmap_1(X56,X57),X58) = X58 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t95_tmap_1])])])])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk4_0))
    | r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),k4_tmap_1(esk3_0,esk4_0))
    | ~ m1_pre_topc(esk4_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_30]),c_0_51]),c_0_65]),c_0_31]),c_0_32]),c_0_33]),c_0_34])]),c_0_36])).

cnf(c_0_100,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(X1))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_36])).

fof(c_0_101,plain,(
    ! [X43,X44,X45,X46,X47,X48] :
      ( v2_struct_0(X43)
      | ~ v2_pre_topc(X43)
      | ~ l1_pre_topc(X43)
      | v2_struct_0(X44)
      | ~ v2_pre_topc(X44)
      | ~ l1_pre_topc(X44)
      | v2_struct_0(X45)
      | ~ m1_pre_topc(X45,X43)
      | v2_struct_0(X46)
      | ~ m1_pre_topc(X46,X43)
      | ~ v1_funct_1(X47)
      | ~ v1_funct_2(X47,u1_struct_0(X46),u1_struct_0(X44))
      | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X44))))
      | ~ m1_pre_topc(X45,X46)
      | ~ m1_subset_1(X48,u1_struct_0(X46))
      | ~ r2_hidden(X48,u1_struct_0(X45))
      | k3_funct_2(u1_struct_0(X46),u1_struct_0(X44),X47,X48) = k1_funct_1(k3_tmap_1(X43,X44,X46,X45,X47),X48) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_tmap_1])])])])).

cnf(c_0_102,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k1_funct_1(k4_tmap_1(X1,X2),X3) = X3
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_103,negated_conjecture,
    ( r2_hidden(esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk4_0))
    | r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),k4_tmap_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_40]),c_0_31])])).

cnf(c_0_104,negated_conjecture,
    ( X1 = k1_funct_1(esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_105,negated_conjecture,
    ( m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_23]),c_0_24])]),c_0_35])).

cnf(c_0_106,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | k3_funct_2(u1_struct_0(X4),u1_struct_0(X2),X5,X6) = k1_funct_1(k3_tmap_1(X1,X2,X4,X3,X5),X6)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_subset_1(X6,u1_struct_0(X4))
    | ~ r2_hidden(X6,u1_struct_0(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_107,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(X1,esk4_0),esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))) = esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))
    | v2_struct_0(X1)
    | r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),k4_tmap_1(esk3_0,esk4_0))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_36]),c_0_100])).

cnf(c_0_108,negated_conjecture,
    ( k1_funct_1(esk5_0,esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))) = esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))
    | r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),k4_tmap_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_103]),c_0_105])])).

cnf(c_0_109,plain,
    ( k1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5),X6) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X2),X5,X6)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | ~ r2_hidden(X6,u1_struct_0(X4))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_subset_1(X6,u1_struct_0(X3))
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X5) ),
    inference(csr,[status(thm)],[c_0_106,c_0_28])).

cnf(c_0_110,plain,
    ( r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k2_tmap_1(X1,X2,X3,X4),X5)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,esk2_5(X2,X1,X4,X3,X5)) != k1_funct_1(X5,esk2_5(X2,X1,X4,X3,X5))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_111,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))) = esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))
    | r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),k4_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_23]),c_0_24]),c_0_26])]),c_0_35])).

cnf(c_0_112,negated_conjecture,
    ( k1_funct_1(esk5_0,esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))) = esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))
    | k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),X1) = k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ v1_funct_2(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_108]),c_0_67])])).

cnf(c_0_113,negated_conjecture,
    ( k1_funct_1(k3_tmap_1(X1,esk3_0,esk4_0,X2,esk5_0),X3) = k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X3,u1_struct_0(X2))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,esk4_0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_30]),c_0_24]),c_0_26]),c_0_33]),c_0_34])]),c_0_36]),c_0_35])).

cnf(c_0_114,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(X1,esk3_0,X2,esk4_0),k4_tmap_1(esk3_0,esk4_0))
    | k3_funct_2(u1_struct_0(X1),u1_struct_0(esk3_0),X2,esk2_5(esk3_0,X1,esk4_0,X2,k4_tmap_1(esk3_0,esk4_0))) != k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_5(esk3_0,X1,esk4_0,X2,k4_tmap_1(esk3_0,esk4_0)))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0))))
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_56]),c_0_24]),c_0_26]),c_0_57]),c_0_58])]),c_0_36]),c_0_35])).

cnf(c_0_115,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))) = esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))
    | k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),X1) = k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ v1_funct_2(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_111]),c_0_67])])).

cnf(c_0_116,negated_conjecture,
    ( k1_funct_1(esk5_0,esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))) = esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))
    | k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),X1) = k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1)
    | ~ m1_pre_topc(esk4_0,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_73]),c_0_74])).

cnf(c_0_117,negated_conjecture,
    ( k1_funct_1(k3_tmap_1(X1,esk3_0,esk4_0,X2,esk5_0),esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))) = k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0,esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(X2))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,esk4_0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_113,c_0_97])).

cnf(c_0_118,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),k4_tmap_1(esk3_0,esk4_0))
    | k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))) != k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0,esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)))
    | ~ m1_pre_topc(esk4_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_30]),c_0_51]),c_0_65]),c_0_31]),c_0_32]),c_0_33]),c_0_34])]),c_0_36])).

cnf(c_0_119,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))) = esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))
    | k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),X1) = k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1)
    | ~ m1_pre_topc(esk4_0,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_73]),c_0_74])).

cnf(c_0_120,negated_conjecture,
    ( k1_funct_1(esk5_0,esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))) = esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))
    | k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),X1) = k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_40]),c_0_31])])).

cnf(c_0_121,negated_conjecture,
    ( k1_funct_1(k3_tmap_1(X1,esk3_0,esk4_0,esk4_0,esk5_0),esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))) = k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0,esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)))
    | v2_struct_0(X1)
    | r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),k4_tmap_1(esk3_0,esk4_0))
    | ~ m1_pre_topc(esk4_0,esk4_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_103]),c_0_36])).

cnf(c_0_122,negated_conjecture,
    ( k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),X1) = k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1)
    | k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))) != k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0,esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)))
    | ~ m1_pre_topc(esk4_0,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_118]),c_0_67])]),c_0_73]),c_0_74])).

cnf(c_0_123,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))) = esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))
    | k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),X1) = k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_40]),c_0_31])])).

cnf(c_0_124,negated_conjecture,
    ( k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))) = k1_funct_1(esk5_0,esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_87,c_0_97])).

cnf(c_0_125,negated_conjecture,
    ( k1_funct_1(esk5_0,esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))) = esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_88]),c_0_93]),c_0_94])).

cnf(c_0_126,negated_conjecture,
    ( k1_funct_1(k3_tmap_1(X1,esk3_0,esk4_0,esk4_0,esk5_0),esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))) = k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0,esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)))
    | v2_struct_0(X1)
    | r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),k4_tmap_1(esk3_0,esk4_0))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_40]),c_0_31])])).

cnf(c_0_127,negated_conjecture,
    ( k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),X1) = k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1)
    | k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))) != k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0,esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_40]),c_0_31])])).

cnf(c_0_128,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))) = esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_97]),c_0_124]),c_0_125])])).

cnf(c_0_129,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0,esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))) = esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))
    | r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),k4_tmap_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_40]),c_0_65]),c_0_124]),c_0_125]),c_0_31]),c_0_32])]),c_0_36])).

cnf(c_0_130,negated_conjecture,
    ( k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),X1) = k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1)
    | k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0,esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))) != esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_127,c_0_128])).

cnf(c_0_131,negated_conjecture,
    ( k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),X1) = k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ v1_funct_2(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))
    | ~ v1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_129]),c_0_67])]),c_0_130])).

cnf(c_0_132,negated_conjecture,
    ( k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),X1) = k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1)
    | ~ m1_pre_topc(esk4_0,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_73]),c_0_74])).

cnf(c_0_133,negated_conjecture,
    ( k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),X1) = k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_40]),c_0_31])])).

cnf(c_0_134,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_88]),c_0_93]),c_0_94]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:16:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.54/0.69  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S059I
% 0.54/0.69  # and selection function SelectComplexExceptUniqMaxPosHorn.
% 0.54/0.69  #
% 0.54/0.69  # Preprocessing time       : 0.030 s
% 0.54/0.69  # Presaturation interreduction done
% 0.54/0.69  
% 0.54/0.69  # Proof found!
% 0.54/0.69  # SZS status Theorem
% 0.54/0.69  # SZS output start CNFRefutation
% 0.54/0.69  fof(t96_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,u1_struct_0(X2))=>X4=k1_funct_1(X3,X4)))=>r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k4_tmap_1(X1,X2),X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_tmap_1)).
% 0.54/0.69  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.54/0.69  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.54/0.69  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 0.54/0.69  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.54/0.69  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.54/0.69  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.54/0.69  fof(dt_k3_tmap_1, axiom, ![X1, X2, X3, X4, X5]:(((((((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v2_pre_topc(X2))&l1_pre_topc(X2))&m1_pre_topc(X3,X1))&m1_pre_topc(X4,X1))&v1_funct_1(X5))&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>((v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))&v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 0.54/0.69  fof(dt_k4_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_funct_1(k4_tmap_1(X1,X2))&v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_tmap_1)).
% 0.54/0.69  fof(t59_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))))=>(![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>(r2_hidden(X6,u1_struct_0(X3))=>k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X4,X6)=k1_funct_1(X5,X6)))=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_tmap_1)).
% 0.54/0.69  fof(d9_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>![X5]:(m1_subset_1(X5,X1)=>k1_funct_1(X3,X5)=k1_funct_1(X4,X5))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_2)).
% 0.54/0.69  fof(t74_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),X4,k3_tmap_1(X1,X2,X3,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tmap_1)).
% 0.54/0.69  fof(t55_pre_topc, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>m1_subset_1(X3,u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 0.54/0.69  fof(t95_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,u1_struct_0(X2))=>k1_funct_1(k4_tmap_1(X1,X2),X3)=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_tmap_1)).
% 0.54/0.69  fof(t72_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(m1_pre_topc(X3,X4)=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>(r2_hidden(X6,u1_struct_0(X3))=>k3_funct_2(u1_struct_0(X4),u1_struct_0(X2),X5,X6)=k1_funct_1(k3_tmap_1(X1,X2,X4,X3,X5),X6))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_tmap_1)).
% 0.54/0.69  fof(c_0_15, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,u1_struct_0(X2))=>X4=k1_funct_1(X3,X4)))=>r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k4_tmap_1(X1,X2),X3)))))), inference(assume_negation,[status(cth)],[t96_tmap_1])).
% 0.54/0.69  fof(c_0_16, plain, ![X15, X16]:(~l1_pre_topc(X15)|(~m1_pre_topc(X16,X15)|l1_pre_topc(X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.54/0.69  fof(c_0_17, negated_conjecture, ![X62]:(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk3_0))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))))&((~m1_subset_1(X62,u1_struct_0(esk3_0))|(~r2_hidden(X62,u1_struct_0(esk4_0))|X62=k1_funct_1(esk5_0,X62)))&~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),esk5_0))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])).
% 0.54/0.69  fof(c_0_18, plain, ![X13, X14]:(~v2_pre_topc(X13)|~l1_pre_topc(X13)|(~m1_pre_topc(X14,X13)|v2_pre_topc(X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.54/0.69  fof(c_0_19, plain, ![X24, X25, X26, X27, X28]:(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)|(~m1_pre_topc(X26,X24)|(~m1_pre_topc(X27,X24)|(~v1_funct_1(X28)|~v1_funct_2(X28,u1_struct_0(X26),u1_struct_0(X25))|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X25))))|(~m1_pre_topc(X27,X26)|k3_tmap_1(X24,X25,X26,X27,X28)=k2_partfun1(u1_struct_0(X26),u1_struct_0(X25),X28,u1_struct_0(X27)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 0.54/0.69  fof(c_0_20, plain, ![X53, X54, X55]:(~v2_pre_topc(X53)|~l1_pre_topc(X53)|(~m1_pre_topc(X54,X53)|(~m1_pre_topc(X55,X54)|m1_pre_topc(X55,X53)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.54/0.69  fof(c_0_21, plain, ![X20, X21, X22, X23]:(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)|(~v1_funct_1(X22)|~v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21))))|(~m1_pre_topc(X23,X20)|k2_tmap_1(X20,X21,X22,X23)=k2_partfun1(u1_struct_0(X20),u1_struct_0(X21),X22,u1_struct_0(X23)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.54/0.69  cnf(c_0_22, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.54/0.69  cnf(c_0_23, negated_conjecture, (m1_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.54/0.69  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.54/0.69  cnf(c_0_25, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.54/0.69  cnf(c_0_26, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.54/0.69  cnf(c_0_27, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.54/0.69  cnf(c_0_28, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.54/0.69  cnf(c_0_29, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.54/0.69  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.54/0.69  cnf(c_0_31, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.54/0.69  cnf(c_0_32, negated_conjecture, (v2_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_23]), c_0_24]), c_0_26])])).
% 0.54/0.69  cnf(c_0_33, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.54/0.69  cnf(c_0_34, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.54/0.69  cnf(c_0_35, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.54/0.69  cnf(c_0_36, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.54/0.69  fof(c_0_37, plain, ![X36]:(~l1_pre_topc(X36)|m1_pre_topc(X36,X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.54/0.69  cnf(c_0_38, plain, (k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X3,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X5)), inference(csr,[status(thm)],[c_0_27, c_0_28])).
% 0.54/0.69  cnf(c_0_39, negated_conjecture, (k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0,u1_struct_0(X1))=k2_tmap_1(esk4_0,esk3_0,esk5_0,X1)|~m1_pre_topc(X1,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_24]), c_0_31]), c_0_26]), c_0_32]), c_0_33]), c_0_34])]), c_0_35]), c_0_36])).
% 0.54/0.69  cnf(c_0_40, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.54/0.69  cnf(c_0_41, negated_conjecture, (k3_tmap_1(X1,esk3_0,esk4_0,X2,esk5_0)=k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0,u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,esk4_0)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_30]), c_0_24]), c_0_26]), c_0_33]), c_0_34])]), c_0_35])).
% 0.54/0.69  cnf(c_0_42, negated_conjecture, (k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0,u1_struct_0(esk4_0))=k2_tmap_1(esk4_0,esk3_0,esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_31])])).
% 0.54/0.69  fof(c_0_43, plain, ![X29, X30, X31, X32, X33]:(((v1_funct_1(k3_tmap_1(X29,X30,X31,X32,X33))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)|v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|~m1_pre_topc(X31,X29)|~m1_pre_topc(X32,X29)|~v1_funct_1(X33)|~v1_funct_2(X33,u1_struct_0(X31),u1_struct_0(X30))|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X30))))))&(v1_funct_2(k3_tmap_1(X29,X30,X31,X32,X33),u1_struct_0(X32),u1_struct_0(X30))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)|v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|~m1_pre_topc(X31,X29)|~m1_pre_topc(X32,X29)|~v1_funct_1(X33)|~v1_funct_2(X33,u1_struct_0(X31),u1_struct_0(X30))|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X30)))))))&(m1_subset_1(k3_tmap_1(X29,X30,X31,X32,X33),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X30))))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)|v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|~m1_pre_topc(X31,X29)|~m1_pre_topc(X32,X29)|~v1_funct_1(X33)|~v1_funct_2(X33,u1_struct_0(X31),u1_struct_0(X30))|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X30))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_tmap_1])])])])).
% 0.54/0.69  fof(c_0_44, plain, ![X34, X35]:(((v1_funct_1(k4_tmap_1(X34,X35))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)|~m1_pre_topc(X35,X34)))&(v1_funct_2(k4_tmap_1(X34,X35),u1_struct_0(X35),u1_struct_0(X34))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)|~m1_pre_topc(X35,X34))))&(m1_subset_1(k4_tmap_1(X34,X35),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X35),u1_struct_0(X34))))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)|~m1_pre_topc(X35,X34)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_tmap_1])])])])).
% 0.54/0.69  cnf(c_0_45, negated_conjecture, (k3_tmap_1(X1,esk3_0,esk4_0,esk4_0,esk5_0)=k2_tmap_1(esk4_0,esk3_0,esk5_0,esk4_0)|v2_struct_0(X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_40]), c_0_42]), c_0_31])])).
% 0.54/0.69  cnf(c_0_46, plain, (m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.54/0.69  fof(c_0_47, plain, ![X37, X38, X39, X40, X41]:((m1_subset_1(esk2_5(X37,X38,X39,X40,X41),u1_struct_0(X38))|r2_funct_2(u1_struct_0(X39),u1_struct_0(X37),k2_tmap_1(X38,X37,X40,X39),X41)|(~v1_funct_1(X41)|~v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X37))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X37)))))|(~v1_funct_1(X40)|~v1_funct_2(X40,u1_struct_0(X38),u1_struct_0(X37))|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(X37)))))|(v2_struct_0(X39)|~m1_pre_topc(X39,X38))|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)))&((r2_hidden(esk2_5(X37,X38,X39,X40,X41),u1_struct_0(X39))|r2_funct_2(u1_struct_0(X39),u1_struct_0(X37),k2_tmap_1(X38,X37,X40,X39),X41)|(~v1_funct_1(X41)|~v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X37))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X37)))))|(~v1_funct_1(X40)|~v1_funct_2(X40,u1_struct_0(X38),u1_struct_0(X37))|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(X37)))))|(v2_struct_0(X39)|~m1_pre_topc(X39,X38))|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)))&(k3_funct_2(u1_struct_0(X38),u1_struct_0(X37),X40,esk2_5(X37,X38,X39,X40,X41))!=k1_funct_1(X41,esk2_5(X37,X38,X39,X40,X41))|r2_funct_2(u1_struct_0(X39),u1_struct_0(X37),k2_tmap_1(X38,X37,X40,X39),X41)|(~v1_funct_1(X41)|~v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X37))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X37)))))|(~v1_funct_1(X40)|~v1_funct_2(X40,u1_struct_0(X38),u1_struct_0(X37))|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(X37)))))|(v2_struct_0(X39)|~m1_pre_topc(X39,X38))|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38))|(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t59_tmap_1])])])])])])).
% 0.54/0.69  cnf(c_0_48, plain, (m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.54/0.69  cnf(c_0_49, plain, (v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.54/0.69  cnf(c_0_50, plain, (v1_funct_1(k4_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.54/0.69  cnf(c_0_51, negated_conjecture, (k2_tmap_1(esk4_0,esk3_0,esk5_0,esk4_0)=k3_tmap_1(esk4_0,esk3_0,esk4_0,esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_40]), c_0_31]), c_0_32])]), c_0_36])).
% 0.54/0.69  cnf(c_0_52, negated_conjecture, (v2_struct_0(X1)|m1_subset_1(k3_tmap_1(X1,esk3_0,esk4_0,X2,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk3_0))))|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_30]), c_0_24]), c_0_26]), c_0_33]), c_0_34])]), c_0_35])).
% 0.54/0.69  cnf(c_0_53, plain, (v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.54/0.69  cnf(c_0_54, plain, (v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.54/0.69  cnf(c_0_55, plain, (m1_subset_1(esk2_5(X1,X2,X3,X4,X5),u1_struct_0(X2))|r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.54/0.69  cnf(c_0_56, negated_conjecture, (m1_subset_1(k4_tmap_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_23]), c_0_24]), c_0_26])]), c_0_35])).
% 0.54/0.69  cnf(c_0_57, negated_conjecture, (v1_funct_2(k4_tmap_1(esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_23]), c_0_24]), c_0_26])]), c_0_35])).
% 0.54/0.69  cnf(c_0_58, negated_conjecture, (v1_funct_1(k4_tmap_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_23]), c_0_24]), c_0_26])]), c_0_35])).
% 0.54/0.69  cnf(c_0_59, negated_conjecture, (k3_tmap_1(X1,esk3_0,esk4_0,esk4_0,esk5_0)=k3_tmap_1(esk4_0,esk3_0,esk4_0,esk4_0,esk5_0)|v2_struct_0(X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(rw,[status(thm)],[c_0_45, c_0_51])).
% 0.54/0.69  fof(c_0_60, plain, ![X7, X8, X9, X10, X11]:((~r2_funct_2(X7,X8,X9,X10)|(~m1_subset_1(X11,X7)|k1_funct_1(X9,X11)=k1_funct_1(X10,X11))|(~v1_funct_1(X10)|~v1_funct_2(X10,X7,X8)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8))))|(~v1_funct_1(X9)|~v1_funct_2(X9,X7,X8)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))))&((m1_subset_1(esk1_4(X7,X8,X9,X10),X7)|r2_funct_2(X7,X8,X9,X10)|(~v1_funct_1(X10)|~v1_funct_2(X10,X7,X8)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8))))|(~v1_funct_1(X9)|~v1_funct_2(X9,X7,X8)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))))&(k1_funct_1(X9,esk1_4(X7,X8,X9,X10))!=k1_funct_1(X10,esk1_4(X7,X8,X9,X10))|r2_funct_2(X7,X8,X9,X10)|(~v1_funct_1(X10)|~v1_funct_2(X10,X7,X8)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8))))|(~v1_funct_1(X9)|~v1_funct_2(X9,X7,X8)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_2])])])])])).
% 0.54/0.69  cnf(c_0_61, negated_conjecture, (m1_subset_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,X1,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0))))|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_23]), c_0_24]), c_0_26])]), c_0_35])).
% 0.54/0.69  cnf(c_0_62, negated_conjecture, (v2_struct_0(X1)|v1_funct_1(k3_tmap_1(X1,esk3_0,esk4_0,X2,esk5_0))|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_30]), c_0_24]), c_0_26]), c_0_33]), c_0_34])]), c_0_35])).
% 0.54/0.69  cnf(c_0_63, negated_conjecture, (v2_struct_0(X1)|v1_funct_2(k3_tmap_1(X1,esk3_0,esk4_0,X2,esk5_0),u1_struct_0(X2),u1_struct_0(esk3_0))|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_30]), c_0_24]), c_0_26]), c_0_33]), c_0_34])]), c_0_35])).
% 0.54/0.69  cnf(c_0_64, negated_conjecture, (v2_struct_0(X1)|r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(X1,esk3_0,X2,esk4_0),k4_tmap_1(esk3_0,esk4_0))|m1_subset_1(esk2_5(esk3_0,X1,esk4_0,X2,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(X1))|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0))))|~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk3_0))|~v1_funct_1(X2)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_24]), c_0_26]), c_0_57]), c_0_58])]), c_0_36]), c_0_35])).
% 0.54/0.69  cnf(c_0_65, negated_conjecture, (k3_tmap_1(esk4_0,esk3_0,esk4_0,esk4_0,esk5_0)=k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_23]), c_0_24]), c_0_26])]), c_0_35])).
% 0.54/0.69  cnf(c_0_66, plain, (k1_funct_1(X3,X5)=k1_funct_1(X4,X5)|~r2_funct_2(X1,X2,X3,X4)|~m1_subset_1(X5,X1)|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.54/0.69  cnf(c_0_67, negated_conjecture, (m1_subset_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))), inference(spm,[status(thm)],[c_0_61, c_0_23])).
% 0.54/0.69  cnf(c_0_68, negated_conjecture, (v1_funct_1(k3_tmap_1(esk4_0,esk3_0,esk4_0,X1,esk5_0))|~m1_pre_topc(X1,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_40]), c_0_31]), c_0_32])]), c_0_36])).
% 0.54/0.69  cnf(c_0_69, negated_conjecture, (v1_funct_2(k3_tmap_1(esk4_0,esk3_0,esk4_0,X1,esk5_0),u1_struct_0(X1),u1_struct_0(esk3_0))|~m1_pre_topc(X1,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_40]), c_0_31]), c_0_32])]), c_0_36])).
% 0.54/0.69  fof(c_0_70, plain, ![X49, X50, X51, X52]:(v2_struct_0(X49)|~v2_pre_topc(X49)|~l1_pre_topc(X49)|(v2_struct_0(X50)|~v2_pre_topc(X50)|~l1_pre_topc(X50)|(v2_struct_0(X51)|~m1_pre_topc(X51,X49)|(~v1_funct_1(X52)|~v1_funct_2(X52,u1_struct_0(X51),u1_struct_0(X50))|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X51),u1_struct_0(X50))))|r2_funct_2(u1_struct_0(X51),u1_struct_0(X50),X52,k3_tmap_1(X49,X50,X51,X51,X52)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t74_tmap_1])])])])).
% 0.54/0.69  cnf(c_0_71, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),k4_tmap_1(esk3_0,esk4_0))|m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk4_0))|~m1_pre_topc(esk4_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_30]), c_0_51]), c_0_65]), c_0_31]), c_0_32]), c_0_33]), c_0_34])]), c_0_36])).
% 0.54/0.69  cnf(c_0_72, negated_conjecture, (k1_funct_1(X1,X2)=k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),X2)|~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),X1,k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))|~m1_subset_1(X2,u1_struct_0(esk4_0))|~v1_funct_2(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))|~v1_funct_2(X1,u1_struct_0(esk4_0),u1_struct_0(esk3_0))|~v1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0))|~v1_funct_1(X1)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.54/0.69  cnf(c_0_73, negated_conjecture, (v1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0))|~m1_pre_topc(esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_68, c_0_65])).
% 0.54/0.69  cnf(c_0_74, negated_conjecture, (v1_funct_2(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))|~m1_pre_topc(esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_69, c_0_65])).
% 0.54/0.69  cnf(c_0_75, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),X4,k3_tmap_1(X1,X2,X3,X3,X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.54/0.69  cnf(c_0_76, negated_conjecture, (k1_funct_1(X1,X2)=k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X2)|~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),X1,k4_tmap_1(esk3_0,esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))|~m1_subset_1(X2,u1_struct_0(esk4_0))|~v1_funct_2(X1,u1_struct_0(esk4_0),u1_struct_0(esk3_0))|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_56]), c_0_57]), c_0_58])])).
% 0.54/0.69  cnf(c_0_77, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),k4_tmap_1(esk3_0,esk4_0))|m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_40]), c_0_31])])).
% 0.54/0.69  cnf(c_0_78, negated_conjecture, (k1_funct_1(X1,X2)=k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),X2)|~m1_pre_topc(esk4_0,esk4_0)|~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),X1,k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))|~m1_subset_1(X2,u1_struct_0(esk4_0))|~v1_funct_2(X1,u1_struct_0(esk4_0),u1_struct_0(esk3_0))|~v1_funct_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74])).
% 0.54/0.69  cnf(c_0_79, negated_conjecture, (v2_struct_0(X1)|r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0,k3_tmap_1(X1,esk3_0,esk4_0,esk4_0,esk5_0))|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_30]), c_0_24]), c_0_26]), c_0_33]), c_0_34])]), c_0_36]), c_0_35])).
% 0.54/0.69  cnf(c_0_80, plain, (m1_subset_1(esk1_4(X1,X2,X3,X4),X1)|r2_funct_2(X1,X2,X3,X4)|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.54/0.69  cnf(c_0_81, negated_conjecture, (k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),X1)=k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1)|m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))|~v1_funct_2(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))|~v1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_67])])).
% 0.54/0.69  cnf(c_0_82, negated_conjecture, (k1_funct_1(X1,X2)=k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),X2)|~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),X1,k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))|~m1_subset_1(X2,u1_struct_0(esk4_0))|~v1_funct_2(X1,u1_struct_0(esk4_0),u1_struct_0(esk3_0))|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_40]), c_0_31])])).
% 0.54/0.69  cnf(c_0_83, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0,k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_23]), c_0_24]), c_0_26])]), c_0_35])).
% 0.54/0.69  cnf(c_0_84, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),X1,esk5_0)|m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),X1,esk5_0),u1_struct_0(esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))|~v1_funct_2(X1,u1_struct_0(esk4_0),u1_struct_0(esk3_0))|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_30]), c_0_33]), c_0_34])])).
% 0.54/0.69  cnf(c_0_85, negated_conjecture, (~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.54/0.69  cnf(c_0_86, negated_conjecture, (k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),X1)=k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1)|m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk4_0))|~m1_pre_topc(esk4_0,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_73]), c_0_74])).
% 0.54/0.69  cnf(c_0_87, negated_conjecture, (k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),X1)=k1_funct_1(esk5_0,X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_30]), c_0_33]), c_0_34])])).
% 0.54/0.69  cnf(c_0_88, negated_conjecture, (m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),esk5_0),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_56]), c_0_57]), c_0_58])]), c_0_85])).
% 0.54/0.69  cnf(c_0_89, plain, (r2_funct_2(X2,X3,X1,X4)|k1_funct_1(X1,esk1_4(X2,X3,X1,X4))!=k1_funct_1(X4,esk1_4(X2,X3,X1,X4))|~v1_funct_1(X4)|~v1_funct_2(X4,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.54/0.69  cnf(c_0_90, plain, (r2_hidden(esk2_5(X1,X2,X3,X4,X5),u1_struct_0(X3))|r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.54/0.69  fof(c_0_91, plain, ![X17, X18, X19]:(v2_struct_0(X17)|~l1_pre_topc(X17)|(v2_struct_0(X18)|~m1_pre_topc(X18,X17)|(~m1_subset_1(X19,u1_struct_0(X18))|m1_subset_1(X19,u1_struct_0(X17))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).
% 0.54/0.69  cnf(c_0_92, negated_conjecture, (k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),X1)=k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1)|m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_40]), c_0_31])])).
% 0.54/0.69  cnf(c_0_93, negated_conjecture, (k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),esk5_0))=k1_funct_1(esk5_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),esk5_0))), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.54/0.69  cnf(c_0_94, negated_conjecture, (k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),esk5_0))!=k1_funct_1(esk5_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k4_tmap_1(esk3_0,esk4_0),esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_89]), c_0_30]), c_0_56]), c_0_33]), c_0_57]), c_0_34]), c_0_58])])).
% 0.54/0.69  cnf(c_0_95, negated_conjecture, (r2_hidden(esk2_5(esk3_0,X1,esk4_0,X2,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk4_0))|v2_struct_0(X1)|r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(X1,esk3_0,X2,esk4_0),k4_tmap_1(esk3_0,esk4_0))|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0))))|~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk3_0))|~v1_funct_1(X2)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_56]), c_0_24]), c_0_26]), c_0_57]), c_0_58])]), c_0_36]), c_0_35])).
% 0.54/0.69  cnf(c_0_96, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(X3,u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_91])).
% 0.54/0.69  cnf(c_0_97, negated_conjecture, (m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_88]), c_0_93]), c_0_94])).
% 0.54/0.69  fof(c_0_98, plain, ![X56, X57, X58]:(v2_struct_0(X56)|~v2_pre_topc(X56)|~l1_pre_topc(X56)|(v2_struct_0(X57)|~m1_pre_topc(X57,X56)|(~m1_subset_1(X58,u1_struct_0(X56))|(~r2_hidden(X58,u1_struct_0(X57))|k1_funct_1(k4_tmap_1(X56,X57),X58)=X58)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t95_tmap_1])])])])).
% 0.54/0.69  cnf(c_0_99, negated_conjecture, (r2_hidden(esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk4_0))|r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),k4_tmap_1(esk3_0,esk4_0))|~m1_pre_topc(esk4_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_30]), c_0_51]), c_0_65]), c_0_31]), c_0_32]), c_0_33]), c_0_34])]), c_0_36])).
% 0.54/0.69  cnf(c_0_100, negated_conjecture, (v2_struct_0(X1)|m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(X1))|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_36])).
% 0.54/0.69  fof(c_0_101, plain, ![X43, X44, X45, X46, X47, X48]:(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43)|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44)|(v2_struct_0(X45)|~m1_pre_topc(X45,X43)|(v2_struct_0(X46)|~m1_pre_topc(X46,X43)|(~v1_funct_1(X47)|~v1_funct_2(X47,u1_struct_0(X46),u1_struct_0(X44))|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X44))))|(~m1_pre_topc(X45,X46)|(~m1_subset_1(X48,u1_struct_0(X46))|(~r2_hidden(X48,u1_struct_0(X45))|k3_funct_2(u1_struct_0(X46),u1_struct_0(X44),X47,X48)=k1_funct_1(k3_tmap_1(X43,X44,X46,X45,X47),X48))))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_tmap_1])])])])).
% 0.54/0.69  cnf(c_0_102, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k1_funct_1(k4_tmap_1(X1,X2),X3)=X3|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_98])).
% 0.54/0.69  cnf(c_0_103, negated_conjecture, (r2_hidden(esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk4_0))|r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),k4_tmap_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_40]), c_0_31])])).
% 0.54/0.69  cnf(c_0_104, negated_conjecture, (X1=k1_funct_1(esk5_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.54/0.69  cnf(c_0_105, negated_conjecture, (m1_subset_1(esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_23]), c_0_24])]), c_0_35])).
% 0.54/0.69  cnf(c_0_106, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|k3_funct_2(u1_struct_0(X4),u1_struct_0(X2),X5,X6)=k1_funct_1(k3_tmap_1(X1,X2,X4,X3,X5),X6)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~m1_pre_topc(X3,X4)|~m1_subset_1(X6,u1_struct_0(X4))|~r2_hidden(X6,u1_struct_0(X3))), inference(split_conjunct,[status(thm)],[c_0_101])).
% 0.54/0.69  cnf(c_0_107, negated_conjecture, (k1_funct_1(k4_tmap_1(X1,esk4_0),esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)))=esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))|v2_struct_0(X1)|r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),k4_tmap_1(esk3_0,esk4_0))|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_36]), c_0_100])).
% 0.54/0.69  cnf(c_0_108, negated_conjecture, (k1_funct_1(esk5_0,esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)))=esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))|r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),k4_tmap_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_103]), c_0_105])])).
% 0.54/0.69  cnf(c_0_109, plain, (k1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5),X6)=k3_funct_2(u1_struct_0(X3),u1_struct_0(X2),X5,X6)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X4)|v2_struct_0(X3)|~r2_hidden(X6,u1_struct_0(X4))|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X3)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_subset_1(X6,u1_struct_0(X3))|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X5)), inference(csr,[status(thm)],[c_0_106, c_0_28])).
% 0.54/0.69  cnf(c_0_110, plain, (r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k2_tmap_1(X1,X2,X3,X4),X5)|v2_struct_0(X4)|v2_struct_0(X1)|v2_struct_0(X2)|k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,esk2_5(X2,X1,X4,X3,X5))!=k1_funct_1(X5,esk2_5(X2,X1,X4,X3,X5))|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.54/0.69  cnf(c_0_111, negated_conjecture, (k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)))=esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))|r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),k4_tmap_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_23]), c_0_24]), c_0_26])]), c_0_35])).
% 0.54/0.69  cnf(c_0_112, negated_conjecture, (k1_funct_1(esk5_0,esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)))=esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))|k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),X1)=k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))|~v1_funct_2(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))|~v1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_108]), c_0_67])])).
% 0.54/0.69  cnf(c_0_113, negated_conjecture, (k1_funct_1(k3_tmap_1(X1,esk3_0,esk4_0,X2,esk5_0),X3)=k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0,X3)|v2_struct_0(X1)|v2_struct_0(X2)|~r2_hidden(X3,u1_struct_0(X2))|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,esk4_0)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X3,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_30]), c_0_24]), c_0_26]), c_0_33]), c_0_34])]), c_0_36]), c_0_35])).
% 0.54/0.69  cnf(c_0_114, negated_conjecture, (v2_struct_0(X1)|r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_tmap_1(X1,esk3_0,X2,esk4_0),k4_tmap_1(esk3_0,esk4_0))|k3_funct_2(u1_struct_0(X1),u1_struct_0(esk3_0),X2,esk2_5(esk3_0,X1,esk4_0,X2,k4_tmap_1(esk3_0,esk4_0)))!=k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_5(esk3_0,X1,esk4_0,X2,k4_tmap_1(esk3_0,esk4_0)))|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0))))|~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk3_0))|~v1_funct_1(X2)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_56]), c_0_24]), c_0_26]), c_0_57]), c_0_58])]), c_0_36]), c_0_35])).
% 0.54/0.69  cnf(c_0_115, negated_conjecture, (k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)))=esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))|k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),X1)=k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))|~v1_funct_2(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))|~v1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_111]), c_0_67])])).
% 0.54/0.69  cnf(c_0_116, negated_conjecture, (k1_funct_1(esk5_0,esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)))=esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))|k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),X1)=k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1)|~m1_pre_topc(esk4_0,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_73]), c_0_74])).
% 0.54/0.69  cnf(c_0_117, negated_conjecture, (k1_funct_1(k3_tmap_1(X1,esk3_0,esk4_0,X2,esk5_0),esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)))=k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0,esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)))|v2_struct_0(X2)|v2_struct_0(X1)|~r2_hidden(esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)),u1_struct_0(X2))|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,esk4_0)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_113, c_0_97])).
% 0.54/0.69  cnf(c_0_118, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),k4_tmap_1(esk3_0,esk4_0))|k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)))!=k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0,esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)))|~m1_pre_topc(esk4_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_30]), c_0_51]), c_0_65]), c_0_31]), c_0_32]), c_0_33]), c_0_34])]), c_0_36])).
% 0.54/0.69  cnf(c_0_119, negated_conjecture, (k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)))=esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))|k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),X1)=k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1)|~m1_pre_topc(esk4_0,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_73]), c_0_74])).
% 0.54/0.69  cnf(c_0_120, negated_conjecture, (k1_funct_1(esk5_0,esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)))=esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))|k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),X1)=k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_40]), c_0_31])])).
% 0.54/0.69  cnf(c_0_121, negated_conjecture, (k1_funct_1(k3_tmap_1(X1,esk3_0,esk4_0,esk4_0,esk5_0),esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)))=k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0,esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)))|v2_struct_0(X1)|r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),k4_tmap_1(esk3_0,esk4_0))|~m1_pre_topc(esk4_0,esk4_0)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_103]), c_0_36])).
% 0.54/0.69  cnf(c_0_122, negated_conjecture, (k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),X1)=k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1)|k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)))!=k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0,esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)))|~m1_pre_topc(esk4_0,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_118]), c_0_67])]), c_0_73]), c_0_74])).
% 0.54/0.69  cnf(c_0_123, negated_conjecture, (k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)))=esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))|k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),X1)=k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_40]), c_0_31])])).
% 0.54/0.69  cnf(c_0_124, negated_conjecture, (k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)))=k1_funct_1(esk5_0,esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_87, c_0_97])).
% 0.54/0.69  cnf(c_0_125, negated_conjecture, (k1_funct_1(esk5_0,esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)))=esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_88]), c_0_93]), c_0_94])).
% 0.54/0.69  cnf(c_0_126, negated_conjecture, (k1_funct_1(k3_tmap_1(X1,esk3_0,esk4_0,esk4_0,esk5_0),esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)))=k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0,esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)))|v2_struct_0(X1)|r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),k4_tmap_1(esk3_0,esk4_0))|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_40]), c_0_31])])).
% 0.54/0.69  cnf(c_0_127, negated_conjecture, (k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),X1)=k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1)|k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)))!=k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0,esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_40]), c_0_31])])).
% 0.54/0.69  cnf(c_0_128, negated_conjecture, (k1_funct_1(k4_tmap_1(esk3_0,esk4_0),esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)))=esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_97]), c_0_124]), c_0_125])])).
% 0.54/0.69  cnf(c_0_129, negated_conjecture, (k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0,esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)))=esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))|r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),k4_tmap_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_40]), c_0_65]), c_0_124]), c_0_125]), c_0_31]), c_0_32])]), c_0_36])).
% 0.54/0.69  cnf(c_0_130, negated_conjecture, (k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),X1)=k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1)|k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk5_0,esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0)))!=esk2_5(esk3_0,esk4_0,esk4_0,esk5_0,k4_tmap_1(esk3_0,esk4_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(rw,[status(thm)],[c_0_127, c_0_128])).
% 0.54/0.69  cnf(c_0_131, negated_conjecture, (k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),X1)=k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))|~v1_funct_2(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))|~v1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_129]), c_0_67])]), c_0_130])).
% 0.54/0.69  cnf(c_0_132, negated_conjecture, (k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),X1)=k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1)|~m1_pre_topc(esk4_0,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_73]), c_0_74])).
% 0.54/0.69  cnf(c_0_133, negated_conjecture, (k1_funct_1(k3_tmap_1(esk3_0,esk3_0,esk4_0,esk4_0,esk5_0),X1)=k1_funct_1(k4_tmap_1(esk3_0,esk4_0),X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_40]), c_0_31])])).
% 0.54/0.69  cnf(c_0_134, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133, c_0_88]), c_0_93]), c_0_94]), ['proof']).
% 0.54/0.69  # SZS output end CNFRefutation
% 0.54/0.69  # Proof object total steps             : 135
% 0.54/0.69  # Proof object clause steps            : 104
% 0.54/0.69  # Proof object formula steps           : 31
% 0.54/0.69  # Proof object conjectures             : 83
% 0.54/0.69  # Proof object clause conjectures      : 80
% 0.54/0.69  # Proof object formula conjectures     : 3
% 0.54/0.69  # Proof object initial clauses used    : 32
% 0.54/0.69  # Proof object initial formulas used   : 15
% 0.54/0.69  # Proof object generating inferences   : 68
% 0.54/0.69  # Proof object simplifying inferences  : 228
% 0.54/0.69  # Training examples: 0 positive, 0 negative
% 0.54/0.69  # Parsed axioms                        : 15
% 0.54/0.69  # Removed by relevancy pruning/SinE    : 0
% 0.54/0.69  # Initial clauses                      : 32
% 0.54/0.69  # Removed in clause preprocessing      : 0
% 0.54/0.69  # Initial clauses in saturation        : 32
% 0.54/0.69  # Processed clauses                    : 1319
% 0.54/0.69  # ...of these trivial                  : 2
% 0.54/0.69  # ...subsumed                          : 83
% 0.54/0.69  # ...remaining for further processing  : 1234
% 0.54/0.69  # Other redundant clauses eliminated   : 0
% 0.54/0.69  # Clauses deleted for lack of memory   : 0
% 0.54/0.69  # Backward-subsumed                    : 323
% 0.54/0.69  # Backward-rewritten                   : 192
% 0.54/0.69  # Generated clauses                    : 3217
% 0.54/0.69  # ...of the previous two non-trivial   : 3296
% 0.54/0.69  # Contextual simplify-reflections      : 153
% 0.54/0.69  # Paramodulations                      : 3217
% 0.54/0.69  # Factorizations                       : 0
% 0.54/0.69  # Equation resolutions                 : 0
% 0.54/0.69  # Propositional unsat checks           : 0
% 0.54/0.69  #    Propositional check models        : 0
% 0.54/0.69  #    Propositional check unsatisfiable : 0
% 0.54/0.69  #    Propositional clauses             : 0
% 0.54/0.69  #    Propositional clauses after purity: 0
% 0.54/0.69  #    Propositional unsat core size     : 0
% 0.54/0.69  #    Propositional preprocessing time  : 0.000
% 0.54/0.69  #    Propositional encoding time       : 0.000
% 0.54/0.69  #    Propositional solver time         : 0.000
% 0.54/0.69  #    Success case prop preproc time    : 0.000
% 0.54/0.69  #    Success case prop encoding time   : 0.000
% 0.54/0.69  #    Success case prop solver time     : 0.000
% 0.54/0.69  # Current number of processed clauses  : 687
% 0.54/0.69  #    Positive orientable unit clauses  : 143
% 0.54/0.69  #    Positive unorientable unit clauses: 0
% 0.54/0.69  #    Negative unit clauses             : 4
% 0.54/0.69  #    Non-unit-clauses                  : 540
% 0.54/0.69  # Current number of unprocessed clauses: 1852
% 0.54/0.69  # ...number of literals in the above   : 10510
% 0.54/0.69  # Current number of archived formulas  : 0
% 0.54/0.69  # Current number of archived clauses   : 547
% 0.54/0.69  # Clause-clause subsumption calls (NU) : 116091
% 0.54/0.69  # Rec. Clause-clause subsumption calls : 12769
% 0.54/0.69  # Non-unit clause-clause subsumptions  : 551
% 0.54/0.69  # Unit Clause-clause subsumption calls : 3960
% 0.54/0.69  # Rewrite failures with RHS unbound    : 0
% 0.54/0.69  # BW rewrite match attempts            : 1563
% 0.54/0.69  # BW rewrite match successes           : 51
% 0.54/0.69  # Condensation attempts                : 0
% 0.54/0.69  # Condensation successes               : 0
% 0.54/0.69  # Termbank termtop insertions          : 233977
% 0.54/0.70  
% 0.54/0.70  # -------------------------------------------------
% 0.54/0.70  # User time                : 0.340 s
% 0.54/0.70  # System time              : 0.008 s
% 0.54/0.70  # Total time               : 0.348 s
% 0.54/0.70  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
