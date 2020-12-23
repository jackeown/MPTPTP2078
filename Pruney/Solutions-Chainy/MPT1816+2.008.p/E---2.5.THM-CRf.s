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
% DateTime   : Thu Dec  3 11:18:33 EST 2020

% Result     : Theorem 9.00s
% Output     : CNFRefutation 9.00s
% Verified   : 
% Statistics : Number of formulae       :   91 (4278 expanded)
%              Number of clauses        :   76 (1249 expanded)
%              Number of leaves         :    6 (1042 expanded)
%              Depth                    :   17
%              Number of atoms          :  689 (142021 expanded)
%              Number of equality atoms :   18 (3070 expanded)
%              Maximal formula depth    :   49 (   7 average)
%              Maximal clause size      :   91 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t132_tmap_1,conjecture,(
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
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ! [X5] :
                      ( ( ~ v2_struct_0(X5)
                        & m1_pre_topc(X5,X1) )
                     => ( ( X1 = k1_tsep_1(X1,X4,X5)
                          & r4_tsep_1(X1,X4,X5) )
                       => ( ( v1_funct_1(X3)
                            & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                            & v5_pre_topc(X3,X1,X2)
                            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                        <=> ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
                            & v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
                            & v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
                            & m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
                            & v1_funct_1(k2_tmap_1(X1,X2,X3,X5))
                            & v1_funct_2(k2_tmap_1(X1,X2,X3,X5),u1_struct_0(X5),u1_struct_0(X2))
                            & v5_pre_topc(k2_tmap_1(X1,X2,X3,X5),X5,X2)
                            & m1_subset_1(k2_tmap_1(X1,X2,X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2)))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_tmap_1)).

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

fof(dt_k1_tsep_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X2,X1)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X3,X1) )
     => ( ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
        & v1_pre_topc(k1_tsep_1(X1,X2,X3))
        & m1_pre_topc(k1_tsep_1(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(t126_tmap_1,axiom,(
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
                 => ( r4_tsep_1(X1,X3,X4)
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) )
                       => ( ( v1_funct_1(X5)
                            & v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
                            & v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) )
                        <=> ( v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5))
                            & v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),u1_struct_0(X3),u1_struct_0(X2))
                            & v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),X3,X2)
                            & m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
                            & v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5))
                            & v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),u1_struct_0(X4),u1_struct_0(X2))
                            & v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),X4,X2)
                            & m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_tmap_1)).

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

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
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
                    ( ( ~ v2_struct_0(X4)
                      & m1_pre_topc(X4,X1) )
                   => ! [X5] :
                        ( ( ~ v2_struct_0(X5)
                          & m1_pre_topc(X5,X1) )
                       => ( ( X1 = k1_tsep_1(X1,X4,X5)
                            & r4_tsep_1(X1,X4,X5) )
                         => ( ( v1_funct_1(X3)
                              & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                              & v5_pre_topc(X3,X1,X2)
                              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                          <=> ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
                              & v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
                              & v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
                              & m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
                              & v1_funct_1(k2_tmap_1(X1,X2,X3,X5))
                              & v1_funct_2(k2_tmap_1(X1,X2,X3,X5),u1_struct_0(X5),u1_struct_0(X2))
                              & v5_pre_topc(k2_tmap_1(X1,X2,X3,X5),X5,X2)
                              & m1_subset_1(k2_tmap_1(X1,X2,X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2)))) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t132_tmap_1])).

fof(c_0_6,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( v2_struct_0(X10)
      | ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | v2_struct_0(X11)
      | ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | ~ m1_pre_topc(X12,X10)
      | ~ m1_pre_topc(X13,X10)
      | ~ v1_funct_1(X14)
      | ~ v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(X11))
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X11))))
      | ~ m1_pre_topc(X13,X12)
      | k3_tmap_1(X10,X11,X12,X13,X14) = k2_partfun1(u1_struct_0(X12),u1_struct_0(X11),X14,u1_struct_0(X13)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).

fof(c_0_7,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk1_0)
    & ~ v2_struct_0(esk5_0)
    & m1_pre_topc(esk5_0,esk1_0)
    & esk1_0 = k1_tsep_1(esk1_0,esk4_0,esk5_0)
    & r4_tsep_1(esk1_0,esk4_0,esk5_0)
    & ( ~ v1_funct_1(esk3_0)
      | ~ v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
      | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
      | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
      | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
      | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
      | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
      | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
      | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
      | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
      | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
      | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
      | v1_funct_1(esk3_0) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
      | v1_funct_1(esk3_0) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
      | v1_funct_1(esk3_0) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
      | v1_funct_1(esk3_0) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
      | v1_funct_1(esk3_0) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
      | v1_funct_1(esk3_0) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
      | v1_funct_1(esk3_0) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
      | v1_funct_1(esk3_0) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
      | v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
      | v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
      | v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
      | v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
      | v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
      | v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
      | v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
      | v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
      | v5_pre_topc(esk3_0,esk1_0,esk2_0) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
      | v5_pre_topc(esk3_0,esk1_0,esk2_0) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
      | v5_pre_topc(esk3_0,esk1_0,esk2_0) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
      | v5_pre_topc(esk3_0,esk1_0,esk2_0) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
      | v5_pre_topc(esk3_0,esk1_0,esk2_0) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
      | v5_pre_topc(esk3_0,esk1_0,esk2_0) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
      | v5_pre_topc(esk3_0,esk1_0,esk2_0) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
      | v5_pre_topc(esk3_0,esk1_0,esk2_0) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
      | m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
      | m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
      | m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
      | m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
      | m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
      | m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
      | m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
      | m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])])).

fof(c_0_8,plain,(
    ! [X15,X16,X17] :
      ( ( ~ v2_struct_0(k1_tsep_1(X15,X16,X17))
        | v2_struct_0(X15)
        | ~ l1_pre_topc(X15)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X15) )
      & ( v1_pre_topc(k1_tsep_1(X15,X16,X17))
        | v2_struct_0(X15)
        | ~ l1_pre_topc(X15)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X15) )
      & ( m1_pre_topc(k1_tsep_1(X15,X16,X17),X15)
        | v2_struct_0(X15)
        | ~ l1_pre_topc(X15)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).

fof(c_0_9,plain,(
    ! [X1,X5,X4,X3,X2] :
      ( epred1_5(X2,X3,X4,X5,X1)
    <=> ( ( v1_funct_1(X5)
          & v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
          & v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) )
      <=> ( v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5))
          & v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),u1_struct_0(X3),u1_struct_0(X2))
          & v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),X3,X2)
          & m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
          & v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5))
          & v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),u1_struct_0(X4),u1_struct_0(X2))
          & v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),X4,X2)
          & m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ) ),
    introduced(definition)).

cnf(c_0_10,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,plain,
    ( m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_22,axiom,(
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
                 => ( r4_tsep_1(X1,X3,X4)
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) )
                       => epred1_5(X2,X3,X4,X5,X1) ) ) ) ) ) ) ),
    inference(apply_def,[status(thm)],[t126_tmap_1,c_0_9])).

fof(c_0_23,plain,(
    ! [X1,X5,X4,X3,X2] :
      ( epred1_5(X2,X3,X4,X5,X1)
     => ( ( v1_funct_1(X5)
          & v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
          & v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) )
      <=> ( v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5))
          & v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),u1_struct_0(X3),u1_struct_0(X2))
          & v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),X3,X2)
          & m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
          & v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5))
          & v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),u1_struct_0(X4),u1_struct_0(X2))
          & v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),X4,X2)
          & m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ) ),
    inference(split_equiv,[status(thm)],[c_0_9])).

fof(c_0_24,plain,(
    ! [X6,X7,X8,X9] :
      ( v2_struct_0(X6)
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(X7)
      | ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
      | ~ m1_pre_topc(X9,X6)
      | k2_tmap_1(X6,X7,X8,X9) = k2_partfun1(u1_struct_0(X6),u1_struct_0(X7),X8,u1_struct_0(X9)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_25,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk1_0,X2,esk3_0) = k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,X1,esk5_0),esk1_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])]),c_0_20]),c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_28,negated_conjecture,
    ( esk1_0 = k1_tsep_1(esk1_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_30,plain,(
    ! [X18,X19,X20,X21,X22] :
      ( v2_struct_0(X18)
      | ~ v2_pre_topc(X18)
      | ~ l1_pre_topc(X18)
      | v2_struct_0(X19)
      | ~ v2_pre_topc(X19)
      | ~ l1_pre_topc(X19)
      | v2_struct_0(X20)
      | ~ m1_pre_topc(X20,X18)
      | v2_struct_0(X21)
      | ~ m1_pre_topc(X21,X18)
      | ~ r4_tsep_1(X18,X20,X21)
      | ~ v1_funct_1(X22)
      | ~ v1_funct_2(X22,u1_struct_0(k1_tsep_1(X18,X20,X21)),u1_struct_0(X19))
      | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X18,X20,X21)),u1_struct_0(X19))))
      | epred1_5(X19,X20,X21,X22,X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])).

fof(c_0_31,plain,(
    ! [X28,X29,X30,X31,X32] :
      ( ( v1_funct_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29))
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,u1_struct_0(k1_tsep_1(X28,X31,X30)),u1_struct_0(X32))
        | ~ v5_pre_topc(X29,k1_tsep_1(X28,X31,X30),X32)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X28,X31,X30)),u1_struct_0(X32))))
        | ~ epred1_5(X32,X31,X30,X29,X28) )
      & ( v1_funct_2(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29),u1_struct_0(X31),u1_struct_0(X32))
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,u1_struct_0(k1_tsep_1(X28,X31,X30)),u1_struct_0(X32))
        | ~ v5_pre_topc(X29,k1_tsep_1(X28,X31,X30),X32)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X28,X31,X30)),u1_struct_0(X32))))
        | ~ epred1_5(X32,X31,X30,X29,X28) )
      & ( v5_pre_topc(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29),X31,X32)
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,u1_struct_0(k1_tsep_1(X28,X31,X30)),u1_struct_0(X32))
        | ~ v5_pre_topc(X29,k1_tsep_1(X28,X31,X30),X32)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X28,X31,X30)),u1_struct_0(X32))))
        | ~ epred1_5(X32,X31,X30,X29,X28) )
      & ( m1_subset_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X32))))
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,u1_struct_0(k1_tsep_1(X28,X31,X30)),u1_struct_0(X32))
        | ~ v5_pre_topc(X29,k1_tsep_1(X28,X31,X30),X32)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X28,X31,X30)),u1_struct_0(X32))))
        | ~ epred1_5(X32,X31,X30,X29,X28) )
      & ( v1_funct_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29))
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,u1_struct_0(k1_tsep_1(X28,X31,X30)),u1_struct_0(X32))
        | ~ v5_pre_topc(X29,k1_tsep_1(X28,X31,X30),X32)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X28,X31,X30)),u1_struct_0(X32))))
        | ~ epred1_5(X32,X31,X30,X29,X28) )
      & ( v1_funct_2(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29),u1_struct_0(X30),u1_struct_0(X32))
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,u1_struct_0(k1_tsep_1(X28,X31,X30)),u1_struct_0(X32))
        | ~ v5_pre_topc(X29,k1_tsep_1(X28,X31,X30),X32)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X28,X31,X30)),u1_struct_0(X32))))
        | ~ epred1_5(X32,X31,X30,X29,X28) )
      & ( v5_pre_topc(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29),X30,X32)
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,u1_struct_0(k1_tsep_1(X28,X31,X30)),u1_struct_0(X32))
        | ~ v5_pre_topc(X29,k1_tsep_1(X28,X31,X30),X32)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X28,X31,X30)),u1_struct_0(X32))))
        | ~ epred1_5(X32,X31,X30,X29,X28) )
      & ( m1_subset_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X32))))
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,u1_struct_0(k1_tsep_1(X28,X31,X30)),u1_struct_0(X32))
        | ~ v5_pre_topc(X29,k1_tsep_1(X28,X31,X30),X32)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X28,X31,X30)),u1_struct_0(X32))))
        | ~ epred1_5(X32,X31,X30,X29,X28) )
      & ( v1_funct_1(X29)
        | ~ v1_funct_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29))
        | ~ v1_funct_2(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29),u1_struct_0(X31),u1_struct_0(X32))
        | ~ v5_pre_topc(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29),X31,X32)
        | ~ m1_subset_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X32))))
        | ~ v1_funct_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29))
        | ~ v1_funct_2(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29),u1_struct_0(X30),u1_struct_0(X32))
        | ~ v5_pre_topc(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29),X30,X32)
        | ~ m1_subset_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X32))))
        | ~ epred1_5(X32,X31,X30,X29,X28) )
      & ( v1_funct_2(X29,u1_struct_0(k1_tsep_1(X28,X31,X30)),u1_struct_0(X32))
        | ~ v1_funct_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29))
        | ~ v1_funct_2(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29),u1_struct_0(X31),u1_struct_0(X32))
        | ~ v5_pre_topc(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29),X31,X32)
        | ~ m1_subset_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X32))))
        | ~ v1_funct_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29))
        | ~ v1_funct_2(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29),u1_struct_0(X30),u1_struct_0(X32))
        | ~ v5_pre_topc(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29),X30,X32)
        | ~ m1_subset_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X32))))
        | ~ epred1_5(X32,X31,X30,X29,X28) )
      & ( v5_pre_topc(X29,k1_tsep_1(X28,X31,X30),X32)
        | ~ v1_funct_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29))
        | ~ v1_funct_2(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29),u1_struct_0(X31),u1_struct_0(X32))
        | ~ v5_pre_topc(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29),X31,X32)
        | ~ m1_subset_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X32))))
        | ~ v1_funct_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29))
        | ~ v1_funct_2(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29),u1_struct_0(X30),u1_struct_0(X32))
        | ~ v5_pre_topc(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29),X30,X32)
        | ~ m1_subset_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X32))))
        | ~ epred1_5(X32,X31,X30,X29,X28) )
      & ( m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X28,X31,X30)),u1_struct_0(X32))))
        | ~ v1_funct_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29))
        | ~ v1_funct_2(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29),u1_struct_0(X31),u1_struct_0(X32))
        | ~ v5_pre_topc(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29),X31,X32)
        | ~ m1_subset_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X32))))
        | ~ v1_funct_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29))
        | ~ v1_funct_2(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29),u1_struct_0(X30),u1_struct_0(X32))
        | ~ v5_pre_topc(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29),X30,X32)
        | ~ m1_subset_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X32))))
        | ~ epred1_5(X32,X31,X30,X29,X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

cnf(c_0_32,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_34,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk1_0,esk5_0,esk3_0) = k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(esk5_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_18])).

cnf(c_0_35,negated_conjecture,
    ( m1_pre_topc(esk1_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_36,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | epred1_5(X2,X3,X4,X5,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ r4_tsep_1(X1,X3,X4)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( r4_tsep_1(esk1_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_38,plain,
    ( v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),X4,X2)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
    | ~ v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))
    | ~ epred1_5(X2,X3,X4,X5,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(X1)) = k2_tmap_1(esk1_0,esk2_0,esk3_0,X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_19]),c_0_15]),c_0_33])]),c_0_16]),c_0_21])).

cnf(c_0_40,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(esk5_0)) = k3_tmap_1(esk1_0,esk2_0,esk1_0,esk5_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_18]),c_0_19]),c_0_33])]),c_0_21])).

cnf(c_0_41,negated_conjecture,
    ( epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_28]),c_0_37]),c_0_18]),c_0_27]),c_0_19]),c_0_33])]),c_0_20]),c_0_29]),c_0_21])).

cnf(c_0_42,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk1_0,esk4_0,esk3_0) = k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(esk4_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_27])).

cnf(c_0_43,negated_conjecture,
    ( ~ v1_funct_1(esk3_0)
    | ~ v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_44,negated_conjecture,
    ( v5_pre_topc(k3_tmap_1(esk1_0,X1,esk1_0,esk5_0,X2),esk5_0,X1)
    | ~ epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)
    | ~ v5_pre_topc(X2,esk1_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_28])).

cnf(c_0_45,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk1_0,esk5_0,esk3_0) = k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_18])])).

cnf(c_0_46,negated_conjecture,
    ( epred1_5(esk2_0,esk4_0,esk5_0,esk3_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_47,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_48,plain,
    ( v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),X3,X2)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
    | ~ v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))
    | ~ epred1_5(X2,X3,X4,X5,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_49,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(esk4_0)) = k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_35]),c_0_27]),c_0_19]),c_0_33])]),c_0_21])).

cnf(c_0_50,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_13]),c_0_12]),c_0_11])])).

cnf(c_0_51,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_11]),c_0_12]),c_0_13])]),c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( v5_pre_topc(k3_tmap_1(esk1_0,X1,esk1_0,esk4_0,X2),esk4_0,X1)
    | ~ epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)
    | ~ v5_pre_topc(X2,esk1_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_28])).

cnf(c_0_53,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk3_0) = k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_49]),c_0_27])])).

cnf(c_0_54,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_55,plain,
    ( v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
    | ~ v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))
    | ~ epred1_5(X2,X3,X4,X5,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_56,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51])])).

cnf(c_0_57,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_46]),c_0_11]),c_0_12]),c_0_13])]),c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(esk1_0,X1,esk1_0,esk5_0,X2))
    | ~ epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)
    | ~ v5_pre_topc(X2,esk1_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_28])).

cnf(c_0_59,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_60,plain,
    ( v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
    | ~ v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))
    | ~ epred1_5(X2,X3,X4,X5,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_61,negated_conjecture,
    ( ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57])])).

cnf(c_0_62,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_11]),c_0_45]),c_0_46]),c_0_12]),c_0_13])]),c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(esk1_0,X1,esk1_0,esk4_0,X2))
    | ~ epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)
    | ~ v5_pre_topc(X2,esk1_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2) ),
    inference(spm,[status(thm)],[c_0_60,c_0_28])).

cnf(c_0_64,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_65,plain,
    ( m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
    | ~ v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))
    | ~ epred1_5(X2,X3,X4,X5,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_66,negated_conjecture,
    ( ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62])])).

cnf(c_0_67,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_11]),c_0_53]),c_0_46]),c_0_12]),c_0_13])]),c_0_64])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(esk1_0,X1,esk1_0,esk5_0,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))
    | ~ epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)
    | ~ v5_pre_topc(X2,esk1_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2) ),
    inference(spm,[status(thm)],[c_0_65,c_0_28])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_70,plain,
    ( m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
    | ~ v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))
    | ~ epred1_5(X2,X3,X4,X5,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_71,negated_conjecture,
    ( ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67])])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_45]),c_0_46]),c_0_11]),c_0_12]),c_0_13])]),c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(esk1_0,X1,esk1_0,esk4_0,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1))))
    | ~ epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)
    | ~ v5_pre_topc(X2,esk1_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2) ),
    inference(spm,[status(thm)],[c_0_70,c_0_28])).

cnf(c_0_74,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_75,plain,
    ( v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),u1_struct_0(X4),u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
    | ~ v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))
    | ~ epred1_5(X2,X3,X4,X5,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_76,negated_conjecture,
    ( ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_72])])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_53]),c_0_46]),c_0_11]),c_0_12]),c_0_13])]),c_0_74])).

cnf(c_0_78,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(esk1_0,X1,esk1_0,esk5_0,X2),u1_struct_0(esk5_0),u1_struct_0(X1))
    | ~ epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)
    | ~ v5_pre_topc(X2,esk1_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2) ),
    inference(spm,[status(thm)],[c_0_75,c_0_28])).

cnf(c_0_79,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_80,plain,
    ( v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
    | ~ v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))
    | ~ epred1_5(X2,X3,X4,X5,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_81,negated_conjecture,
    ( ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_77])])).

cnf(c_0_82,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_11]),c_0_45]),c_0_46]),c_0_12]),c_0_13])]),c_0_79])).

cnf(c_0_83,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(esk1_0,X1,esk1_0,esk4_0,X2),u1_struct_0(esk4_0),u1_struct_0(X1))
    | ~ epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)
    | ~ v5_pre_topc(X2,esk1_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2) ),
    inference(spm,[status(thm)],[c_0_80,c_0_28])).

cnf(c_0_84,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_85,plain,
    ( v5_pre_topc(X1,k1_tsep_1(X2,X3,X4),X5)
    | ~ v1_funct_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1))
    | ~ v1_funct_2(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1),u1_struct_0(X3),u1_struct_0(X5))
    | ~ v5_pre_topc(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1),X3,X5)
    | ~ m1_subset_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X5))))
    | ~ v1_funct_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1))
    | ~ v1_funct_2(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1),u1_struct_0(X4),u1_struct_0(X5))
    | ~ v5_pre_topc(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1),X4,X5)
    | ~ m1_subset_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))
    | ~ epred1_5(X5,X3,X4,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_86,negated_conjecture,
    ( ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_82])])).

cnf(c_0_87,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_11]),c_0_53]),c_0_46]),c_0_12]),c_0_13])]),c_0_84])).

cnf(c_0_88,negated_conjecture,
    ( v5_pre_topc(X1,esk1_0,X2)
    | ~ epred1_5(X2,esk4_0,esk5_0,X1,esk1_0)
    | ~ v5_pre_topc(k3_tmap_1(esk1_0,X2,esk1_0,esk5_0,X1),esk5_0,X2)
    | ~ v5_pre_topc(k3_tmap_1(esk1_0,X2,esk1_0,esk4_0,X1),esk4_0,X2)
    | ~ m1_subset_1(k3_tmap_1(esk1_0,X2,esk1_0,esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X2))))
    | ~ m1_subset_1(k3_tmap_1(esk1_0,X2,esk1_0,esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X2))))
    | ~ v1_funct_2(k3_tmap_1(esk1_0,X2,esk1_0,esk5_0,X1),u1_struct_0(esk5_0),u1_struct_0(X2))
    | ~ v1_funct_2(k3_tmap_1(esk1_0,X2,esk1_0,esk4_0,X1),u1_struct_0(esk4_0),u1_struct_0(X2))
    | ~ v1_funct_1(k3_tmap_1(esk1_0,X2,esk1_0,esk5_0,X1))
    | ~ v1_funct_1(k3_tmap_1(esk1_0,X2,esk1_0,esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_28])).

cnf(c_0_89,negated_conjecture,
    ( ~ v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_87])])).

cnf(c_0_90,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_45]),c_0_46]),c_0_51]),c_0_53]),c_0_57]),c_0_72]),c_0_53]),c_0_77]),c_0_82]),c_0_53]),c_0_87]),c_0_62]),c_0_53]),c_0_67])]),c_0_89]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:48:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 9.00/9.22  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 9.00/9.22  # and selection function SelectComplexExceptUniqMaxHorn.
% 9.00/9.22  #
% 9.00/9.22  # Preprocessing time       : 0.018 s
% 9.00/9.22  # Presaturation interreduction done
% 9.00/9.22  
% 9.00/9.22  # Proof found!
% 9.00/9.22  # SZS status Theorem
% 9.00/9.22  # SZS output start CNFRefutation
% 9.00/9.22  fof(t132_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>((X1=k1_tsep_1(X1,X4,X5)&r4_tsep_1(X1,X4,X5))=>((((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&v5_pre_topc(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))<=>(((((((v1_funct_1(k2_tmap_1(X1,X2,X3,X4))&v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2))&m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))&v1_funct_1(k2_tmap_1(X1,X2,X3,X5)))&v1_funct_2(k2_tmap_1(X1,X2,X3,X5),u1_struct_0(X5),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X3,X5),X5,X2))&m1_subset_1(k2_tmap_1(X1,X2,X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_tmap_1)).
% 9.00/9.22  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 9.00/9.22  fof(dt_k1_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>((~(v2_struct_0(k1_tsep_1(X1,X2,X3)))&v1_pre_topc(k1_tsep_1(X1,X2,X3)))&m1_pre_topc(k1_tsep_1(X1,X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 9.00/9.22  fof(t126_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(r4_tsep_1(X1,X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))=>((((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))<=>(((((((v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5))&v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),u1_struct_0(X3),u1_struct_0(X2)))&v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),X3,X2))&m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))&v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5)))&v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),X4,X2))&m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_tmap_1)).
% 9.00/9.22  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 9.00/9.22  fof(c_0_5, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>((X1=k1_tsep_1(X1,X4,X5)&r4_tsep_1(X1,X4,X5))=>((((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&v5_pre_topc(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))<=>(((((((v1_funct_1(k2_tmap_1(X1,X2,X3,X4))&v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2))&m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))&v1_funct_1(k2_tmap_1(X1,X2,X3,X5)))&v1_funct_2(k2_tmap_1(X1,X2,X3,X5),u1_struct_0(X5),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X3,X5),X5,X2))&m1_subset_1(k2_tmap_1(X1,X2,X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2))))))))))))), inference(assume_negation,[status(cth)],[t132_tmap_1])).
% 9.00/9.22  fof(c_0_6, plain, ![X10, X11, X12, X13, X14]:(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10)|(v2_struct_0(X11)|~v2_pre_topc(X11)|~l1_pre_topc(X11)|(~m1_pre_topc(X12,X10)|(~m1_pre_topc(X13,X10)|(~v1_funct_1(X14)|~v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(X11))|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X11))))|(~m1_pre_topc(X13,X12)|k3_tmap_1(X10,X11,X12,X13,X14)=k2_partfun1(u1_struct_0(X12),u1_struct_0(X11),X14,u1_struct_0(X13)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 9.00/9.22  fof(c_0_7, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk1_0))&((esk1_0=k1_tsep_1(esk1_0,esk4_0,esk5_0)&r4_tsep_1(esk1_0,esk4_0,esk5_0))&((~v1_funct_1(esk3_0)|~v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))|(~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))))&(((((((((((v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|v1_funct_1(esk3_0))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|v1_funct_1(esk3_0)))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|v1_funct_1(esk3_0)))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|v1_funct_1(esk3_0)))&(v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))|v1_funct_1(esk3_0)))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|v1_funct_1(esk3_0)))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|v1_funct_1(esk3_0)))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))|v1_funct_1(esk3_0)))&((((((((v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))))&(v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&((((((((v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|v5_pre_topc(esk3_0,esk1_0,esk2_0))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|v5_pre_topc(esk3_0,esk1_0,esk2_0)))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|v5_pre_topc(esk3_0,esk1_0,esk2_0)))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|v5_pre_topc(esk3_0,esk1_0,esk2_0)))&(v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))|v5_pre_topc(esk3_0,esk1_0,esk2_0)))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|v5_pre_topc(esk3_0,esk1_0,esk2_0)))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|v5_pre_topc(esk3_0,esk1_0,esk2_0)))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))|v5_pre_topc(esk3_0,esk1_0,esk2_0))))&((((((((v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))))&(v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))))))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])])).
% 9.00/9.22  fof(c_0_8, plain, ![X15, X16, X17]:(((~v2_struct_0(k1_tsep_1(X15,X16,X17))|(v2_struct_0(X15)|~l1_pre_topc(X15)|v2_struct_0(X16)|~m1_pre_topc(X16,X15)|v2_struct_0(X17)|~m1_pre_topc(X17,X15)))&(v1_pre_topc(k1_tsep_1(X15,X16,X17))|(v2_struct_0(X15)|~l1_pre_topc(X15)|v2_struct_0(X16)|~m1_pre_topc(X16,X15)|v2_struct_0(X17)|~m1_pre_topc(X17,X15))))&(m1_pre_topc(k1_tsep_1(X15,X16,X17),X15)|(v2_struct_0(X15)|~l1_pre_topc(X15)|v2_struct_0(X16)|~m1_pre_topc(X16,X15)|v2_struct_0(X17)|~m1_pre_topc(X17,X15)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).
% 9.00/9.22  fof(c_0_9, plain, ![X1, X5, X4, X3, X2]:(epred1_5(X2,X3,X4,X5,X1)<=>((((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))<=>(((((((v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5))&v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),u1_struct_0(X3),u1_struct_0(X2)))&v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),X3,X2))&m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))&v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5)))&v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),X4,X2))&m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))))), introduced(definition)).
% 9.00/9.22  cnf(c_0_10, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 9.00/9.22  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 9.00/9.22  cnf(c_0_12, negated_conjecture, (v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 9.00/9.22  cnf(c_0_13, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 9.00/9.22  cnf(c_0_14, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 9.00/9.22  cnf(c_0_15, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 9.00/9.22  cnf(c_0_16, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 9.00/9.22  cnf(c_0_17, plain, (m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 9.00/9.22  cnf(c_0_18, negated_conjecture, (m1_pre_topc(esk5_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 9.00/9.22  cnf(c_0_19, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 9.00/9.22  cnf(c_0_20, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 9.00/9.22  cnf(c_0_21, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 9.00/9.22  fof(c_0_22, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(r4_tsep_1(X1,X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))=>epred1_5(X2,X3,X4,X5,X1))))))), inference(apply_def,[status(thm)],[t126_tmap_1, c_0_9])).
% 9.00/9.22  fof(c_0_23, plain, ![X1, X5, X4, X3, X2]:(epred1_5(X2,X3,X4,X5,X1)=>((((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))<=>(((((((v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5))&v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),u1_struct_0(X3),u1_struct_0(X2)))&v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),X3,X2))&m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))&v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5)))&v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),X4,X2))&m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))))), inference(split_equiv,[status(thm)],[c_0_9])).
% 9.00/9.22  fof(c_0_24, plain, ![X6, X7, X8, X9]:(v2_struct_0(X6)|~v2_pre_topc(X6)|~l1_pre_topc(X6)|(v2_struct_0(X7)|~v2_pre_topc(X7)|~l1_pre_topc(X7)|(~v1_funct_1(X8)|~v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))|(~m1_pre_topc(X9,X6)|k2_tmap_1(X6,X7,X8,X9)=k2_partfun1(u1_struct_0(X6),u1_struct_0(X7),X8,u1_struct_0(X9)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 9.00/9.22  cnf(c_0_25, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk1_0,X2,esk3_0)=k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(esk1_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12]), c_0_13]), c_0_14]), c_0_15])]), c_0_16])).
% 9.00/9.22  cnf(c_0_26, negated_conjecture, (m1_pre_topc(k1_tsep_1(esk1_0,X1,esk5_0),esk1_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])]), c_0_20]), c_0_21])).
% 9.00/9.22  cnf(c_0_27, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 9.00/9.22  cnf(c_0_28, negated_conjecture, (esk1_0=k1_tsep_1(esk1_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 9.00/9.22  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 9.00/9.22  fof(c_0_30, plain, ![X18, X19, X20, X21, X22]:(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)|(v2_struct_0(X20)|~m1_pre_topc(X20,X18)|(v2_struct_0(X21)|~m1_pre_topc(X21,X18)|(~r4_tsep_1(X18,X20,X21)|(~v1_funct_1(X22)|~v1_funct_2(X22,u1_struct_0(k1_tsep_1(X18,X20,X21)),u1_struct_0(X19))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X18,X20,X21)),u1_struct_0(X19))))|epred1_5(X19,X20,X21,X22,X18))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])).
% 9.00/9.22  fof(c_0_31, plain, ![X28, X29, X30, X31, X32]:(((((((((v1_funct_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29))|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(k1_tsep_1(X28,X31,X30)),u1_struct_0(X32))|~v5_pre_topc(X29,k1_tsep_1(X28,X31,X30),X32)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X28,X31,X30)),u1_struct_0(X32)))))|~epred1_5(X32,X31,X30,X29,X28))&(v1_funct_2(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29),u1_struct_0(X31),u1_struct_0(X32))|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(k1_tsep_1(X28,X31,X30)),u1_struct_0(X32))|~v5_pre_topc(X29,k1_tsep_1(X28,X31,X30),X32)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X28,X31,X30)),u1_struct_0(X32)))))|~epred1_5(X32,X31,X30,X29,X28)))&(v5_pre_topc(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29),X31,X32)|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(k1_tsep_1(X28,X31,X30)),u1_struct_0(X32))|~v5_pre_topc(X29,k1_tsep_1(X28,X31,X30),X32)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X28,X31,X30)),u1_struct_0(X32)))))|~epred1_5(X32,X31,X30,X29,X28)))&(m1_subset_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X32))))|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(k1_tsep_1(X28,X31,X30)),u1_struct_0(X32))|~v5_pre_topc(X29,k1_tsep_1(X28,X31,X30),X32)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X28,X31,X30)),u1_struct_0(X32)))))|~epred1_5(X32,X31,X30,X29,X28)))&(v1_funct_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29))|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(k1_tsep_1(X28,X31,X30)),u1_struct_0(X32))|~v5_pre_topc(X29,k1_tsep_1(X28,X31,X30),X32)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X28,X31,X30)),u1_struct_0(X32)))))|~epred1_5(X32,X31,X30,X29,X28)))&(v1_funct_2(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29),u1_struct_0(X30),u1_struct_0(X32))|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(k1_tsep_1(X28,X31,X30)),u1_struct_0(X32))|~v5_pre_topc(X29,k1_tsep_1(X28,X31,X30),X32)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X28,X31,X30)),u1_struct_0(X32)))))|~epred1_5(X32,X31,X30,X29,X28)))&(v5_pre_topc(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29),X30,X32)|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(k1_tsep_1(X28,X31,X30)),u1_struct_0(X32))|~v5_pre_topc(X29,k1_tsep_1(X28,X31,X30),X32)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X28,X31,X30)),u1_struct_0(X32)))))|~epred1_5(X32,X31,X30,X29,X28)))&(m1_subset_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X32))))|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(k1_tsep_1(X28,X31,X30)),u1_struct_0(X32))|~v5_pre_topc(X29,k1_tsep_1(X28,X31,X30),X32)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X28,X31,X30)),u1_struct_0(X32)))))|~epred1_5(X32,X31,X30,X29,X28)))&((((v1_funct_1(X29)|(~v1_funct_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29))|~v1_funct_2(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29),u1_struct_0(X31),u1_struct_0(X32))|~v5_pre_topc(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29),X31,X32)|~m1_subset_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X32))))|~v1_funct_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29))|~v1_funct_2(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29),u1_struct_0(X30),u1_struct_0(X32))|~v5_pre_topc(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29),X30,X32)|~m1_subset_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X32)))))|~epred1_5(X32,X31,X30,X29,X28))&(v1_funct_2(X29,u1_struct_0(k1_tsep_1(X28,X31,X30)),u1_struct_0(X32))|(~v1_funct_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29))|~v1_funct_2(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29),u1_struct_0(X31),u1_struct_0(X32))|~v5_pre_topc(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29),X31,X32)|~m1_subset_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X32))))|~v1_funct_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29))|~v1_funct_2(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29),u1_struct_0(X30),u1_struct_0(X32))|~v5_pre_topc(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29),X30,X32)|~m1_subset_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X32)))))|~epred1_5(X32,X31,X30,X29,X28)))&(v5_pre_topc(X29,k1_tsep_1(X28,X31,X30),X32)|(~v1_funct_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29))|~v1_funct_2(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29),u1_struct_0(X31),u1_struct_0(X32))|~v5_pre_topc(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29),X31,X32)|~m1_subset_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X32))))|~v1_funct_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29))|~v1_funct_2(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29),u1_struct_0(X30),u1_struct_0(X32))|~v5_pre_topc(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29),X30,X32)|~m1_subset_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X32)))))|~epred1_5(X32,X31,X30,X29,X28)))&(m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X28,X31,X30)),u1_struct_0(X32))))|(~v1_funct_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29))|~v1_funct_2(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29),u1_struct_0(X31),u1_struct_0(X32))|~v5_pre_topc(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29),X31,X32)|~m1_subset_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X31,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X32))))|~v1_funct_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29))|~v1_funct_2(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29),u1_struct_0(X30),u1_struct_0(X32))|~v5_pre_topc(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29),X30,X32)|~m1_subset_1(k3_tmap_1(X28,X32,k1_tsep_1(X28,X31,X30),X30,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X32)))))|~epred1_5(X32,X31,X30,X29,X28)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 9.00/9.22  cnf(c_0_32, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 9.00/9.22  cnf(c_0_33, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 9.00/9.22  cnf(c_0_34, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk1_0,esk5_0,esk3_0)=k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(esk5_0))|v2_struct_0(X1)|~m1_pre_topc(esk1_0,X1)|~m1_pre_topc(esk5_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_25, c_0_18])).
% 9.00/9.22  cnf(c_0_35, negated_conjecture, (m1_pre_topc(esk1_0,esk1_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])).
% 9.00/9.22  cnf(c_0_36, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|epred1_5(X2,X3,X4,X5,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~r4_tsep_1(X1,X3,X4)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 9.00/9.22  cnf(c_0_37, negated_conjecture, (r4_tsep_1(esk1_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 9.00/9.22  cnf(c_0_38, plain, (v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),X4,X2)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))|~v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))|~epred1_5(X2,X3,X4,X5,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 9.00/9.22  cnf(c_0_39, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(X1))=k2_tmap_1(esk1_0,esk2_0,esk3_0,X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_11]), c_0_12]), c_0_13]), c_0_14]), c_0_19]), c_0_15]), c_0_33])]), c_0_16]), c_0_21])).
% 9.00/9.22  cnf(c_0_40, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(esk5_0))=k3_tmap_1(esk1_0,esk2_0,esk1_0,esk5_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_18]), c_0_19]), c_0_33])]), c_0_21])).
% 9.00/9.22  cnf(c_0_41, negated_conjecture, (epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_28]), c_0_37]), c_0_18]), c_0_27]), c_0_19]), c_0_33])]), c_0_20]), c_0_29]), c_0_21])).
% 9.00/9.22  cnf(c_0_42, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk1_0,esk4_0,esk3_0)=k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(esk4_0))|v2_struct_0(X1)|~m1_pre_topc(esk1_0,X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_25, c_0_27])).
% 9.00/9.22  cnf(c_0_43, negated_conjecture, (~v1_funct_1(esk3_0)|~v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))|~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 9.00/9.22  cnf(c_0_44, negated_conjecture, (v5_pre_topc(k3_tmap_1(esk1_0,X1,esk1_0,esk5_0,X2),esk5_0,X1)|~epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)|~v5_pre_topc(X2,esk1_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)), inference(spm,[status(thm)],[c_0_38, c_0_28])).
% 9.00/9.22  cnf(c_0_45, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk1_0,esk5_0,esk3_0)=k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_18])])).
% 9.00/9.22  cnf(c_0_46, negated_conjecture, (epred1_5(esk2_0,esk4_0,esk5_0,esk3_0,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_11]), c_0_12]), c_0_13]), c_0_14]), c_0_15])]), c_0_16])).
% 9.00/9.22  cnf(c_0_47, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 9.00/9.22  cnf(c_0_48, plain, (v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),X3,X2)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))|~v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))|~epred1_5(X2,X3,X4,X5,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 9.00/9.22  cnf(c_0_49, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(esk4_0))=k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_35]), c_0_27]), c_0_19]), c_0_33])]), c_0_21])).
% 9.00/9.22  cnf(c_0_50, negated_conjecture, (~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_13]), c_0_12]), c_0_11])])).
% 9.00/9.22  cnf(c_0_51, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_11]), c_0_12]), c_0_13])]), c_0_47])).
% 9.00/9.22  cnf(c_0_52, negated_conjecture, (v5_pre_topc(k3_tmap_1(esk1_0,X1,esk1_0,esk4_0,X2),esk4_0,X1)|~epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)|~v5_pre_topc(X2,esk1_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)), inference(spm,[status(thm)],[c_0_48, c_0_28])).
% 9.00/9.22  cnf(c_0_53, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk3_0)=k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_49]), c_0_27])])).
% 9.00/9.22  cnf(c_0_54, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 9.00/9.22  cnf(c_0_55, plain, (v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5))|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))|~v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))|~epred1_5(X2,X3,X4,X5,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 9.00/9.22  cnf(c_0_56, negated_conjecture, (~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_51])])).
% 9.00/9.22  cnf(c_0_57, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_46]), c_0_11]), c_0_12]), c_0_13])]), c_0_54])).
% 9.00/9.22  cnf(c_0_58, negated_conjecture, (v1_funct_1(k3_tmap_1(esk1_0,X1,esk1_0,esk5_0,X2))|~epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)|~v5_pre_topc(X2,esk1_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)), inference(spm,[status(thm)],[c_0_55, c_0_28])).
% 9.00/9.22  cnf(c_0_59, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 9.00/9.22  cnf(c_0_60, plain, (v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5))|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))|~v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))|~epred1_5(X2,X3,X4,X5,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 9.00/9.22  cnf(c_0_61, negated_conjecture, (~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57])])).
% 9.00/9.22  cnf(c_0_62, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_11]), c_0_45]), c_0_46]), c_0_12]), c_0_13])]), c_0_59])).
% 9.00/9.22  cnf(c_0_63, negated_conjecture, (v1_funct_1(k3_tmap_1(esk1_0,X1,esk1_0,esk4_0,X2))|~epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)|~v5_pre_topc(X2,esk1_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)), inference(spm,[status(thm)],[c_0_60, c_0_28])).
% 9.00/9.22  cnf(c_0_64, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 9.00/9.22  cnf(c_0_65, plain, (m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))|~v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))|~epred1_5(X2,X3,X4,X5,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 9.00/9.22  cnf(c_0_66, negated_conjecture, (~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62])])).
% 9.00/9.22  cnf(c_0_67, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_11]), c_0_53]), c_0_46]), c_0_12]), c_0_13])]), c_0_64])).
% 9.00/9.22  cnf(c_0_68, negated_conjecture, (m1_subset_1(k3_tmap_1(esk1_0,X1,esk1_0,esk5_0,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))|~epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)|~v5_pre_topc(X2,esk1_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)), inference(spm,[status(thm)],[c_0_65, c_0_28])).
% 9.00/9.22  cnf(c_0_69, negated_conjecture, (m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 9.00/9.22  cnf(c_0_70, plain, (m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))|~v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))|~epred1_5(X2,X3,X4,X5,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 9.00/9.22  cnf(c_0_71, negated_conjecture, (~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_67])])).
% 9.00/9.22  cnf(c_0_72, negated_conjecture, (m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_45]), c_0_46]), c_0_11]), c_0_12]), c_0_13])]), c_0_69])).
% 9.00/9.22  cnf(c_0_73, negated_conjecture, (m1_subset_1(k3_tmap_1(esk1_0,X1,esk1_0,esk4_0,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1))))|~epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)|~v5_pre_topc(X2,esk1_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)), inference(spm,[status(thm)],[c_0_70, c_0_28])).
% 9.00/9.22  cnf(c_0_74, negated_conjecture, (m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 9.00/9.22  cnf(c_0_75, plain, (v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),u1_struct_0(X4),u1_struct_0(X2))|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))|~v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))|~epred1_5(X2,X3,X4,X5,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 9.00/9.22  cnf(c_0_76, negated_conjecture, (~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_72])])).
% 9.00/9.22  cnf(c_0_77, negated_conjecture, (m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_53]), c_0_46]), c_0_11]), c_0_12]), c_0_13])]), c_0_74])).
% 9.00/9.22  cnf(c_0_78, negated_conjecture, (v1_funct_2(k3_tmap_1(esk1_0,X1,esk1_0,esk5_0,X2),u1_struct_0(esk5_0),u1_struct_0(X1))|~epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)|~v5_pre_topc(X2,esk1_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)), inference(spm,[status(thm)],[c_0_75, c_0_28])).
% 9.00/9.22  cnf(c_0_79, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 9.00/9.22  cnf(c_0_80, plain, (v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))|~v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))|~epred1_5(X2,X3,X4,X5,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 9.00/9.22  cnf(c_0_81, negated_conjecture, (~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_77])])).
% 9.00/9.22  cnf(c_0_82, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_11]), c_0_45]), c_0_46]), c_0_12]), c_0_13])]), c_0_79])).
% 9.00/9.22  cnf(c_0_83, negated_conjecture, (v1_funct_2(k3_tmap_1(esk1_0,X1,esk1_0,esk4_0,X2),u1_struct_0(esk4_0),u1_struct_0(X1))|~epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)|~v5_pre_topc(X2,esk1_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)), inference(spm,[status(thm)],[c_0_80, c_0_28])).
% 9.00/9.22  cnf(c_0_84, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 9.00/9.22  cnf(c_0_85, plain, (v5_pre_topc(X1,k1_tsep_1(X2,X3,X4),X5)|~v1_funct_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1))|~v1_funct_2(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1),u1_struct_0(X3),u1_struct_0(X5))|~v5_pre_topc(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1),X3,X5)|~m1_subset_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X5))))|~v1_funct_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1))|~v1_funct_2(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1),u1_struct_0(X4),u1_struct_0(X5))|~v5_pre_topc(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1),X4,X5)|~m1_subset_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))|~epred1_5(X5,X3,X4,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 9.00/9.22  cnf(c_0_86, negated_conjecture, (~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_82])])).
% 9.00/9.22  cnf(c_0_87, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_11]), c_0_53]), c_0_46]), c_0_12]), c_0_13])]), c_0_84])).
% 9.00/9.22  cnf(c_0_88, negated_conjecture, (v5_pre_topc(X1,esk1_0,X2)|~epred1_5(X2,esk4_0,esk5_0,X1,esk1_0)|~v5_pre_topc(k3_tmap_1(esk1_0,X2,esk1_0,esk5_0,X1),esk5_0,X2)|~v5_pre_topc(k3_tmap_1(esk1_0,X2,esk1_0,esk4_0,X1),esk4_0,X2)|~m1_subset_1(k3_tmap_1(esk1_0,X2,esk1_0,esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X2))))|~m1_subset_1(k3_tmap_1(esk1_0,X2,esk1_0,esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X2))))|~v1_funct_2(k3_tmap_1(esk1_0,X2,esk1_0,esk5_0,X1),u1_struct_0(esk5_0),u1_struct_0(X2))|~v1_funct_2(k3_tmap_1(esk1_0,X2,esk1_0,esk4_0,X1),u1_struct_0(esk4_0),u1_struct_0(X2))|~v1_funct_1(k3_tmap_1(esk1_0,X2,esk1_0,esk5_0,X1))|~v1_funct_1(k3_tmap_1(esk1_0,X2,esk1_0,esk4_0,X1))), inference(spm,[status(thm)],[c_0_85, c_0_28])).
% 9.00/9.22  cnf(c_0_89, negated_conjecture, (~v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_87])])).
% 9.00/9.22  cnf(c_0_90, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_45]), c_0_46]), c_0_51]), c_0_53]), c_0_57]), c_0_72]), c_0_53]), c_0_77]), c_0_82]), c_0_53]), c_0_87]), c_0_62]), c_0_53]), c_0_67])]), c_0_89]), ['proof']).
% 9.00/9.22  # SZS output end CNFRefutation
% 9.00/9.22  # Proof object total steps             : 91
% 9.00/9.22  # Proof object clause steps            : 76
% 9.00/9.22  # Proof object formula steps           : 15
% 9.00/9.22  # Proof object conjectures             : 66
% 9.00/9.22  # Proof object clause conjectures      : 63
% 9.00/9.22  # Proof object formula conjectures     : 3
% 9.00/9.22  # Proof object initial clauses used    : 37
% 9.00/9.22  # Proof object initial formulas used   : 5
% 9.00/9.22  # Proof object generating inferences   : 30
% 9.00/9.22  # Proof object simplifying inferences  : 133
% 9.00/9.22  # Training examples: 0 positive, 0 negative
% 9.00/9.22  # Parsed axioms                        : 5
% 9.00/9.22  # Removed by relevancy pruning/SinE    : 0
% 9.00/9.22  # Initial clauses                      : 66
% 9.00/9.22  # Removed in clause preprocessing      : 0
% 9.00/9.22  # Initial clauses in saturation        : 66
% 9.00/9.22  # Processed clauses                    : 4241
% 9.00/9.22  # ...of these trivial                  : 24
% 9.00/9.22  # ...subsumed                          : 2
% 9.00/9.22  # ...remaining for further processing  : 4215
% 9.00/9.22  # Other redundant clauses eliminated   : 0
% 9.00/9.22  # Clauses deleted for lack of memory   : 0
% 9.00/9.22  # Backward-subsumed                    : 12
% 9.00/9.22  # Backward-rewritten                   : 34
% 9.00/9.22  # Generated clauses                    : 938405
% 9.00/9.22  # ...of the previous two non-trivial   : 938407
% 9.00/9.22  # Contextual simplify-reflections      : 98
% 9.00/9.22  # Paramodulations                      : 938405
% 9.00/9.22  # Factorizations                       : 0
% 9.00/9.22  # Equation resolutions                 : 0
% 9.00/9.22  # Propositional unsat checks           : 0
% 9.00/9.22  #    Propositional check models        : 0
% 9.00/9.22  #    Propositional check unsatisfiable : 0
% 9.00/9.22  #    Propositional clauses             : 0
% 9.00/9.22  #    Propositional clauses after purity: 0
% 9.00/9.22  #    Propositional unsat core size     : 0
% 9.00/9.22  #    Propositional preprocessing time  : 0.000
% 9.00/9.22  #    Propositional encoding time       : 0.000
% 9.00/9.22  #    Propositional solver time         : 0.000
% 9.00/9.22  #    Success case prop preproc time    : 0.000
% 9.00/9.22  #    Success case prop encoding time   : 0.000
% 9.00/9.22  #    Success case prop solver time     : 0.000
% 9.00/9.22  # Current number of processed clauses  : 4127
% 9.00/9.22  #    Positive orientable unit clauses  : 60
% 9.00/9.22  #    Positive unorientable unit clauses: 0
% 9.00/9.22  #    Negative unit clauses             : 5
% 9.00/9.22  #    Non-unit-clauses                  : 4062
% 9.00/9.22  # Current number of unprocessed clauses: 934272
% 9.00/9.22  # ...number of literals in the above   : 6589432
% 9.00/9.22  # Current number of archived formulas  : 0
% 9.00/9.22  # Current number of archived clauses   : 88
% 9.00/9.22  # Clause-clause subsumption calls (NU) : 3576535
% 9.00/9.22  # Rec. Clause-clause subsumption calls : 98644
% 9.00/9.22  # Non-unit clause-clause subsumptions  : 104
% 9.00/9.22  # Unit Clause-clause subsumption calls : 196
% 9.00/9.22  # Rewrite failures with RHS unbound    : 0
% 9.00/9.22  # BW rewrite match attempts            : 257
% 9.00/9.22  # BW rewrite match successes           : 30
% 9.00/9.22  # Condensation attempts                : 0
% 9.00/9.22  # Condensation successes               : 0
% 9.00/9.22  # Termbank termtop insertions          : 61113326
% 9.11/9.28  
% 9.11/9.28  # -------------------------------------------------
% 9.11/9.28  # User time                : 8.381 s
% 9.11/9.28  # System time              : 0.560 s
% 9.11/9.28  # Total time               : 8.941 s
% 9.11/9.28  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
