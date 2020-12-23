%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:32 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  102 (3462 expanded)
%              Number of clauses        :   75 (1126 expanded)
%              Number of leaves         :   12 ( 850 expanded)
%              Depth                    :   19
%              Number of atoms          :  647 (97138 expanded)
%              Number of equality atoms :   18 (2064 expanded)
%              Maximal formula depth    :   49 (   6 average)
%              Maximal clause size      :   91 (   3 average)
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

fof(dt_k2_tmap_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X2)
        & v1_funct_1(X3)
        & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        & l1_struct_0(X4) )
     => ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
        & v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
        & m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

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

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t129_tmap_1,axiom,(
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
                          & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                       => ( ( v1_funct_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)))
                            & v1_funct_2(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
                            & v5_pre_topc(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_tsep_1(X1,X3,X4),X2)
                            & m1_subset_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) )
                        <=> ( v1_funct_1(k2_tmap_1(X1,X2,X5,X3))
                            & v1_funct_2(k2_tmap_1(X1,X2,X5,X3),u1_struct_0(X3),u1_struct_0(X2))
                            & v5_pre_topc(k2_tmap_1(X1,X2,X5,X3),X3,X2)
                            & m1_subset_1(k2_tmap_1(X1,X2,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
                            & v1_funct_1(k2_tmap_1(X1,X2,X5,X4))
                            & v1_funct_2(k2_tmap_1(X1,X2,X5,X4),u1_struct_0(X4),u1_struct_0(X2))
                            & v5_pre_topc(k2_tmap_1(X1,X2,X5,X4),X4,X2)
                            & m1_subset_1(k2_tmap_1(X1,X2,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_tmap_1)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(c_0_11,negated_conjecture,(
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

fof(c_0_12,plain,(
    ! [X25,X26,X27,X28] :
      ( ( v1_funct_1(k2_tmap_1(X25,X26,X27,X28))
        | ~ l1_struct_0(X25)
        | ~ l1_struct_0(X26)
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,u1_struct_0(X25),u1_struct_0(X26))
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(X26))))
        | ~ l1_struct_0(X28) )
      & ( v1_funct_2(k2_tmap_1(X25,X26,X27,X28),u1_struct_0(X28),u1_struct_0(X26))
        | ~ l1_struct_0(X25)
        | ~ l1_struct_0(X26)
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,u1_struct_0(X25),u1_struct_0(X26))
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(X26))))
        | ~ l1_struct_0(X28) )
      & ( m1_subset_1(k2_tmap_1(X25,X26,X27,X28),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X26))))
        | ~ l1_struct_0(X25)
        | ~ l1_struct_0(X26)
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,u1_struct_0(X25),u1_struct_0(X26))
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(X26))))
        | ~ l1_struct_0(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).

fof(c_0_13,negated_conjecture,
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
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])).

cnf(c_0_14,plain,
    ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X18] :
      ( ~ l1_pre_topc(X18)
      | l1_struct_0(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])])).

cnf(c_0_20,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_22,plain,(
    ! [X14,X15,X16,X17] :
      ( ~ v1_funct_1(X16)
      | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
      | k2_partfun1(X14,X15,X16,X17) = k7_relat_1(X16,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1))
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_25,plain,(
    ! [X19,X20] :
      ( ~ l1_pre_topc(X19)
      | ~ m1_pre_topc(X20,X19)
      | l1_pre_topc(X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_26,plain,(
    ! [X21,X22,X23,X24] :
      ( v2_struct_0(X21)
      | ~ v2_pre_topc(X21)
      | ~ l1_pre_topc(X21)
      | v2_struct_0(X22)
      | ~ v2_pre_topc(X22)
      | ~ l1_pre_topc(X22)
      | ~ v1_funct_1(X23)
      | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22))))
      | ~ m1_pre_topc(X24,X21)
      | k2_tmap_1(X21,X22,X23,X24) = k2_partfun1(u1_struct_0(X21),u1_struct_0(X22),X23,u1_struct_0(X24)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_27,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_28,plain,(
    ! [X8,X9,X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | v1_relat_1(X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_29,plain,(
    ! [X1,X5,X4,X3,X2] :
      ( epred1_5(X2,X3,X4,X5,X1)
    <=> ( ( v1_funct_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)))
          & v1_funct_2(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
          & v5_pre_topc(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_tsep_1(X1,X3,X4),X2)
          & m1_subset_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) )
      <=> ( v1_funct_1(k2_tmap_1(X1,X2,X5,X3))
          & v1_funct_2(k2_tmap_1(X1,X2,X5,X3),u1_struct_0(X3),u1_struct_0(X2))
          & v5_pre_topc(k2_tmap_1(X1,X2,X5,X3),X3,X2)
          & m1_subset_1(k2_tmap_1(X1,X2,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
          & v1_funct_1(k2_tmap_1(X1,X2,X5,X4))
          & v1_funct_2(k2_tmap_1(X1,X2,X5,X4),u1_struct_0(X4),u1_struct_0(X2))
          & v5_pre_topc(k2_tmap_1(X1,X2,X5,X4),X4,X2)
          & m1_subset_1(k2_tmap_1(X1,X2,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ) ),
    introduced(definition)).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_20]),c_0_24])])).

cnf(c_0_31,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_33,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_34,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(X7)
      | ~ v4_relat_1(X7,X6)
      | X7 = k7_relat_1(X7,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_35,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1) = k7_relat_1(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_15]),c_0_17])])).

cnf(c_0_37,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_38,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_39,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_40,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_41,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_42,plain,(
    ! [X11,X12,X13] :
      ( ( v4_relat_1(X13,X11)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) )
      & ( v5_relat_1(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_43,axiom,(
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
                          & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                       => epred1_5(X2,X3,X4,X5,X1) ) ) ) ) ) ) ),
    inference(apply_def,[status(thm)],[t129_tmap_1,c_0_29])).

cnf(c_0_44,negated_conjecture,
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
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_20])).

cnf(c_0_46,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_24])])).

cnf(c_0_47,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_33]),c_0_24])])).

fof(c_0_48,plain,(
    ! [X1,X5,X4,X3,X2] :
      ( epred1_5(X2,X3,X4,X5,X1)
     => ( ( v1_funct_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)))
          & v1_funct_2(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
          & v5_pre_topc(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_tsep_1(X1,X3,X4),X2)
          & m1_subset_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) )
      <=> ( v1_funct_1(k2_tmap_1(X1,X2,X5,X3))
          & v1_funct_2(k2_tmap_1(X1,X2,X5,X3),u1_struct_0(X3),u1_struct_0(X2))
          & v5_pre_topc(k2_tmap_1(X1,X2,X5,X3),X3,X2)
          & m1_subset_1(k2_tmap_1(X1,X2,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
          & v1_funct_1(k2_tmap_1(X1,X2,X5,X4))
          & v1_funct_2(k2_tmap_1(X1,X2,X5,X4),u1_struct_0(X4),u1_struct_0(X2))
          & v5_pre_topc(k2_tmap_1(X1,X2,X5,X4),X4,X2)
          & m1_subset_1(k2_tmap_1(X1,X2,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ) ),
    inference(split_equiv,[status(thm)],[c_0_29])).

cnf(c_0_49,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_50,negated_conjecture,
    ( k7_relat_1(esk3_0,u1_struct_0(X1)) = k2_tmap_1(esk1_0,esk2_0,esk3_0,X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_15]),c_0_36]),c_0_16]),c_0_37]),c_0_38]),c_0_21]),c_0_24]),c_0_17])]),c_0_39]),c_0_40])).

cnf(c_0_51,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_15])).

cnf(c_0_52,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_53,plain,(
    ! [X29,X30,X31,X32,X33] :
      ( v2_struct_0(X29)
      | ~ v2_pre_topc(X29)
      | ~ l1_pre_topc(X29)
      | v2_struct_0(X30)
      | ~ v2_pre_topc(X30)
      | ~ l1_pre_topc(X30)
      | v2_struct_0(X31)
      | ~ m1_pre_topc(X31,X29)
      | v2_struct_0(X32)
      | ~ m1_pre_topc(X32,X29)
      | ~ r4_tsep_1(X29,X31,X32)
      | ~ v1_funct_1(X33)
      | ~ v1_funct_2(X33,u1_struct_0(X29),u1_struct_0(X30))
      | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X30))))
      | epred1_5(X30,X31,X32,X33,X29) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_43])])])])).

cnf(c_0_54,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_17]),c_0_16]),c_0_15])])).

cnf(c_0_55,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_56,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_47])).

cnf(c_0_57,plain,
    ( v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_58,plain,(
    ! [X40,X41,X42,X43,X44] :
      ( ( v1_funct_1(k2_tmap_1(X40,X44,X41,X43))
        | ~ v1_funct_1(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)))
        | ~ v1_funct_2(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),u1_struct_0(k1_tsep_1(X40,X43,X42)),u1_struct_0(X44))
        | ~ v5_pre_topc(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),k1_tsep_1(X40,X43,X42),X44)
        | ~ m1_subset_1(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X40,X43,X42)),u1_struct_0(X44))))
        | ~ epred1_5(X44,X43,X42,X41,X40) )
      & ( v1_funct_2(k2_tmap_1(X40,X44,X41,X43),u1_struct_0(X43),u1_struct_0(X44))
        | ~ v1_funct_1(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)))
        | ~ v1_funct_2(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),u1_struct_0(k1_tsep_1(X40,X43,X42)),u1_struct_0(X44))
        | ~ v5_pre_topc(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),k1_tsep_1(X40,X43,X42),X44)
        | ~ m1_subset_1(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X40,X43,X42)),u1_struct_0(X44))))
        | ~ epred1_5(X44,X43,X42,X41,X40) )
      & ( v5_pre_topc(k2_tmap_1(X40,X44,X41,X43),X43,X44)
        | ~ v1_funct_1(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)))
        | ~ v1_funct_2(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),u1_struct_0(k1_tsep_1(X40,X43,X42)),u1_struct_0(X44))
        | ~ v5_pre_topc(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),k1_tsep_1(X40,X43,X42),X44)
        | ~ m1_subset_1(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X40,X43,X42)),u1_struct_0(X44))))
        | ~ epred1_5(X44,X43,X42,X41,X40) )
      & ( m1_subset_1(k2_tmap_1(X40,X44,X41,X43),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X43),u1_struct_0(X44))))
        | ~ v1_funct_1(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)))
        | ~ v1_funct_2(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),u1_struct_0(k1_tsep_1(X40,X43,X42)),u1_struct_0(X44))
        | ~ v5_pre_topc(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),k1_tsep_1(X40,X43,X42),X44)
        | ~ m1_subset_1(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X40,X43,X42)),u1_struct_0(X44))))
        | ~ epred1_5(X44,X43,X42,X41,X40) )
      & ( v1_funct_1(k2_tmap_1(X40,X44,X41,X42))
        | ~ v1_funct_1(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)))
        | ~ v1_funct_2(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),u1_struct_0(k1_tsep_1(X40,X43,X42)),u1_struct_0(X44))
        | ~ v5_pre_topc(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),k1_tsep_1(X40,X43,X42),X44)
        | ~ m1_subset_1(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X40,X43,X42)),u1_struct_0(X44))))
        | ~ epred1_5(X44,X43,X42,X41,X40) )
      & ( v1_funct_2(k2_tmap_1(X40,X44,X41,X42),u1_struct_0(X42),u1_struct_0(X44))
        | ~ v1_funct_1(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)))
        | ~ v1_funct_2(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),u1_struct_0(k1_tsep_1(X40,X43,X42)),u1_struct_0(X44))
        | ~ v5_pre_topc(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),k1_tsep_1(X40,X43,X42),X44)
        | ~ m1_subset_1(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X40,X43,X42)),u1_struct_0(X44))))
        | ~ epred1_5(X44,X43,X42,X41,X40) )
      & ( v5_pre_topc(k2_tmap_1(X40,X44,X41,X42),X42,X44)
        | ~ v1_funct_1(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)))
        | ~ v1_funct_2(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),u1_struct_0(k1_tsep_1(X40,X43,X42)),u1_struct_0(X44))
        | ~ v5_pre_topc(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),k1_tsep_1(X40,X43,X42),X44)
        | ~ m1_subset_1(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X40,X43,X42)),u1_struct_0(X44))))
        | ~ epred1_5(X44,X43,X42,X41,X40) )
      & ( m1_subset_1(k2_tmap_1(X40,X44,X41,X42),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X44))))
        | ~ v1_funct_1(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)))
        | ~ v1_funct_2(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),u1_struct_0(k1_tsep_1(X40,X43,X42)),u1_struct_0(X44))
        | ~ v5_pre_topc(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),k1_tsep_1(X40,X43,X42),X44)
        | ~ m1_subset_1(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X40,X43,X42)),u1_struct_0(X44))))
        | ~ epred1_5(X44,X43,X42,X41,X40) )
      & ( v1_funct_1(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)))
        | ~ v1_funct_1(k2_tmap_1(X40,X44,X41,X43))
        | ~ v1_funct_2(k2_tmap_1(X40,X44,X41,X43),u1_struct_0(X43),u1_struct_0(X44))
        | ~ v5_pre_topc(k2_tmap_1(X40,X44,X41,X43),X43,X44)
        | ~ m1_subset_1(k2_tmap_1(X40,X44,X41,X43),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X43),u1_struct_0(X44))))
        | ~ v1_funct_1(k2_tmap_1(X40,X44,X41,X42))
        | ~ v1_funct_2(k2_tmap_1(X40,X44,X41,X42),u1_struct_0(X42),u1_struct_0(X44))
        | ~ v5_pre_topc(k2_tmap_1(X40,X44,X41,X42),X42,X44)
        | ~ m1_subset_1(k2_tmap_1(X40,X44,X41,X42),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X44))))
        | ~ epred1_5(X44,X43,X42,X41,X40) )
      & ( v1_funct_2(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),u1_struct_0(k1_tsep_1(X40,X43,X42)),u1_struct_0(X44))
        | ~ v1_funct_1(k2_tmap_1(X40,X44,X41,X43))
        | ~ v1_funct_2(k2_tmap_1(X40,X44,X41,X43),u1_struct_0(X43),u1_struct_0(X44))
        | ~ v5_pre_topc(k2_tmap_1(X40,X44,X41,X43),X43,X44)
        | ~ m1_subset_1(k2_tmap_1(X40,X44,X41,X43),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X43),u1_struct_0(X44))))
        | ~ v1_funct_1(k2_tmap_1(X40,X44,X41,X42))
        | ~ v1_funct_2(k2_tmap_1(X40,X44,X41,X42),u1_struct_0(X42),u1_struct_0(X44))
        | ~ v5_pre_topc(k2_tmap_1(X40,X44,X41,X42),X42,X44)
        | ~ m1_subset_1(k2_tmap_1(X40,X44,X41,X42),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X44))))
        | ~ epred1_5(X44,X43,X42,X41,X40) )
      & ( v5_pre_topc(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),k1_tsep_1(X40,X43,X42),X44)
        | ~ v1_funct_1(k2_tmap_1(X40,X44,X41,X43))
        | ~ v1_funct_2(k2_tmap_1(X40,X44,X41,X43),u1_struct_0(X43),u1_struct_0(X44))
        | ~ v5_pre_topc(k2_tmap_1(X40,X44,X41,X43),X43,X44)
        | ~ m1_subset_1(k2_tmap_1(X40,X44,X41,X43),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X43),u1_struct_0(X44))))
        | ~ v1_funct_1(k2_tmap_1(X40,X44,X41,X42))
        | ~ v1_funct_2(k2_tmap_1(X40,X44,X41,X42),u1_struct_0(X42),u1_struct_0(X44))
        | ~ v5_pre_topc(k2_tmap_1(X40,X44,X41,X42),X42,X44)
        | ~ m1_subset_1(k2_tmap_1(X40,X44,X41,X42),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X44))))
        | ~ epred1_5(X44,X43,X42,X41,X40) )
      & ( m1_subset_1(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X40,X43,X42)),u1_struct_0(X44))))
        | ~ v1_funct_1(k2_tmap_1(X40,X44,X41,X43))
        | ~ v1_funct_2(k2_tmap_1(X40,X44,X41,X43),u1_struct_0(X43),u1_struct_0(X44))
        | ~ v5_pre_topc(k2_tmap_1(X40,X44,X41,X43),X43,X44)
        | ~ m1_subset_1(k2_tmap_1(X40,X44,X41,X43),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X43),u1_struct_0(X44))))
        | ~ v1_funct_1(k2_tmap_1(X40,X44,X41,X42))
        | ~ v1_funct_2(k2_tmap_1(X40,X44,X41,X42),u1_struct_0(X42),u1_struct_0(X44))
        | ~ v5_pre_topc(k2_tmap_1(X40,X44,X41,X42),X42,X44)
        | ~ m1_subset_1(k2_tmap_1(X40,X44,X41,X42),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X44))))
        | ~ epred1_5(X44,X43,X42,X41,X40) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_48])])])).

cnf(c_0_59,negated_conjecture,
    ( k2_tmap_1(esk1_0,esk2_0,esk3_0,X1) = esk3_0
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ v4_relat_1(esk3_0,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])])).

cnf(c_0_60,negated_conjecture,
    ( v4_relat_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_15])).

fof(c_0_61,plain,(
    ! [X34] :
      ( ~ l1_pre_topc(X34)
      | m1_pre_topc(X34,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_62,plain,
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
    | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_63,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55])]),c_0_56])])).

cnf(c_0_64,plain,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_65,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_15]),c_0_16]),c_0_17])])).

cnf(c_0_66,plain,
    ( v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),u1_struct_0(k1_tsep_1(X1,X5,X4)),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),k1_tsep_1(X1,X5,X4),X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X5,X4)),u1_struct_0(X2))))
    | ~ epred1_5(X2,X5,X4,X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_67,negated_conjecture,
    ( esk1_0 = k1_tsep_1(esk1_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_68,negated_conjecture,
    ( k2_tmap_1(esk1_0,esk2_0,esk3_0,esk1_0) = esk3_0
    | ~ m1_pre_topc(esk1_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_69,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_70,negated_conjecture,
    ( epred1_5(esk2_0,X1,X2,esk3_0,esk1_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r4_tsep_1(esk1_0,X1,X2)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_15]),c_0_16]),c_0_37]),c_0_38]),c_0_21]),c_0_24]),c_0_17])]),c_0_39]),c_0_40])).

cnf(c_0_71,negated_conjecture,
    ( r4_tsep_1(esk1_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_72,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_73,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_74,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ l1_struct_0(esk5_0)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_16]),c_0_17]),c_0_15])]),c_0_65])).

cnf(c_0_75,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk5_0),esk5_0,X1)
    | ~ epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk1_0),esk1_0,X1)
    | ~ v1_funct_2(k2_tmap_1(esk1_0,X1,X2,esk1_0),u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,X1,X2,esk1_0))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,X1,X2,esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1)))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_76,negated_conjecture,
    ( k2_tmap_1(esk1_0,esk2_0,esk3_0,esk1_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_24])])).

cnf(c_0_77,negated_conjecture,
    ( epred1_5(esk2_0,esk4_0,esk5_0,esk3_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_32]),c_0_33])]),c_0_72]),c_0_73])).

cnf(c_0_78,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_79,plain,
    ( v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_tsep_1(X1,X4,X5),X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))))
    | ~ epred1_5(X2,X4,X5,X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_80,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ l1_struct_0(esk5_0)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_64]),c_0_16]),c_0_17]),c_0_15])]),c_0_65])).

cnf(c_0_81,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77]),c_0_16]),c_0_17]),c_0_15])]),c_0_78])).

cnf(c_0_82,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk4_0),esk4_0,X1)
    | ~ epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk1_0),esk1_0,X1)
    | ~ v1_funct_2(k2_tmap_1(esk1_0,X1,X2,esk1_0),u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,X1,X2,esk1_0))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,X1,X2,esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1)))) ),
    inference(spm,[status(thm)],[c_0_79,c_0_67])).

cnf(c_0_83,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_84,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ l1_struct_0(esk5_0)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_81])])).

cnf(c_0_85,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_76]),c_0_77]),c_0_16]),c_0_17]),c_0_15])]),c_0_83])).

cnf(c_0_86,negated_conjecture,
    ( ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ l1_struct_0(esk5_0)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_85])])).

cnf(c_0_87,negated_conjecture,
    ( ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_20]),c_0_46])])).

cnf(c_0_88,negated_conjecture,
    ( ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_20]),c_0_47])])).

cnf(c_0_89,negated_conjecture,
    ( ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_20]),c_0_24])])).

cnf(c_0_90,plain,
    ( v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_tsep_1(X1,X4,X5),X2)
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,X5))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,X5),u1_struct_0(X5),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,X5),X5,X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2))))
    | ~ epred1_5(X2,X4,X5,X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_91,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_92,negated_conjecture,
    ( ~ v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_20]),c_0_21])])).

cnf(c_0_93,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_94,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_95,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_96,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk1_0),esk1_0,X1)
    | ~ epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk5_0),esk5_0,X1)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk4_0),esk4_0,X1)
    | ~ v1_funct_2(k2_tmap_1(esk1_0,X1,X2,esk5_0),u1_struct_0(esk5_0),u1_struct_0(X1))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,X1,X2,esk4_0),u1_struct_0(esk4_0),u1_struct_0(X1))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,X1,X2,esk5_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,X1,X2,esk4_0))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,X1,X2,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,X1,X2,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1)))) ),
    inference(spm,[status(thm)],[c_0_90,c_0_67])).

cnf(c_0_97,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_98,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[c_0_93,c_0_92])).

cnf(c_0_99,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[c_0_94,c_0_92])).

cnf(c_0_100,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[c_0_95,c_0_92])).

cnf(c_0_101,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_76]),c_0_77]),c_0_81]),c_0_85]),c_0_98]),c_0_99]),c_0_55]),c_0_56]),c_0_100])]),c_0_92]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:43:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.44  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.18/0.44  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.18/0.44  #
% 0.18/0.44  # Preprocessing time       : 0.030 s
% 0.18/0.44  # Presaturation interreduction done
% 0.18/0.44  
% 0.18/0.44  # Proof found!
% 0.18/0.44  # SZS status Theorem
% 0.18/0.44  # SZS output start CNFRefutation
% 0.18/0.44  fof(t132_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>((X1=k1_tsep_1(X1,X4,X5)&r4_tsep_1(X1,X4,X5))=>((((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&v5_pre_topc(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))<=>(((((((v1_funct_1(k2_tmap_1(X1,X2,X3,X4))&v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2))&m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))&v1_funct_1(k2_tmap_1(X1,X2,X3,X5)))&v1_funct_2(k2_tmap_1(X1,X2,X3,X5),u1_struct_0(X5),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X3,X5),X5,X2))&m1_subset_1(k2_tmap_1(X1,X2,X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_tmap_1)).
% 0.18/0.44  fof(dt_k2_tmap_1, axiom, ![X1, X2, X3, X4]:((((((l1_struct_0(X1)&l1_struct_0(X2))&v1_funct_1(X3))&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))&l1_struct_0(X4))=>((v1_funct_1(k2_tmap_1(X1,X2,X3,X4))&v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 0.18/0.44  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.18/0.44  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 0.18/0.44  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.18/0.44  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.18/0.44  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.18/0.44  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 0.18/0.44  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.18/0.44  fof(t129_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(r4_tsep_1(X1,X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((((v1_funct_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)))&v1_funct_2(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_tsep_1(X1,X3,X4),X2))&m1_subset_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))<=>(((((((v1_funct_1(k2_tmap_1(X1,X2,X5,X3))&v1_funct_2(k2_tmap_1(X1,X2,X5,X3),u1_struct_0(X3),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X5,X3),X3,X2))&m1_subset_1(k2_tmap_1(X1,X2,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))&v1_funct_1(k2_tmap_1(X1,X2,X5,X4)))&v1_funct_2(k2_tmap_1(X1,X2,X5,X4),u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X5,X4),X4,X2))&m1_subset_1(k2_tmap_1(X1,X2,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_tmap_1)).
% 0.18/0.44  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.18/0.44  fof(c_0_11, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>((X1=k1_tsep_1(X1,X4,X5)&r4_tsep_1(X1,X4,X5))=>((((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&v5_pre_topc(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))<=>(((((((v1_funct_1(k2_tmap_1(X1,X2,X3,X4))&v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2))&m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))&v1_funct_1(k2_tmap_1(X1,X2,X3,X5)))&v1_funct_2(k2_tmap_1(X1,X2,X3,X5),u1_struct_0(X5),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X3,X5),X5,X2))&m1_subset_1(k2_tmap_1(X1,X2,X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2))))))))))))), inference(assume_negation,[status(cth)],[t132_tmap_1])).
% 0.18/0.44  fof(c_0_12, plain, ![X25, X26, X27, X28]:(((v1_funct_1(k2_tmap_1(X25,X26,X27,X28))|(~l1_struct_0(X25)|~l1_struct_0(X26)|~v1_funct_1(X27)|~v1_funct_2(X27,u1_struct_0(X25),u1_struct_0(X26))|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(X26))))|~l1_struct_0(X28)))&(v1_funct_2(k2_tmap_1(X25,X26,X27,X28),u1_struct_0(X28),u1_struct_0(X26))|(~l1_struct_0(X25)|~l1_struct_0(X26)|~v1_funct_1(X27)|~v1_funct_2(X27,u1_struct_0(X25),u1_struct_0(X26))|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(X26))))|~l1_struct_0(X28))))&(m1_subset_1(k2_tmap_1(X25,X26,X27,X28),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X26))))|(~l1_struct_0(X25)|~l1_struct_0(X26)|~v1_funct_1(X27)|~v1_funct_2(X27,u1_struct_0(X25),u1_struct_0(X26))|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(X26))))|~l1_struct_0(X28)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).
% 0.18/0.44  fof(c_0_13, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk1_0))&((esk1_0=k1_tsep_1(esk1_0,esk4_0,esk5_0)&r4_tsep_1(esk1_0,esk4_0,esk5_0))&((~v1_funct_1(esk3_0)|~v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))|(~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))))&(((((((((((v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|v1_funct_1(esk3_0))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|v1_funct_1(esk3_0)))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|v1_funct_1(esk3_0)))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|v1_funct_1(esk3_0)))&(v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))|v1_funct_1(esk3_0)))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|v1_funct_1(esk3_0)))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|v1_funct_1(esk3_0)))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))|v1_funct_1(esk3_0)))&((((((((v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))))&(v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&((((((((v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|v5_pre_topc(esk3_0,esk1_0,esk2_0))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|v5_pre_topc(esk3_0,esk1_0,esk2_0)))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|v5_pre_topc(esk3_0,esk1_0,esk2_0)))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|v5_pre_topc(esk3_0,esk1_0,esk2_0)))&(v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))|v5_pre_topc(esk3_0,esk1_0,esk2_0)))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|v5_pre_topc(esk3_0,esk1_0,esk2_0)))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|v5_pre_topc(esk3_0,esk1_0,esk2_0)))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))|v5_pre_topc(esk3_0,esk1_0,esk2_0))))&((((((((v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))))&(v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))))))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])).
% 0.18/0.44  cnf(c_0_14, plain, (v1_funct_1(k2_tmap_1(X1,X2,X3,X4))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.44  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.44  cnf(c_0_16, negated_conjecture, (v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.44  cnf(c_0_17, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.44  fof(c_0_18, plain, ![X18]:(~l1_pre_topc(X18)|l1_struct_0(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.18/0.44  cnf(c_0_19, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1))|~l1_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17])])).
% 0.18/0.44  cnf(c_0_20, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.44  cnf(c_0_21, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.44  fof(c_0_22, plain, ![X14, X15, X16, X17]:(~v1_funct_1(X16)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))|k2_partfun1(X14,X15,X16,X17)=k7_relat_1(X16,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 0.18/0.44  cnf(c_0_23, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1))|~l1_struct_0(esk1_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 0.18/0.44  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.44  fof(c_0_25, plain, ![X19, X20]:(~l1_pre_topc(X19)|(~m1_pre_topc(X20,X19)|l1_pre_topc(X20))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.18/0.44  fof(c_0_26, plain, ![X21, X22, X23, X24]:(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)|(~v1_funct_1(X23)|~v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22))))|(~m1_pre_topc(X24,X21)|k2_tmap_1(X21,X22,X23,X24)=k2_partfun1(u1_struct_0(X21),u1_struct_0(X22),X23,u1_struct_0(X24)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.18/0.44  cnf(c_0_27, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.44  fof(c_0_28, plain, ![X8, X9, X10]:(~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))|v1_relat_1(X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.18/0.44  fof(c_0_29, plain, ![X1, X5, X4, X3, X2]:(epred1_5(X2,X3,X4,X5,X1)<=>((((v1_funct_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)))&v1_funct_2(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_tsep_1(X1,X3,X4),X2))&m1_subset_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))<=>(((((((v1_funct_1(k2_tmap_1(X1,X2,X5,X3))&v1_funct_2(k2_tmap_1(X1,X2,X5,X3),u1_struct_0(X3),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X5,X3),X3,X2))&m1_subset_1(k2_tmap_1(X1,X2,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))&v1_funct_1(k2_tmap_1(X1,X2,X5,X4)))&v1_funct_2(k2_tmap_1(X1,X2,X5,X4),u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X5,X4),X4,X2))&m1_subset_1(k2_tmap_1(X1,X2,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))))), introduced(definition)).
% 0.18/0.44  cnf(c_0_30, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1))|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_20]), c_0_24])])).
% 0.18/0.44  cnf(c_0_31, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.18/0.44  cnf(c_0_32, negated_conjecture, (m1_pre_topc(esk5_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.44  cnf(c_0_33, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.44  fof(c_0_34, plain, ![X6, X7]:(~v1_relat_1(X7)|~v4_relat_1(X7,X6)|X7=k7_relat_1(X7,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.18/0.44  cnf(c_0_35, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.44  cnf(c_0_36, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1)=k7_relat_1(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_15]), c_0_17])])).
% 0.18/0.44  cnf(c_0_37, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.44  cnf(c_0_38, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.44  cnf(c_0_39, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.44  cnf(c_0_40, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.44  cnf(c_0_41, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.44  fof(c_0_42, plain, ![X11, X12, X13]:((v4_relat_1(X13,X11)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))))&(v5_relat_1(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.18/0.44  fof(c_0_43, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(r4_tsep_1(X1,X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>epred1_5(X2,X3,X4,X5,X1))))))), inference(apply_def,[status(thm)],[t129_tmap_1, c_0_29])).
% 0.18/0.44  cnf(c_0_44, negated_conjecture, (~v1_funct_1(esk3_0)|~v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))|~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.44  cnf(c_0_45, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_30, c_0_20])).
% 0.18/0.44  cnf(c_0_46, negated_conjecture, (l1_pre_topc(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_24])])).
% 0.18/0.44  cnf(c_0_47, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_33]), c_0_24])])).
% 0.18/0.44  fof(c_0_48, plain, ![X1, X5, X4, X3, X2]:(epred1_5(X2,X3,X4,X5,X1)=>((((v1_funct_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)))&v1_funct_2(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_tsep_1(X1,X3,X4),X2))&m1_subset_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))<=>(((((((v1_funct_1(k2_tmap_1(X1,X2,X5,X3))&v1_funct_2(k2_tmap_1(X1,X2,X5,X3),u1_struct_0(X3),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X5,X3),X3,X2))&m1_subset_1(k2_tmap_1(X1,X2,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))&v1_funct_1(k2_tmap_1(X1,X2,X5,X4)))&v1_funct_2(k2_tmap_1(X1,X2,X5,X4),u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X5,X4),X4,X2))&m1_subset_1(k2_tmap_1(X1,X2,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))))), inference(split_equiv,[status(thm)],[c_0_29])).
% 0.18/0.44  cnf(c_0_49, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.44  cnf(c_0_50, negated_conjecture, (k7_relat_1(esk3_0,u1_struct_0(X1))=k2_tmap_1(esk1_0,esk2_0,esk3_0,X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_15]), c_0_36]), c_0_16]), c_0_37]), c_0_38]), c_0_21]), c_0_24]), c_0_17])]), c_0_39]), c_0_40])).
% 0.18/0.44  cnf(c_0_51, negated_conjecture, (v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_41, c_0_15])).
% 0.18/0.44  cnf(c_0_52, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.18/0.44  fof(c_0_53, plain, ![X29, X30, X31, X32, X33]:(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|(v2_struct_0(X31)|~m1_pre_topc(X31,X29)|(v2_struct_0(X32)|~m1_pre_topc(X32,X29)|(~r4_tsep_1(X29,X31,X32)|(~v1_funct_1(X33)|~v1_funct_2(X33,u1_struct_0(X29),u1_struct_0(X30))|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X30))))|epred1_5(X30,X31,X32,X33,X29))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_43])])])])).
% 0.18/0.45  cnf(c_0_54, negated_conjecture, (~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_17]), c_0_16]), c_0_15])])).
% 0.18/0.45  cnf(c_0_55, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.18/0.45  cnf(c_0_56, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_45, c_0_47])).
% 0.18/0.45  cnf(c_0_57, plain, (v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.45  fof(c_0_58, plain, ![X40, X41, X42, X43, X44]:(((((((((v1_funct_1(k2_tmap_1(X40,X44,X41,X43))|(~v1_funct_1(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)))|~v1_funct_2(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),u1_struct_0(k1_tsep_1(X40,X43,X42)),u1_struct_0(X44))|~v5_pre_topc(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),k1_tsep_1(X40,X43,X42),X44)|~m1_subset_1(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X40,X43,X42)),u1_struct_0(X44)))))|~epred1_5(X44,X43,X42,X41,X40))&(v1_funct_2(k2_tmap_1(X40,X44,X41,X43),u1_struct_0(X43),u1_struct_0(X44))|(~v1_funct_1(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)))|~v1_funct_2(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),u1_struct_0(k1_tsep_1(X40,X43,X42)),u1_struct_0(X44))|~v5_pre_topc(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),k1_tsep_1(X40,X43,X42),X44)|~m1_subset_1(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X40,X43,X42)),u1_struct_0(X44)))))|~epred1_5(X44,X43,X42,X41,X40)))&(v5_pre_topc(k2_tmap_1(X40,X44,X41,X43),X43,X44)|(~v1_funct_1(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)))|~v1_funct_2(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),u1_struct_0(k1_tsep_1(X40,X43,X42)),u1_struct_0(X44))|~v5_pre_topc(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),k1_tsep_1(X40,X43,X42),X44)|~m1_subset_1(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X40,X43,X42)),u1_struct_0(X44)))))|~epred1_5(X44,X43,X42,X41,X40)))&(m1_subset_1(k2_tmap_1(X40,X44,X41,X43),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X43),u1_struct_0(X44))))|(~v1_funct_1(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)))|~v1_funct_2(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),u1_struct_0(k1_tsep_1(X40,X43,X42)),u1_struct_0(X44))|~v5_pre_topc(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),k1_tsep_1(X40,X43,X42),X44)|~m1_subset_1(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X40,X43,X42)),u1_struct_0(X44)))))|~epred1_5(X44,X43,X42,X41,X40)))&(v1_funct_1(k2_tmap_1(X40,X44,X41,X42))|(~v1_funct_1(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)))|~v1_funct_2(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),u1_struct_0(k1_tsep_1(X40,X43,X42)),u1_struct_0(X44))|~v5_pre_topc(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),k1_tsep_1(X40,X43,X42),X44)|~m1_subset_1(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X40,X43,X42)),u1_struct_0(X44)))))|~epred1_5(X44,X43,X42,X41,X40)))&(v1_funct_2(k2_tmap_1(X40,X44,X41,X42),u1_struct_0(X42),u1_struct_0(X44))|(~v1_funct_1(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)))|~v1_funct_2(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),u1_struct_0(k1_tsep_1(X40,X43,X42)),u1_struct_0(X44))|~v5_pre_topc(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),k1_tsep_1(X40,X43,X42),X44)|~m1_subset_1(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X40,X43,X42)),u1_struct_0(X44)))))|~epred1_5(X44,X43,X42,X41,X40)))&(v5_pre_topc(k2_tmap_1(X40,X44,X41,X42),X42,X44)|(~v1_funct_1(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)))|~v1_funct_2(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),u1_struct_0(k1_tsep_1(X40,X43,X42)),u1_struct_0(X44))|~v5_pre_topc(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),k1_tsep_1(X40,X43,X42),X44)|~m1_subset_1(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X40,X43,X42)),u1_struct_0(X44)))))|~epred1_5(X44,X43,X42,X41,X40)))&(m1_subset_1(k2_tmap_1(X40,X44,X41,X42),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X44))))|(~v1_funct_1(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)))|~v1_funct_2(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),u1_struct_0(k1_tsep_1(X40,X43,X42)),u1_struct_0(X44))|~v5_pre_topc(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),k1_tsep_1(X40,X43,X42),X44)|~m1_subset_1(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X40,X43,X42)),u1_struct_0(X44)))))|~epred1_5(X44,X43,X42,X41,X40)))&((((v1_funct_1(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)))|(~v1_funct_1(k2_tmap_1(X40,X44,X41,X43))|~v1_funct_2(k2_tmap_1(X40,X44,X41,X43),u1_struct_0(X43),u1_struct_0(X44))|~v5_pre_topc(k2_tmap_1(X40,X44,X41,X43),X43,X44)|~m1_subset_1(k2_tmap_1(X40,X44,X41,X43),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X43),u1_struct_0(X44))))|~v1_funct_1(k2_tmap_1(X40,X44,X41,X42))|~v1_funct_2(k2_tmap_1(X40,X44,X41,X42),u1_struct_0(X42),u1_struct_0(X44))|~v5_pre_topc(k2_tmap_1(X40,X44,X41,X42),X42,X44)|~m1_subset_1(k2_tmap_1(X40,X44,X41,X42),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X44)))))|~epred1_5(X44,X43,X42,X41,X40))&(v1_funct_2(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),u1_struct_0(k1_tsep_1(X40,X43,X42)),u1_struct_0(X44))|(~v1_funct_1(k2_tmap_1(X40,X44,X41,X43))|~v1_funct_2(k2_tmap_1(X40,X44,X41,X43),u1_struct_0(X43),u1_struct_0(X44))|~v5_pre_topc(k2_tmap_1(X40,X44,X41,X43),X43,X44)|~m1_subset_1(k2_tmap_1(X40,X44,X41,X43),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X43),u1_struct_0(X44))))|~v1_funct_1(k2_tmap_1(X40,X44,X41,X42))|~v1_funct_2(k2_tmap_1(X40,X44,X41,X42),u1_struct_0(X42),u1_struct_0(X44))|~v5_pre_topc(k2_tmap_1(X40,X44,X41,X42),X42,X44)|~m1_subset_1(k2_tmap_1(X40,X44,X41,X42),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X44)))))|~epred1_5(X44,X43,X42,X41,X40)))&(v5_pre_topc(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),k1_tsep_1(X40,X43,X42),X44)|(~v1_funct_1(k2_tmap_1(X40,X44,X41,X43))|~v1_funct_2(k2_tmap_1(X40,X44,X41,X43),u1_struct_0(X43),u1_struct_0(X44))|~v5_pre_topc(k2_tmap_1(X40,X44,X41,X43),X43,X44)|~m1_subset_1(k2_tmap_1(X40,X44,X41,X43),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X43),u1_struct_0(X44))))|~v1_funct_1(k2_tmap_1(X40,X44,X41,X42))|~v1_funct_2(k2_tmap_1(X40,X44,X41,X42),u1_struct_0(X42),u1_struct_0(X44))|~v5_pre_topc(k2_tmap_1(X40,X44,X41,X42),X42,X44)|~m1_subset_1(k2_tmap_1(X40,X44,X41,X42),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X44)))))|~epred1_5(X44,X43,X42,X41,X40)))&(m1_subset_1(k2_tmap_1(X40,X44,X41,k1_tsep_1(X40,X43,X42)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X40,X43,X42)),u1_struct_0(X44))))|(~v1_funct_1(k2_tmap_1(X40,X44,X41,X43))|~v1_funct_2(k2_tmap_1(X40,X44,X41,X43),u1_struct_0(X43),u1_struct_0(X44))|~v5_pre_topc(k2_tmap_1(X40,X44,X41,X43),X43,X44)|~m1_subset_1(k2_tmap_1(X40,X44,X41,X43),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X43),u1_struct_0(X44))))|~v1_funct_1(k2_tmap_1(X40,X44,X41,X42))|~v1_funct_2(k2_tmap_1(X40,X44,X41,X42),u1_struct_0(X42),u1_struct_0(X44))|~v5_pre_topc(k2_tmap_1(X40,X44,X41,X42),X42,X44)|~m1_subset_1(k2_tmap_1(X40,X44,X41,X42),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X44)))))|~epred1_5(X44,X43,X42,X41,X40)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_48])])])).
% 0.18/0.45  cnf(c_0_59, negated_conjecture, (k2_tmap_1(esk1_0,esk2_0,esk3_0,X1)=esk3_0|~m1_pre_topc(X1,esk1_0)|~v4_relat_1(esk3_0,u1_struct_0(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])])).
% 0.18/0.45  cnf(c_0_60, negated_conjecture, (v4_relat_1(esk3_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_52, c_0_15])).
% 0.18/0.45  fof(c_0_61, plain, ![X34]:(~l1_pre_topc(X34)|m1_pre_topc(X34,X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.18/0.45  cnf(c_0_62, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|epred1_5(X2,X3,X4,X5,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~r4_tsep_1(X1,X3,X4)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.18/0.45  cnf(c_0_63, negated_conjecture, (~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55])]), c_0_56])])).
% 0.18/0.45  cnf(c_0_64, plain, (m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.45  cnf(c_0_65, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))|~l1_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_15]), c_0_16]), c_0_17])])).
% 0.18/0.45  cnf(c_0_66, plain, (v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)|~v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)))|~v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),u1_struct_0(k1_tsep_1(X1,X5,X4)),u1_struct_0(X2))|~v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),k1_tsep_1(X1,X5,X4),X2)|~m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X5,X4)),u1_struct_0(X2))))|~epred1_5(X2,X5,X4,X3,X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.18/0.45  cnf(c_0_67, negated_conjecture, (esk1_0=k1_tsep_1(esk1_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.45  cnf(c_0_68, negated_conjecture, (k2_tmap_1(esk1_0,esk2_0,esk3_0,esk1_0)=esk3_0|~m1_pre_topc(esk1_0,esk1_0)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.18/0.45  cnf(c_0_69, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.18/0.45  cnf(c_0_70, negated_conjecture, (epred1_5(esk2_0,X1,X2,esk3_0,esk1_0)|v2_struct_0(X1)|v2_struct_0(X2)|~r4_tsep_1(esk1_0,X1,X2)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_15]), c_0_16]), c_0_37]), c_0_38]), c_0_21]), c_0_24]), c_0_17])]), c_0_39]), c_0_40])).
% 0.18/0.45  cnf(c_0_71, negated_conjecture, (r4_tsep_1(esk1_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.45  cnf(c_0_72, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.45  cnf(c_0_73, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.45  cnf(c_0_74, negated_conjecture, (~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~l1_struct_0(esk5_0)|~l1_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_16]), c_0_17]), c_0_15])]), c_0_65])).
% 0.18/0.45  cnf(c_0_75, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk5_0),esk5_0,X1)|~epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)|~v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk1_0),esk1_0,X1)|~v1_funct_2(k2_tmap_1(esk1_0,X1,X2,esk1_0),u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(k2_tmap_1(esk1_0,X1,X2,esk1_0))|~m1_subset_1(k2_tmap_1(esk1_0,X1,X2,esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.18/0.45  cnf(c_0_76, negated_conjecture, (k2_tmap_1(esk1_0,esk2_0,esk3_0,esk1_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_24])])).
% 0.18/0.45  cnf(c_0_77, negated_conjecture, (epred1_5(esk2_0,esk4_0,esk5_0,esk3_0,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_32]), c_0_33])]), c_0_72]), c_0_73])).
% 0.18/0.45  cnf(c_0_78, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.45  cnf(c_0_79, plain, (v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)|~v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)))|~v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))|~v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_tsep_1(X1,X4,X5),X2)|~m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))))|~epred1_5(X2,X4,X5,X3,X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.18/0.45  cnf(c_0_80, negated_conjecture, (~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~l1_struct_0(esk5_0)|~l1_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(esk4_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_64]), c_0_16]), c_0_17]), c_0_15])]), c_0_65])).
% 0.18/0.45  cnf(c_0_81, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77]), c_0_16]), c_0_17]), c_0_15])]), c_0_78])).
% 0.18/0.45  cnf(c_0_82, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk4_0),esk4_0,X1)|~epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)|~v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk1_0),esk1_0,X1)|~v1_funct_2(k2_tmap_1(esk1_0,X1,X2,esk1_0),u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(k2_tmap_1(esk1_0,X1,X2,esk1_0))|~m1_subset_1(k2_tmap_1(esk1_0,X1,X2,esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))), inference(spm,[status(thm)],[c_0_79, c_0_67])).
% 0.18/0.45  cnf(c_0_83, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.45  cnf(c_0_84, negated_conjecture, (~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~l1_struct_0(esk5_0)|~l1_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_81])])).
% 0.18/0.45  cnf(c_0_85, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_76]), c_0_77]), c_0_16]), c_0_17]), c_0_15])]), c_0_83])).
% 0.18/0.45  cnf(c_0_86, negated_conjecture, (~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~l1_struct_0(esk5_0)|~l1_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_85])])).
% 0.18/0.45  cnf(c_0_87, negated_conjecture, (~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~l1_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_20]), c_0_46])])).
% 0.18/0.45  cnf(c_0_88, negated_conjecture, (~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~l1_struct_0(esk2_0)|~l1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_20]), c_0_47])])).
% 0.18/0.45  cnf(c_0_89, negated_conjecture, (~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_20]), c_0_24])])).
% 0.18/0.45  cnf(c_0_90, plain, (v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_tsep_1(X1,X4,X5),X2)|~v1_funct_1(k2_tmap_1(X1,X2,X3,X4))|~v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))|~v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)|~m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~v1_funct_1(k2_tmap_1(X1,X2,X3,X5))|~v1_funct_2(k2_tmap_1(X1,X2,X3,X5),u1_struct_0(X5),u1_struct_0(X2))|~v5_pre_topc(k2_tmap_1(X1,X2,X3,X5),X5,X2)|~m1_subset_1(k2_tmap_1(X1,X2,X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2))))|~epred1_5(X2,X4,X5,X3,X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.18/0.45  cnf(c_0_91, negated_conjecture, (m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.45  cnf(c_0_92, negated_conjecture, (~v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_20]), c_0_21])])).
% 0.18/0.45  cnf(c_0_93, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.45  cnf(c_0_94, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.45  cnf(c_0_95, negated_conjecture, (m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.45  cnf(c_0_96, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk1_0),esk1_0,X1)|~epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)|~v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk5_0),esk5_0,X1)|~v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk4_0),esk4_0,X1)|~v1_funct_2(k2_tmap_1(esk1_0,X1,X2,esk5_0),u1_struct_0(esk5_0),u1_struct_0(X1))|~v1_funct_2(k2_tmap_1(esk1_0,X1,X2,esk4_0),u1_struct_0(esk4_0),u1_struct_0(X1))|~v1_funct_1(k2_tmap_1(esk1_0,X1,X2,esk5_0))|~v1_funct_1(k2_tmap_1(esk1_0,X1,X2,esk4_0))|~m1_subset_1(k2_tmap_1(esk1_0,X1,X2,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))|~m1_subset_1(k2_tmap_1(esk1_0,X1,X2,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1))))), inference(spm,[status(thm)],[c_0_90, c_0_67])).
% 0.18/0.45  cnf(c_0_97, negated_conjecture, (m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[c_0_91, c_0_92])).
% 0.18/0.45  cnf(c_0_98, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[c_0_93, c_0_92])).
% 0.18/0.45  cnf(c_0_99, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[c_0_94, c_0_92])).
% 0.18/0.45  cnf(c_0_100, negated_conjecture, (m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[c_0_95, c_0_92])).
% 0.18/0.45  cnf(c_0_101, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_76]), c_0_77]), c_0_81]), c_0_85]), c_0_98]), c_0_99]), c_0_55]), c_0_56]), c_0_100])]), c_0_92]), ['proof']).
% 0.18/0.45  # SZS output end CNFRefutation
% 0.18/0.45  # Proof object total steps             : 102
% 0.18/0.45  # Proof object clause steps            : 75
% 0.18/0.45  # Proof object formula steps           : 27
% 0.18/0.45  # Proof object conjectures             : 63
% 0.18/0.45  # Proof object clause conjectures      : 60
% 0.18/0.45  # Proof object formula conjectures     : 3
% 0.18/0.45  # Proof object initial clauses used    : 37
% 0.18/0.45  # Proof object initial formulas used   : 11
% 0.18/0.45  # Proof object generating inferences   : 30
% 0.18/0.45  # Proof object simplifying inferences  : 101
% 0.18/0.45  # Training examples: 0 positive, 0 negative
% 0.18/0.45  # Parsed axioms                        : 11
% 0.18/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.45  # Initial clauses                      : 73
% 0.18/0.45  # Removed in clause preprocessing      : 0
% 0.18/0.45  # Initial clauses in saturation        : 73
% 0.18/0.45  # Processed clauses                    : 600
% 0.18/0.45  # ...of these trivial                  : 28
% 0.18/0.45  # ...subsumed                          : 59
% 0.18/0.45  # ...remaining for further processing  : 513
% 0.18/0.45  # Other redundant clauses eliminated   : 0
% 0.18/0.45  # Clauses deleted for lack of memory   : 0
% 0.18/0.45  # Backward-subsumed                    : 103
% 0.18/0.45  # Backward-rewritten                   : 15
% 0.18/0.45  # Generated clauses                    : 698
% 0.18/0.45  # ...of the previous two non-trivial   : 628
% 0.18/0.45  # Contextual simplify-reflections      : 78
% 0.18/0.45  # Paramodulations                      : 639
% 0.18/0.45  # Factorizations                       : 0
% 0.18/0.45  # Equation resolutions                 : 0
% 0.18/0.45  # Propositional unsat checks           : 0
% 0.18/0.45  #    Propositional check models        : 0
% 0.18/0.45  #    Propositional check unsatisfiable : 0
% 0.18/0.45  #    Propositional clauses             : 0
% 0.18/0.45  #    Propositional clauses after purity: 0
% 0.18/0.45  #    Propositional unsat core size     : 0
% 0.18/0.45  #    Propositional preprocessing time  : 0.000
% 0.18/0.45  #    Propositional encoding time       : 0.000
% 0.18/0.45  #    Propositional solver time         : 0.000
% 0.18/0.45  #    Success case prop preproc time    : 0.000
% 0.18/0.45  #    Success case prop encoding time   : 0.000
% 0.18/0.45  #    Success case prop solver time     : 0.000
% 0.18/0.45  # Current number of processed clauses  : 287
% 0.18/0.45  #    Positive orientable unit clauses  : 93
% 0.18/0.45  #    Positive unorientable unit clauses: 0
% 0.18/0.45  #    Negative unit clauses             : 5
% 0.18/0.45  #    Non-unit-clauses                  : 189
% 0.18/0.45  # Current number of unprocessed clauses: 138
% 0.18/0.45  # ...number of literals in the above   : 1436
% 0.18/0.45  # Current number of archived formulas  : 0
% 0.18/0.45  # Current number of archived clauses   : 226
% 0.18/0.45  # Clause-clause subsumption calls (NU) : 22530
% 0.18/0.45  # Rec. Clause-clause subsumption calls : 3410
% 0.18/0.45  # Non-unit clause-clause subsumptions  : 224
% 0.18/0.45  # Unit Clause-clause subsumption calls : 805
% 0.18/0.45  # Rewrite failures with RHS unbound    : 0
% 0.18/0.45  # BW rewrite match attempts            : 140
% 0.18/0.45  # BW rewrite match successes           : 8
% 0.18/0.45  # Condensation attempts                : 0
% 0.18/0.45  # Condensation successes               : 0
% 0.18/0.45  # Termbank termtop insertions          : 46318
% 0.18/0.45  
% 0.18/0.45  # -------------------------------------------------
% 0.18/0.45  # User time                : 0.110 s
% 0.18/0.45  # System time              : 0.006 s
% 0.18/0.45  # Total time               : 0.116 s
% 0.18/0.45  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
