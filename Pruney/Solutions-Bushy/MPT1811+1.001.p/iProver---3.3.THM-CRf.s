%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1811+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:30 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :  190 (1295 expanded)
%              Number of clauses        :  119 ( 235 expanded)
%              Number of leaves         :   12 ( 468 expanded)
%              Depth                    :   19
%              Number of atoms          : 1527 (43047 expanded)
%              Number of equality atoms :  145 ( 227 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal clause size      :   78 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f43,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( sP0(X1,X3,X4,X2,X0)
    <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
        & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
        & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
        & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f55,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( sP0(X1,X3,X4,X2,X0)
        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
      & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
        | ~ sP0(X1,X3,X4,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f56,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( sP0(X1,X3,X4,X2,X0)
        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
      & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
        | ~ sP0(X1,X3,X4,X2,X0) ) ) ),
    inference(flattening,[],[f55])).

fof(f57,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
        | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
        | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
        | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
        | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
        | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
        | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) )
      & ( ( m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
          & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
          & m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
          & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
          & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
          & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f56])).

fof(f98,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f94,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f92,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & m1_pre_topc(X2,X0)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_borsuk_1(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_borsuk_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_borsuk_1(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(X4) )
                        <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                            & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <~> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_borsuk_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <~> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_borsuk_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f58,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))
                        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                        | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        | ~ v1_funct_1(X4) )
                      & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
                        | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_borsuk_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f59,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))
                        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                        | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        | ~ v1_funct_1(X4) )
                      & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
                        | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_borsuk_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
            | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
            | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
            | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
            | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
            | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
            | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
            | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))
            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
            | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            | ~ v1_funct_1(X4) )
          & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
              & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
              & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
              & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
              & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
              & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
              & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
              & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
            | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
              & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
              & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
              & v1_funct_1(X4) ) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,sK9),X3,X1)
          | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,sK9),u1_struct_0(X3),u1_struct_0(X1))
          | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,sK9))
          | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,sK9),X2,X1)
          | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,sK9),u1_struct_0(X2),u1_struct_0(X1))
          | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,sK9))
          | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          | ~ v5_pre_topc(sK9,k1_tsep_1(X0,X2,X3),X1)
          | ~ v1_funct_2(sK9,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          | ~ v1_funct_1(sK9) )
        & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,sK9),X3,X1)
            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,sK9),u1_struct_0(X3),u1_struct_0(X1))
            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,sK9))
            & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,sK9),X2,X1)
            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,sK9),u1_struct_0(X2),u1_struct_0(X1))
            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,sK9)) )
          | ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            & v5_pre_topc(sK9,k1_tsep_1(X0,X2,X3),X1)
            & v1_funct_2(sK9,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            & v1_funct_1(sK9) ) )
        & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(sK9,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))
                | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                | ~ v1_funct_1(X4) )
              & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                  & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                  & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                  & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                  & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
                | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                  & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                  & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                  & v1_funct_1(X4) ) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
              & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X0)
          & v1_borsuk_1(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK8),sK8,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(X1))))
              | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK8),sK8,X4),sK8,X1)
              | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK8),sK8,X4),u1_struct_0(sK8),u1_struct_0(X1))
              | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK8),sK8,X4))
              | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK8),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
              | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK8),X2,X4),X2,X1)
              | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK8),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
              | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK8),X2,X4))
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,sK8)),u1_struct_0(X1))))
              | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,sK8),X1)
              | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,sK8)),u1_struct_0(X1))
              | ~ v1_funct_1(X4) )
            & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK8),sK8,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(X1))))
                & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK8),sK8,X4),sK8,X1)
                & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK8),sK8,X4),u1_struct_0(sK8),u1_struct_0(X1))
                & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK8),sK8,X4))
                & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK8),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK8),X2,X4),X2,X1)
                & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK8),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,sK8),X2,X4)) )
              | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,sK8)),u1_struct_0(X1))))
                & v5_pre_topc(X4,k1_tsep_1(X0,X2,sK8),X1)
                & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,sK8)),u1_struct_0(X1))
                & v1_funct_1(X4) ) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,sK8)),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,sK8)),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK8,X0)
        & v1_borsuk_1(sK8,X0)
        & ~ v2_struct_0(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                    | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                    | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                    | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                    | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                    | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))
                    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                    | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                    | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                    | ~ v1_funct_1(X4) )
                  & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                      & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                      & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                      & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
                    | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                      & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      & v1_funct_1(X4) ) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                  & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,X0)
              & v1_borsuk_1(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & v1_borsuk_1(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK7,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK7,X3),X3,X4),X3,X1)
                  | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK7,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                  | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK7,X3),X3,X4))
                  | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK7,X3),sK7,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X1))))
                  | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK7,X3),sK7,X4),sK7,X1)
                  | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK7,X3),sK7,X4),u1_struct_0(sK7),u1_struct_0(X1))
                  | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK7,X3),sK7,X4))
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK7,X3)),u1_struct_0(X1))))
                  | ~ v5_pre_topc(X4,k1_tsep_1(X0,sK7,X3),X1)
                  | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,sK7,X3)),u1_struct_0(X1))
                  | ~ v1_funct_1(X4) )
                & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK7,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK7,X3),X3,X4),X3,X1)
                    & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK7,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                    & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK7,X3),X3,X4))
                    & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK7,X3),sK7,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X1))))
                    & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK7,X3),sK7,X4),sK7,X1)
                    & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK7,X3),sK7,X4),u1_struct_0(sK7),u1_struct_0(X1))
                    & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,sK7,X3),sK7,X4)) )
                  | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK7,X3)),u1_struct_0(X1))))
                    & v5_pre_topc(X4,k1_tsep_1(X0,sK7,X3),X1)
                    & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,sK7,X3)),u1_struct_0(X1))
                    & v1_funct_1(X4) ) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK7,X3)),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,sK7,X3)),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & v1_borsuk_1(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK7,X0)
        & v1_borsuk_1(sK7,X0)
        & ~ v2_struct_0(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))
                        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                        | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        | ~ v1_funct_1(X4) )
                      & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
                        | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_borsuk_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ( ~ m1_subset_1(k3_tmap_1(X0,sK6,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK6))))
                      | ~ v5_pre_topc(k3_tmap_1(X0,sK6,k1_tsep_1(X0,X2,X3),X3,X4),X3,sK6)
                      | ~ v1_funct_2(k3_tmap_1(X0,sK6,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(sK6))
                      | ~ v1_funct_1(k3_tmap_1(X0,sK6,k1_tsep_1(X0,X2,X3),X3,X4))
                      | ~ m1_subset_1(k3_tmap_1(X0,sK6,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK6))))
                      | ~ v5_pre_topc(k3_tmap_1(X0,sK6,k1_tsep_1(X0,X2,X3),X2,X4),X2,sK6)
                      | ~ v1_funct_2(k3_tmap_1(X0,sK6,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(sK6))
                      | ~ v1_funct_1(k3_tmap_1(X0,sK6,k1_tsep_1(X0,X2,X3),X2,X4))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK6))))
                      | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),sK6)
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK6))
                      | ~ v1_funct_1(X4) )
                    & ( ( m1_subset_1(k3_tmap_1(X0,sK6,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK6))))
                        & v5_pre_topc(k3_tmap_1(X0,sK6,k1_tsep_1(X0,X2,X3),X3,X4),X3,sK6)
                        & v1_funct_2(k3_tmap_1(X0,sK6,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(sK6))
                        & v1_funct_1(k3_tmap_1(X0,sK6,k1_tsep_1(X0,X2,X3),X3,X4))
                        & m1_subset_1(k3_tmap_1(X0,sK6,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK6))))
                        & v5_pre_topc(k3_tmap_1(X0,sK6,k1_tsep_1(X0,X2,X3),X2,X4),X2,sK6)
                        & v1_funct_2(k3_tmap_1(X0,sK6,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(sK6))
                        & v1_funct_1(k3_tmap_1(X0,sK6,k1_tsep_1(X0,X2,X3),X2,X4)) )
                      | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK6))))
                        & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),sK6)
                        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK6))
                        & v1_funct_1(X4) ) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK6))))
                    & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK6))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & v1_borsuk_1(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & v1_borsuk_1(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK6)
        & v2_pre_topc(sK6)
        & ~ v2_struct_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          | ~ v1_funct_1(X4) )
                        & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                            & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
                          | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(X4) ) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X0)
                    & v1_borsuk_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & v1_borsuk_1(X2,X0)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k3_tmap_1(sK5,X1,k1_tsep_1(sK5,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(sK5,X1,k1_tsep_1(sK5,X2,X3),X3,X4),X3,X1)
                        | ~ v1_funct_2(k3_tmap_1(sK5,X1,k1_tsep_1(sK5,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(sK5,X1,k1_tsep_1(sK5,X2,X3),X3,X4))
                        | ~ m1_subset_1(k3_tmap_1(sK5,X1,k1_tsep_1(sK5,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(sK5,X1,k1_tsep_1(sK5,X2,X3),X2,X4),X2,X1)
                        | ~ v1_funct_2(k3_tmap_1(sK5,X1,k1_tsep_1(sK5,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(sK5,X1,k1_tsep_1(sK5,X2,X3),X2,X4))
                        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,X2,X3)),u1_struct_0(X1))))
                        | ~ v5_pre_topc(X4,k1_tsep_1(sK5,X2,X3),X1)
                        | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK5,X2,X3)),u1_struct_0(X1))
                        | ~ v1_funct_1(X4) )
                      & ( ( m1_subset_1(k3_tmap_1(sK5,X1,k1_tsep_1(sK5,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(sK5,X1,k1_tsep_1(sK5,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(sK5,X1,k1_tsep_1(sK5,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(sK5,X1,k1_tsep_1(sK5,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(sK5,X1,k1_tsep_1(sK5,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(sK5,X1,k1_tsep_1(sK5,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(sK5,X1,k1_tsep_1(sK5,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(sK5,X1,k1_tsep_1(sK5,X2,X3),X2,X4)) )
                        | ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(sK5,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK5,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,X2,X3)),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK5,X2,X3)),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK5)
                  & v1_borsuk_1(X3,sK5)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK5)
              & v1_borsuk_1(X2,sK5)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,
    ( ( ~ m1_subset_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
      | ~ v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),sK8,sK6)
      | ~ v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),u1_struct_0(sK8),u1_struct_0(sK6))
      | ~ v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9))
      | ~ m1_subset_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
      | ~ v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),sK7,sK6)
      | ~ v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),u1_struct_0(sK7),u1_struct_0(sK6))
      | ~ v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9))
      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))))
      | ~ v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6)
      | ~ v1_funct_2(sK9,u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))
      | ~ v1_funct_1(sK9) )
    & ( ( m1_subset_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
        & v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),sK8,sK6)
        & v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),u1_struct_0(sK8),u1_struct_0(sK6))
        & v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9))
        & m1_subset_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
        & v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),sK7,sK6)
        & v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),u1_struct_0(sK7),u1_struct_0(sK6))
        & v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9)) )
      | ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))))
        & v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6)
        & v1_funct_2(sK9,u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))
        & v1_funct_1(sK9) ) )
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))))
    & v1_funct_2(sK9,u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))
    & v1_funct_1(sK9)
    & m1_pre_topc(sK8,sK5)
    & v1_borsuk_1(sK8,sK5)
    & ~ v2_struct_0(sK8)
    & m1_pre_topc(sK7,sK5)
    & v1_borsuk_1(sK7,sK5)
    & ~ v2_struct_0(sK7)
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6)
    & ~ v2_struct_0(sK6)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f59,f64,f63,f62,f61,f60])).

fof(f117,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6)))) ),
    inference(cnf_transformation,[],[f65])).

fof(f44,plain,(
    ! [X0,X2,X4,X3,X1] :
      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          & v1_funct_1(X4) )
      <=> sP0(X1,X3,X4,X2,X0) )
      | ~ sP1(X0,X2,X4,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f52,plain,(
    ! [X0,X2,X4,X3,X1] :
      ( ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            & v1_funct_1(X4) )
          | ~ sP0(X1,X3,X4,X2,X0) )
        & ( sP0(X1,X3,X4,X2,X0)
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          | ~ v1_funct_1(X4) ) )
      | ~ sP1(X0,X2,X4,X3,X1) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f53,plain,(
    ! [X0,X2,X4,X3,X1] :
      ( ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            & v1_funct_1(X4) )
          | ~ sP0(X1,X3,X4,X2,X0) )
        & ( sP0(X1,X3,X4,X2,X0)
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          | ~ v1_funct_1(X4) ) )
      | ~ sP1(X0,X2,X4,X3,X1) ) ),
    inference(flattening,[],[f52])).

fof(f54,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
            & v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
            & v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
            & v1_funct_1(X2) )
          | ~ sP0(X4,X3,X2,X1,X0) )
        & ( sP0(X4,X3,X2,X1,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
          | ~ v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
          | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
          | ~ v1_funct_1(X2) ) )
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f53])).

fof(f87,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X4,X3,X2,X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
      | ~ v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
      | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
      | ~ v1_funct_1(X2)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f103,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f65])).

fof(f104,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f65])).

fof(f105,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f65])).

fof(f106,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f65])).

fof(f107,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f65])).

fof(f108,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f65])).

fof(f109,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f65])).

fof(f110,plain,(
    v1_borsuk_1(sK7,sK5) ),
    inference(cnf_transformation,[],[f65])).

fof(f111,plain,(
    m1_pre_topc(sK7,sK5) ),
    inference(cnf_transformation,[],[f65])).

fof(f112,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f65])).

fof(f113,plain,(
    v1_borsuk_1(sK8,sK5) ),
    inference(cnf_transformation,[],[f65])).

fof(f114,plain,(
    m1_pre_topc(sK8,sK5) ),
    inference(cnf_transformation,[],[f65])).

fof(f115,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f65])).

fof(f116,plain,(
    v1_funct_2(sK9,u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f65])).

fof(f120,plain,
    ( v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9))
    | v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6) ),
    inference(cnf_transformation,[],[f65])).

fof(f124,plain,
    ( v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),u1_struct_0(sK7),u1_struct_0(sK6))
    | v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6) ),
    inference(cnf_transformation,[],[f65])).

fof(f128,plain,
    ( v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),sK7,sK6)
    | v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6) ),
    inference(cnf_transformation,[],[f65])).

fof(f132,plain,
    ( m1_subset_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
    | v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6) ),
    inference(cnf_transformation,[],[f65])).

fof(f136,plain,
    ( v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9))
    | v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6) ),
    inference(cnf_transformation,[],[f65])).

fof(f140,plain,
    ( v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),u1_struct_0(sK8),u1_struct_0(sK6))
    | v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6) ),
    inference(cnf_transformation,[],[f65])).

fof(f144,plain,
    ( v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),sK8,sK6)
    | v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6) ),
    inference(cnf_transformation,[],[f65])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_borsuk_1(X1,X0) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_borsuk_1(X2,X0) )
             => r4_tsep_1(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_tsep_1(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_borsuk_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_tsep_1(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_borsuk_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_borsuk_1(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( r4_tsep_1(X0,X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(X4) )
                        <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                            & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( sP1(X0,X2,X4,X3,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f38,f44,f43])).

fof(f101,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X0,X2,X4,X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ r4_tsep_1(X0,X2,X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f148,plain,
    ( m1_subset_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
    | v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6) ),
    inference(cnf_transformation,[],[f65])).

fof(f100,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f93,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f99,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f95,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f150,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
    | ~ v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),sK8,sK6)
    | ~ v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),u1_struct_0(sK8),u1_struct_0(sK6))
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9))
    | ~ m1_subset_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
    | ~ v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),sK7,sK6)
    | ~ v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))))
    | ~ v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6)
    | ~ v1_funct_2(sK9,u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))
    | ~ v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f65])).

fof(f90,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_28,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2517,plain,
    ( ~ sP0(X0_57,X1_57,X0_56,X2_57,X3_57)
    | v5_pre_topc(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X1_57,X0_56),X1_57,X0_57) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_13371,plain,
    ( ~ sP0(sK6,sK8,sK9,sK7,sK5)
    | v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),sK8,sK6) ),
    inference(instantiation,[status(thm)],[c_2517])).

cnf(c_32,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2513,plain,
    ( ~ sP0(X0_57,X1_57,X0_56,X2_57,X3_57)
    | v5_pre_topc(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X2_57,X0_56),X2_57,X0_57) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_13374,plain,
    ( ~ sP0(sK6,sK8,sK9,sK7,sK5)
    | v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),sK7,sK6) ),
    inference(instantiation,[status(thm)],[c_2513])).

cnf(c_34,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2511,plain,
    ( ~ sP0(X0_57,X1_57,X0_56,X2_57,X3_57)
    | v1_funct_1(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X2_57,X0_56)) ),
    inference(subtyping,[status(esa)],[c_34])).

cnf(c_13377,plain,
    ( ~ sP0(sK6,sK8,sK9,sK7,sK5)
    | v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_2511])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X4,X3)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2536,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(X0_57),u1_struct_0(X1_57))
    | v1_funct_2(k3_tmap_1(X2_57,X1_57,X0_57,X3_57,X0_56),u1_struct_0(X3_57),u1_struct_0(X1_57))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
    | ~ m1_pre_topc(X0_57,X2_57)
    | ~ m1_pre_topc(X3_57,X2_57)
    | ~ v1_funct_1(X0_56)
    | v2_struct_0(X1_57)
    | v2_struct_0(X2_57)
    | ~ v2_pre_topc(X2_57)
    | ~ v2_pre_topc(X1_57)
    | ~ l1_pre_topc(X1_57)
    | ~ l1_pre_topc(X2_57) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_4947,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(X0_57))
    | v1_funct_2(k3_tmap_1(sK5,X0_57,k1_tsep_1(sK5,sK7,sK8),X1_57,X0_56),u1_struct_0(X1_57),u1_struct_0(X0_57))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(X0_57))))
    | ~ m1_pre_topc(X1_57,sK5)
    | ~ m1_pre_topc(k1_tsep_1(sK5,sK7,sK8),sK5)
    | ~ v1_funct_1(X0_56)
    | v2_struct_0(X0_57)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(X0_57)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(X0_57)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_2536])).

cnf(c_10504,plain,
    ( v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),X0_57,sK9),u1_struct_0(X0_57),u1_struct_0(sK6))
    | ~ v1_funct_2(sK9,u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))))
    | ~ m1_pre_topc(X0_57,sK5)
    | ~ m1_pre_topc(k1_tsep_1(sK5,sK7,sK8),sK5)
    | ~ v1_funct_1(sK9)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK6)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_4947])).

cnf(c_11824,plain,
    ( v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),u1_struct_0(sK8),u1_struct_0(sK6))
    | ~ v1_funct_2(sK9,u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))))
    | ~ m1_pre_topc(k1_tsep_1(sK5,sK7,sK8),sK5)
    | ~ m1_pre_topc(sK8,sK5)
    | ~ v1_funct_1(sK9)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK6)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_10504])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X4,X3)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_tmap_1(X3,X2,X1,X4,X0))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2535,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(X0_57),u1_struct_0(X1_57))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
    | ~ m1_pre_topc(X0_57,X2_57)
    | ~ m1_pre_topc(X3_57,X2_57)
    | ~ v1_funct_1(X0_56)
    | v1_funct_1(k3_tmap_1(X2_57,X1_57,X0_57,X3_57,X0_56))
    | v2_struct_0(X1_57)
    | v2_struct_0(X2_57)
    | ~ v2_pre_topc(X2_57)
    | ~ v2_pre_topc(X1_57)
    | ~ l1_pre_topc(X1_57)
    | ~ l1_pre_topc(X2_57) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_4948,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(X0_57))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(X0_57))))
    | ~ m1_pre_topc(X1_57,sK5)
    | ~ m1_pre_topc(k1_tsep_1(sK5,sK7,sK8),sK5)
    | ~ v1_funct_1(X0_56)
    | v1_funct_1(k3_tmap_1(sK5,X0_57,k1_tsep_1(sK5,sK7,sK8),X1_57,X0_56))
    | v2_struct_0(X0_57)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(X0_57)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(X0_57)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_2535])).

cnf(c_10233,plain,
    ( ~ v1_funct_2(sK9,u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))))
    | ~ m1_pre_topc(X0_57,sK5)
    | ~ m1_pre_topc(k1_tsep_1(sK5,sK7,sK8),sK5)
    | v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),X0_57,sK9))
    | ~ v1_funct_1(sK9)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK6)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_4948])).

cnf(c_11790,plain,
    ( ~ v1_funct_2(sK9,u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))))
    | ~ m1_pre_topc(k1_tsep_1(sK5,sK7,sK8),sK5)
    | ~ m1_pre_topc(sK8,sK5)
    | v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9))
    | ~ v1_funct_1(sK9)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK6)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_10233])).

cnf(c_70,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6)))) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_2500,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6)))) ),
    inference(subtyping,[status(esa)],[c_70])).

cnf(c_3690,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2500])).

cnf(c_25,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | sP0(X4,X3,X2,X1,X0)
    | ~ v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
    | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2520,plain,
    ( ~ sP1(X0_57,X1_57,X0_56,X2_57,X3_57)
    | sP0(X3_57,X2_57,X0_56,X1_57,X0_57)
    | ~ v5_pre_topc(X0_56,k1_tsep_1(X0_57,X1_57,X2_57),X3_57)
    | ~ v1_funct_2(X0_56,u1_struct_0(k1_tsep_1(X0_57,X1_57,X2_57)),u1_struct_0(X3_57))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_57,X1_57,X2_57)),u1_struct_0(X3_57))))
    | ~ v1_funct_1(X0_56) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_3670,plain,
    ( sP1(X0_57,X1_57,X0_56,X2_57,X3_57) != iProver_top
    | sP0(X3_57,X2_57,X0_56,X1_57,X0_57) = iProver_top
    | v5_pre_topc(X0_56,k1_tsep_1(X0_57,X1_57,X2_57),X3_57) != iProver_top
    | v1_funct_2(X0_56,u1_struct_0(k1_tsep_1(X0_57,X1_57,X2_57)),u1_struct_0(X3_57)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_57,X1_57,X2_57)),u1_struct_0(X3_57)))) != iProver_top
    | v1_funct_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2520])).

cnf(c_9368,plain,
    ( sP1(sK5,sK7,sK9,sK8,sK6) != iProver_top
    | sP0(sK6,sK8,sK9,sK7,sK5) = iProver_top
    | v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6)) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_3690,c_3670])).

cnf(c_84,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_85,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_84])).

cnf(c_83,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_86,plain,
    ( v2_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_83])).

cnf(c_82,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_87,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_82])).

cnf(c_81,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_88,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_81])).

cnf(c_80,negated_conjecture,
    ( v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_89,plain,
    ( v2_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_80])).

cnf(c_79,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_90,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_79])).

cnf(c_78,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_91,plain,
    ( v2_struct_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_78])).

cnf(c_77,negated_conjecture,
    ( v1_borsuk_1(sK7,sK5) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_92,plain,
    ( v1_borsuk_1(sK7,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_77])).

cnf(c_76,negated_conjecture,
    ( m1_pre_topc(sK7,sK5) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_93,plain,
    ( m1_pre_topc(sK7,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_76])).

cnf(c_75,negated_conjecture,
    ( ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_94,plain,
    ( v2_struct_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_75])).

cnf(c_74,negated_conjecture,
    ( v1_borsuk_1(sK8,sK5) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_95,plain,
    ( v1_borsuk_1(sK8,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_74])).

cnf(c_73,negated_conjecture,
    ( m1_pre_topc(sK8,sK5) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_96,plain,
    ( m1_pre_topc(sK8,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_73])).

cnf(c_72,negated_conjecture,
    ( v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_97,plain,
    ( v1_funct_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_72])).

cnf(c_71,negated_conjecture,
    ( v1_funct_2(sK9,u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_98,plain,
    ( v1_funct_2(sK9,u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_71])).

cnf(c_99,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_70])).

cnf(c_67,negated_conjecture,
    ( v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6)
    | v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9)) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_102,plain,
    ( v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6) = iProver_top
    | v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_67])).

cnf(c_63,negated_conjecture,
    ( v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6)
    | v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),u1_struct_0(sK7),u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_106,plain,
    ( v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6) = iProver_top
    | v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),u1_struct_0(sK7),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_63])).

cnf(c_59,negated_conjecture,
    ( v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),sK7,sK6)
    | v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_110,plain,
    ( v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),sK7,sK6) = iProver_top
    | v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59])).

cnf(c_55,negated_conjecture,
    ( v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6)
    | m1_subset_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_114,plain,
    ( v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6) = iProver_top
    | m1_subset_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_51,negated_conjecture,
    ( v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6)
    | v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9)) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_118,plain,
    ( v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6) = iProver_top
    | v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_47,negated_conjecture,
    ( v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6)
    | v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),u1_struct_0(sK8),u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_122,plain,
    ( v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6) = iProver_top
    | v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),u1_struct_0(sK8),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_43,negated_conjecture,
    ( v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),sK8,sK6)
    | v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6) ),
    inference(cnf_transformation,[],[f144])).

cnf(c_126,plain,
    ( v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),sK8,sK6) = iProver_top
    | v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_36,plain,
    ( r4_tsep_1(X0,X1,X2)
    | ~ v1_borsuk_1(X2,X0)
    | ~ v1_borsuk_1(X1,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_pre_topc(X2,X0)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_2509,plain,
    ( r4_tsep_1(X0_57,X1_57,X2_57)
    | ~ v1_borsuk_1(X2_57,X0_57)
    | ~ v1_borsuk_1(X1_57,X0_57)
    | ~ m1_pre_topc(X1_57,X0_57)
    | ~ m1_pre_topc(X2_57,X0_57)
    | v2_struct_0(X0_57)
    | ~ v2_pre_topc(X0_57)
    | ~ l1_pre_topc(X0_57) ),
    inference(subtyping,[status(esa)],[c_36])).

cnf(c_4471,plain,
    ( r4_tsep_1(sK5,X0_57,sK8)
    | ~ v1_borsuk_1(X0_57,sK5)
    | ~ v1_borsuk_1(sK8,sK5)
    | ~ m1_pre_topc(X0_57,sK5)
    | ~ m1_pre_topc(sK8,sK5)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_2509])).

cnf(c_4691,plain,
    ( r4_tsep_1(sK5,sK7,sK8)
    | ~ v1_borsuk_1(sK8,sK5)
    | ~ v1_borsuk_1(sK7,sK5)
    | ~ m1_pre_topc(sK8,sK5)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_4471])).

cnf(c_4692,plain,
    ( r4_tsep_1(sK5,sK7,sK8) = iProver_top
    | v1_borsuk_1(sK8,sK5) != iProver_top
    | v1_borsuk_1(sK7,sK5) != iProver_top
    | m1_pre_topc(sK8,sK5) != iProver_top
    | m1_pre_topc(sK7,sK5) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4691])).

cnf(c_35,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ r4_tsep_1(X0,X1,X3)
    | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_pre_topc(X3,X0)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X4) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_2510,plain,
    ( sP1(X0_57,X1_57,X0_56,X2_57,X3_57)
    | ~ r4_tsep_1(X0_57,X1_57,X2_57)
    | ~ v1_funct_2(X0_56,u1_struct_0(k1_tsep_1(X0_57,X1_57,X2_57)),u1_struct_0(X3_57))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_57,X1_57,X2_57)),u1_struct_0(X3_57))))
    | ~ m1_pre_topc(X1_57,X0_57)
    | ~ m1_pre_topc(X2_57,X0_57)
    | ~ v1_funct_1(X0_56)
    | v2_struct_0(X0_57)
    | v2_struct_0(X1_57)
    | v2_struct_0(X3_57)
    | v2_struct_0(X2_57)
    | ~ v2_pre_topc(X0_57)
    | ~ v2_pre_topc(X3_57)
    | ~ l1_pre_topc(X0_57)
    | ~ l1_pre_topc(X3_57) ),
    inference(subtyping,[status(esa)],[c_35])).

cnf(c_4555,plain,
    ( sP1(sK5,sK7,X0_56,X0_57,X1_57)
    | ~ r4_tsep_1(sK5,sK7,X0_57)
    | ~ v1_funct_2(X0_56,u1_struct_0(k1_tsep_1(sK5,sK7,X0_57)),u1_struct_0(X1_57))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,sK7,X0_57)),u1_struct_0(X1_57))))
    | ~ m1_pre_topc(X0_57,sK5)
    | ~ m1_pre_topc(sK7,sK5)
    | ~ v1_funct_1(X0_56)
    | v2_struct_0(X0_57)
    | v2_struct_0(X1_57)
    | v2_struct_0(sK7)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(X1_57)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(X1_57)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_2510])).

cnf(c_5383,plain,
    ( sP1(sK5,sK7,X0_56,sK8,X0_57)
    | ~ r4_tsep_1(sK5,sK7,sK8)
    | ~ v1_funct_2(X0_56,u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(X0_57))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(X0_57))))
    | ~ m1_pre_topc(sK8,sK5)
    | ~ m1_pre_topc(sK7,sK5)
    | ~ v1_funct_1(X0_56)
    | v2_struct_0(X0_57)
    | v2_struct_0(sK8)
    | v2_struct_0(sK7)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(X0_57)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(X0_57)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_4555])).

cnf(c_5759,plain,
    ( sP1(sK5,sK7,sK9,sK8,sK6)
    | ~ r4_tsep_1(sK5,sK7,sK8)
    | ~ v1_funct_2(sK9,u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))))
    | ~ m1_pre_topc(sK8,sK5)
    | ~ m1_pre_topc(sK7,sK5)
    | ~ v1_funct_1(sK9)
    | v2_struct_0(sK8)
    | v2_struct_0(sK7)
    | v2_struct_0(sK6)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK6)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_5383])).

cnf(c_5760,plain,
    ( sP1(sK5,sK7,sK9,sK8,sK6) = iProver_top
    | r4_tsep_1(sK5,sK7,sK8) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6)))) != iProver_top
    | m1_pre_topc(sK8,sK5) != iProver_top
    | m1_pre_topc(sK7,sK5) != iProver_top
    | v1_funct_1(sK9) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5759])).

cnf(c_39,negated_conjecture,
    ( v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6)
    | m1_subset_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) ),
    inference(cnf_transformation,[],[f148])).

cnf(c_2508,negated_conjecture,
    ( v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6)
    | m1_subset_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) ),
    inference(subtyping,[status(esa)],[c_39])).

cnf(c_3682,plain,
    ( v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6) = iProver_top
    | m1_subset_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2508])).

cnf(c_26,plain,
    ( sP0(X0,X1,X2,X3,X4)
    | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
    | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
    | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
    | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
    | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
    | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
    | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2519,plain,
    ( sP0(X0_57,X1_57,X0_56,X2_57,X3_57)
    | ~ v5_pre_topc(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X1_57,X0_56),X1_57,X0_57)
    | ~ v5_pre_topc(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X2_57,X0_56),X2_57,X0_57)
    | ~ v1_funct_2(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X1_57,X0_56),u1_struct_0(X1_57),u1_struct_0(X0_57))
    | ~ v1_funct_2(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X2_57,X0_56),u1_struct_0(X2_57),u1_struct_0(X0_57))
    | ~ m1_subset_1(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X1_57,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57))))
    | ~ m1_subset_1(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X2_57,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X0_57))))
    | ~ v1_funct_1(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X1_57,X0_56))
    | ~ v1_funct_1(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X2_57,X0_56)) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_3671,plain,
    ( sP0(X0_57,X1_57,X0_56,X2_57,X3_57) = iProver_top
    | v5_pre_topc(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X1_57,X0_56),X1_57,X0_57) != iProver_top
    | v5_pre_topc(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X2_57,X0_56),X2_57,X0_57) != iProver_top
    | v1_funct_2(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X1_57,X0_56),u1_struct_0(X1_57),u1_struct_0(X0_57)) != iProver_top
    | v1_funct_2(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X2_57,X0_56),u1_struct_0(X2_57),u1_struct_0(X0_57)) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X1_57,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X2_57,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X0_57)))) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X1_57,X0_56)) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X2_57,X0_56)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2519])).

cnf(c_10246,plain,
    ( sP0(sK6,sK8,sK9,sK7,sK5) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),sK8,sK6) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),sK7,sK6) != iProver_top
    | v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6) = iProver_top
    | v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),u1_struct_0(sK8),u1_struct_0(sK6)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),u1_struct_0(sK7),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3682,c_3671])).

cnf(c_10496,plain,
    ( sP0(sK6,sK8,sK9,sK7,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9368,c_85,c_86,c_87,c_88,c_89,c_90,c_91,c_92,c_93,c_94,c_95,c_96,c_97,c_98,c_99,c_102,c_106,c_110,c_114,c_118,c_122,c_126,c_4692,c_5760,c_10246])).

cnf(c_10498,plain,
    ( sP0(sK6,sK8,sK9,sK7,sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10496])).

cnf(c_33,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2512,plain,
    ( ~ sP0(X0_57,X1_57,X0_56,X2_57,X3_57)
    | v1_funct_2(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X2_57,X0_56),u1_struct_0(X2_57),u1_struct_0(X0_57)) ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_3678,plain,
    ( sP0(X0_57,X1_57,X0_56,X2_57,X3_57) != iProver_top
    | v1_funct_2(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X2_57,X0_56),u1_struct_0(X2_57),u1_struct_0(X0_57)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2512])).

cnf(c_27,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2518,plain,
    ( ~ sP0(X0_57,X1_57,X0_56,X2_57,X3_57)
    | m1_subset_1(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X1_57,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_3672,plain,
    ( sP0(X0_57,X1_57,X0_56,X2_57,X3_57) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X1_57,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_57),u1_struct_0(X0_57)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2518])).

cnf(c_31,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2514,plain,
    ( ~ sP0(X0_57,X1_57,X0_56,X2_57,X3_57)
    | m1_subset_1(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X2_57,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X0_57)))) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_3676,plain,
    ( sP0(X0_57,X1_57,X0_56,X2_57,X3_57) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_57,X0_57,k1_tsep_1(X3_57,X2_57,X1_57),X2_57,X0_56),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_57),u1_struct_0(X0_57)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2514])).

cnf(c_37,negated_conjecture,
    ( ~ v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),sK8,sK6)
    | ~ v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),sK7,sK6)
    | ~ v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6)
    | ~ v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),u1_struct_0(sK8),u1_struct_0(sK6))
    | ~ v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ v1_funct_2(sK9,u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))
    | ~ m1_subset_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
    | ~ m1_subset_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))))
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9))
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9))
    | ~ v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f150])).

cnf(c_542,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9))
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9))
    | ~ v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),u1_struct_0(sK8),u1_struct_0(sK6))
    | ~ v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6)
    | ~ v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),sK7,sK6)
    | ~ v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),sK8,sK6)
    | ~ m1_subset_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
    | ~ m1_subset_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_37,c_72,c_71,c_70])).

cnf(c_543,negated_conjecture,
    ( ~ v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),sK8,sK6)
    | ~ v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),sK7,sK6)
    | ~ v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6)
    | ~ v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),u1_struct_0(sK8),u1_struct_0(sK6))
    | ~ v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
    | ~ m1_subset_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9))
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9)) ),
    inference(renaming,[status(thm)],[c_542])).

cnf(c_2485,negated_conjecture,
    ( ~ v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),sK8,sK6)
    | ~ v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),sK7,sK6)
    | ~ v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6)
    | ~ v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),u1_struct_0(sK8),u1_struct_0(sK6))
    | ~ v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6))))
    | ~ m1_subset_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6))))
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9))
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9)) ),
    inference(subtyping,[status(esa)],[c_543])).

cnf(c_3705,plain,
    ( v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),sK8,sK6) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),sK7,sK6) != iProver_top
    | v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6) != iProver_top
    | v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),u1_struct_0(sK8),u1_struct_0(sK6)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),u1_struct_0(sK7),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK6)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2485])).

cnf(c_8816,plain,
    ( sP0(sK6,sK8,sK9,sK7,sK5) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),sK8,sK6) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),sK7,sK6) != iProver_top
    | v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6) != iProver_top
    | v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),u1_struct_0(sK8),u1_struct_0(sK6)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),u1_struct_0(sK7),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3676,c_3705])).

cnf(c_7672,plain,
    ( ~ sP1(sK5,sK7,sK9,sK8,sK6)
    | sP0(sK6,sK8,sK9,sK7,sK5)
    | ~ v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6)
    | ~ v1_funct_2(sK9,u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6))))
    | ~ v1_funct_1(sK9) ),
    inference(instantiation,[status(thm)],[c_2520])).

cnf(c_7678,plain,
    ( sP1(sK5,sK7,sK9,sK8,sK6) != iProver_top
    | sP0(sK6,sK8,sK9,sK7,sK5) = iProver_top
    | v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6) != iProver_top
    | v1_funct_2(sK9,u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK5,sK7,sK8)),u1_struct_0(sK6)))) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7672])).

cnf(c_8926,plain,
    ( v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),sK8,sK6) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),sK7,sK6) != iProver_top
    | v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6) != iProver_top
    | v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),u1_struct_0(sK8),u1_struct_0(sK6)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),u1_struct_0(sK7),u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK6)))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8816,c_85,c_86,c_87,c_88,c_89,c_90,c_91,c_92,c_93,c_94,c_95,c_96,c_97,c_98,c_99,c_4692,c_5760,c_7678])).

cnf(c_8939,plain,
    ( sP0(sK6,sK8,sK9,sK7,sK5) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),sK8,sK6) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),sK7,sK6) != iProver_top
    | v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6) != iProver_top
    | v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),u1_struct_0(sK8),u1_struct_0(sK6)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),u1_struct_0(sK7),u1_struct_0(sK6)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3672,c_8926])).

cnf(c_8979,plain,
    ( v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),sK8,sK6) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),sK7,sK6) != iProver_top
    | v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6) != iProver_top
    | v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),u1_struct_0(sK8),u1_struct_0(sK6)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),u1_struct_0(sK7),u1_struct_0(sK6)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8939,c_85,c_86,c_87,c_88,c_89,c_90,c_91,c_92,c_93,c_94,c_95,c_96,c_97,c_98,c_99,c_4692,c_5760,c_7678])).

cnf(c_8991,plain,
    ( sP0(sK6,sK8,sK9,sK7,sK5) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),sK8,sK6) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),sK7,sK6) != iProver_top
    | v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6) != iProver_top
    | v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),u1_struct_0(sK8),u1_struct_0(sK6)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3678,c_8979])).

cnf(c_9021,plain,
    ( ~ sP0(sK6,sK8,sK9,sK7,sK5)
    | ~ v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),sK8,sK6)
    | ~ v5_pre_topc(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9),sK7,sK6)
    | ~ v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6)
    | ~ v1_funct_2(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9),u1_struct_0(sK8),u1_struct_0(sK6))
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK8,sK9))
    | ~ v1_funct_1(k3_tmap_1(sK5,sK6,k1_tsep_1(sK5,sK7,sK8),sK7,sK9)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8991])).

cnf(c_22,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2523,plain,
    ( ~ sP1(X0_57,X1_57,X0_56,X2_57,X3_57)
    | ~ sP0(X3_57,X2_57,X0_56,X1_57,X0_57)
    | v5_pre_topc(X0_56,k1_tsep_1(X0_57,X1_57,X2_57),X3_57) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_7674,plain,
    ( ~ sP1(sK5,sK7,sK9,sK8,sK6)
    | ~ sP0(sK6,sK8,sK9,sK7,sK5)
    | v5_pre_topc(sK9,k1_tsep_1(sK5,sK7,sK8),sK6) ),
    inference(instantiation,[status(thm)],[c_2523])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2540,plain,
    ( ~ m1_pre_topc(X0_57,X1_57)
    | ~ m1_pre_topc(X2_57,X1_57)
    | m1_pre_topc(k1_tsep_1(X1_57,X0_57,X2_57),X1_57)
    | v2_struct_0(X0_57)
    | v2_struct_0(X1_57)
    | v2_struct_0(X2_57)
    | ~ l1_pre_topc(X1_57) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_4442,plain,
    ( ~ m1_pre_topc(X0_57,sK5)
    | m1_pre_topc(k1_tsep_1(sK5,sK7,X0_57),sK5)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(X0_57)
    | v2_struct_0(sK7)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_2540])).

cnf(c_4678,plain,
    ( m1_pre_topc(k1_tsep_1(sK5,sK7,sK8),sK5)
    | ~ m1_pre_topc(sK8,sK5)
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK8)
    | v2_struct_0(sK7)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_4442])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13371,c_13374,c_13377,c_11824,c_11790,c_10498,c_9021,c_7674,c_5759,c_4691,c_4678,c_70,c_71,c_72,c_73,c_74,c_75,c_76,c_77,c_78,c_79,c_80,c_81,c_82,c_83,c_84])).


%------------------------------------------------------------------------------
