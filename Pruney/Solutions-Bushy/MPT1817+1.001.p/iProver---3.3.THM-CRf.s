%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1817+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:32 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :  173 (1025 expanded)
%              Number of clauses        :  108 ( 183 expanded)
%              Number of leaves         :   10 ( 371 expanded)
%              Depth                    :   15
%              Number of atoms          : 1307 (35058 expanded)
%              Number of equality atoms :  234 (1297 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal clause size      :   80 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f60,plain,(
    ! [X1,X4,X2,X0,X3] :
      ( sP0(X1,X4,X2,X0,X3)
    <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
        & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
        & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f74,plain,(
    ! [X1,X4,X2,X0,X3] :
      ( ( sP0(X1,X4,X2,X0,X3)
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
        | ~ sP0(X1,X4,X2,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f60])).

fof(f75,plain,(
    ! [X1,X4,X2,X0,X3] :
      ( ( sP0(X1,X4,X2,X0,X3)
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
        | ~ sP0(X1,X4,X2,X0,X3) ) ) ),
    inference(flattening,[],[f74])).

fof(f76,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
        | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
        | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
        | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) )
      & ( ( m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
          & v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
          & m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
          & v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
          & v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
          & v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f75])).

fof(f120,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f121,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f122,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f124,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f125,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f126,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f119,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X3,X0,X2,X4))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f123,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f22,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_borsuk_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & v1_borsuk_1(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( k1_tsep_1(X0,X3,X4) = X0
                       => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v5_pre_topc(X2,X0,X1)
                            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X2) )
                        <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                            & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_borsuk_1(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_pre_topc(X4,X0)
                          & v1_borsuk_1(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( k1_tsep_1(X0,X3,X4) = X0
                         => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                              & v5_pre_topc(X2,X0,X1)
                              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                              & v1_funct_1(X2) )
                          <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                              & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                              & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                              & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                              & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                              & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f58,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) )
                      <~> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & v1_borsuk_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f59,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) )
                      <~> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & v1_borsuk_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f77,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
                        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        | ~ v5_pre_topc(X2,X0,X1)
                        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                        | ~ v1_funct_1(X2) )
                      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                        | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) ) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & v1_borsuk_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f59])).

fof(f78,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
                        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        | ~ v5_pre_topc(X2,X0,X1)
                        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                        | ~ v1_funct_1(X2) )
                      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                        | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) ) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & v1_borsuk_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f77])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
            | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
            | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
            | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
            | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
            | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
            | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
            | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
            | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            | ~ v5_pre_topc(X2,X0,X1)
            | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
            | ~ v1_funct_1(X2) )
          & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
              & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
              & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
              & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
              & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
              & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
              & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
              & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
            | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) ) )
          & k1_tsep_1(X0,X3,X4) = X0
          & m1_pre_topc(X4,X0)
          & v1_borsuk_1(X4,X0)
          & ~ v2_struct_0(X4) )
     => ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(X1))))
          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,sK10),sK10,X1)
          | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,sK10),u1_struct_0(sK10),u1_struct_0(X1))
          | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,sK10))
          | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
          | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
          | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          | ~ v5_pre_topc(X2,X0,X1)
          | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          | ~ v1_funct_1(X2) )
        & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(X1))))
            & v5_pre_topc(k2_tmap_1(X0,X1,X2,sK10),sK10,X1)
            & v1_funct_2(k2_tmap_1(X0,X1,X2,sK10),u1_struct_0(sK10),u1_struct_0(X1))
            & v1_funct_1(k2_tmap_1(X0,X1,X2,sK10))
            & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
            & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
            & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
          | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v5_pre_topc(X2,X0,X1)
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X2) ) )
        & k1_tsep_1(X0,X3,sK10) = X0
        & m1_pre_topc(sK10,X0)
        & v1_borsuk_1(sK10,X0)
        & ~ v2_struct_0(sK10) ) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                | ~ v5_pre_topc(X2,X0,X1)
                | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                | ~ v1_funct_1(X2) )
              & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                  & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                  & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                  & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                  & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                  & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                  & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X2,X0,X1)
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) ) )
              & k1_tsep_1(X0,X3,X4) = X0
              & m1_pre_topc(X4,X0)
              & v1_borsuk_1(X4,X0)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,X0)
          & v1_borsuk_1(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
              | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
              | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
              | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
              | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(X1))))
              | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,sK9),sK9,X1)
              | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,sK9),u1_struct_0(sK9),u1_struct_0(X1))
              | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,sK9))
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v5_pre_topc(X2,X0,X1)
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
            & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                & m1_subset_1(k2_tmap_1(X0,X1,X2,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(X1))))
                & v5_pre_topc(k2_tmap_1(X0,X1,X2,sK9),sK9,X1)
                & v1_funct_2(k2_tmap_1(X0,X1,X2,sK9),u1_struct_0(sK9),u1_struct_0(X1))
                & v1_funct_1(k2_tmap_1(X0,X1,X2,sK9)) )
              | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v5_pre_topc(X2,X0,X1)
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) ) )
            & k1_tsep_1(X0,sK9,X4) = X0
            & m1_pre_topc(X4,X0)
            & v1_borsuk_1(X4,X0)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(sK9,X0)
        & v1_borsuk_1(sK9,X0)
        & ~ v2_struct_0(sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                    | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                    | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                    | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                    | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                    | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                    | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
                    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    | ~ v5_pre_topc(X2,X0,X1)
                    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                    | ~ v1_funct_1(X2) )
                  & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                      & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                      & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                      & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                      & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                      & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                    | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v5_pre_topc(X2,X0,X1)
                      & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X2) ) )
                  & k1_tsep_1(X0,X3,X4) = X0
                  & m1_pre_topc(X4,X0)
                  & v1_borsuk_1(X4,X0)
                  & ~ v2_struct_0(X4) )
              & m1_pre_topc(X3,X0)
              & v1_borsuk_1(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,sK8,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                  | ~ v5_pre_topc(k2_tmap_1(X0,X1,sK8,X4),X4,X1)
                  | ~ v1_funct_2(k2_tmap_1(X0,X1,sK8,X4),u1_struct_0(X4),u1_struct_0(X1))
                  | ~ v1_funct_1(k2_tmap_1(X0,X1,sK8,X4))
                  | ~ m1_subset_1(k2_tmap_1(X0,X1,sK8,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  | ~ v5_pre_topc(k2_tmap_1(X0,X1,sK8,X3),X3,X1)
                  | ~ v1_funct_2(k2_tmap_1(X0,X1,sK8,X3),u1_struct_0(X3),u1_struct_0(X1))
                  | ~ v1_funct_1(k2_tmap_1(X0,X1,sK8,X3))
                  | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  | ~ v5_pre_topc(sK8,X0,X1)
                  | ~ v1_funct_2(sK8,u1_struct_0(X0),u1_struct_0(X1))
                  | ~ v1_funct_1(sK8) )
                & ( ( m1_subset_1(k2_tmap_1(X0,X1,sK8,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                    & v5_pre_topc(k2_tmap_1(X0,X1,sK8,X4),X4,X1)
                    & v1_funct_2(k2_tmap_1(X0,X1,sK8,X4),u1_struct_0(X4),u1_struct_0(X1))
                    & v1_funct_1(k2_tmap_1(X0,X1,sK8,X4))
                    & m1_subset_1(k2_tmap_1(X0,X1,sK8,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v5_pre_topc(k2_tmap_1(X0,X1,sK8,X3),X3,X1)
                    & v1_funct_2(k2_tmap_1(X0,X1,sK8,X3),u1_struct_0(X3),u1_struct_0(X1))
                    & v1_funct_1(k2_tmap_1(X0,X1,sK8,X3)) )
                  | ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    & v5_pre_topc(sK8,X0,X1)
                    & v1_funct_2(sK8,u1_struct_0(X0),u1_struct_0(X1))
                    & v1_funct_1(sK8) ) )
                & k1_tsep_1(X0,X3,X4) = X0
                & m1_pre_topc(X4,X0)
                & v1_borsuk_1(X4,X0)
                & ~ v2_struct_0(X4) )
            & m1_pre_topc(X3,X0)
            & v1_borsuk_1(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK8,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
                        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        | ~ v5_pre_topc(X2,X0,X1)
                        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                        | ~ v1_funct_1(X2) )
                      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                        | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) ) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & v1_borsuk_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ( ~ m1_subset_1(k2_tmap_1(X0,sK7,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK7))))
                      | ~ v5_pre_topc(k2_tmap_1(X0,sK7,X2,X4),X4,sK7)
                      | ~ v1_funct_2(k2_tmap_1(X0,sK7,X2,X4),u1_struct_0(X4),u1_struct_0(sK7))
                      | ~ v1_funct_1(k2_tmap_1(X0,sK7,X2,X4))
                      | ~ m1_subset_1(k2_tmap_1(X0,sK7,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK7))))
                      | ~ v5_pre_topc(k2_tmap_1(X0,sK7,X2,X3),X3,sK7)
                      | ~ v1_funct_2(k2_tmap_1(X0,sK7,X2,X3),u1_struct_0(X3),u1_struct_0(sK7))
                      | ~ v1_funct_1(k2_tmap_1(X0,sK7,X2,X3))
                      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7))))
                      | ~ v5_pre_topc(X2,X0,sK7)
                      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK7))
                      | ~ v1_funct_1(X2) )
                    & ( ( m1_subset_1(k2_tmap_1(X0,sK7,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK7))))
                        & v5_pre_topc(k2_tmap_1(X0,sK7,X2,X4),X4,sK7)
                        & v1_funct_2(k2_tmap_1(X0,sK7,X2,X4),u1_struct_0(X4),u1_struct_0(sK7))
                        & v1_funct_1(k2_tmap_1(X0,sK7,X2,X4))
                        & m1_subset_1(k2_tmap_1(X0,sK7,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK7))))
                        & v5_pre_topc(k2_tmap_1(X0,sK7,X2,X3),X3,sK7)
                        & v1_funct_2(k2_tmap_1(X0,sK7,X2,X3),u1_struct_0(X3),u1_struct_0(sK7))
                        & v1_funct_1(k2_tmap_1(X0,sK7,X2,X3)) )
                      | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7))))
                        & v5_pre_topc(X2,X0,sK7)
                        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK7))
                        & v1_funct_1(X2) ) )
                    & k1_tsep_1(X0,X3,X4) = X0
                    & m1_pre_topc(X4,X0)
                    & v1_borsuk_1(X4,X0)
                    & ~ v2_struct_0(X4) )
                & m1_pre_topc(X3,X0)
                & v1_borsuk_1(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK7))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK7)
        & v2_pre_topc(sK7)
        & ~ v2_struct_0(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
                          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X2,X0,X1)
                          | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          | ~ v1_funct_1(X2) )
                        & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                            & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                          | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v5_pre_topc(X2,X0,X1)
                            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X2) ) )
                        & k1_tsep_1(X0,X3,X4) = X0
                        & m1_pre_topc(X4,X0)
                        & v1_borsuk_1(X4,X0)
                        & ~ v2_struct_0(X4) )
                    & m1_pre_topc(X3,X0)
                    & v1_borsuk_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
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
                      ( ( ~ m1_subset_1(k2_tmap_1(sK6,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(sK6,X1,X2,X4),X4,X1)
                        | ~ v1_funct_2(k2_tmap_1(sK6,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(sK6,X1,X2,X4))
                        | ~ m1_subset_1(k2_tmap_1(sK6,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(sK6,X1,X2,X3),X3,X1)
                        | ~ v1_funct_2(k2_tmap_1(sK6,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(sK6,X1,X2,X3))
                        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1))))
                        | ~ v5_pre_topc(X2,sK6,X1)
                        | ~ v1_funct_2(X2,u1_struct_0(sK6),u1_struct_0(X1))
                        | ~ v1_funct_1(X2) )
                      & ( ( m1_subset_1(k2_tmap_1(sK6,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(sK6,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(sK6,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(sK6,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(sK6,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(sK6,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(sK6,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(sK6,X1,X2,X3)) )
                        | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1))))
                          & v5_pre_topc(X2,sK6,X1)
                          & v1_funct_2(X2,u1_struct_0(sK6),u1_struct_0(X1))
                          & v1_funct_1(X2) ) )
                      & k1_tsep_1(sK6,X3,X4) = sK6
                      & m1_pre_topc(X4,sK6)
                      & v1_borsuk_1(X4,sK6)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,sK6)
                  & v1_borsuk_1(X3,sK6)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK6),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK6)
      & v2_pre_topc(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,
    ( ( ~ m1_subset_1(k2_tmap_1(sK6,sK7,sK8,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK7))))
      | ~ v5_pre_topc(k2_tmap_1(sK6,sK7,sK8,sK10),sK10,sK7)
      | ~ v1_funct_2(k2_tmap_1(sK6,sK7,sK8,sK10),u1_struct_0(sK10),u1_struct_0(sK7))
      | ~ v1_funct_1(k2_tmap_1(sK6,sK7,sK8,sK10))
      | ~ m1_subset_1(k2_tmap_1(sK6,sK7,sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7))))
      | ~ v5_pre_topc(k2_tmap_1(sK6,sK7,sK8,sK9),sK9,sK7)
      | ~ v1_funct_2(k2_tmap_1(sK6,sK7,sK8,sK9),u1_struct_0(sK9),u1_struct_0(sK7))
      | ~ v1_funct_1(k2_tmap_1(sK6,sK7,sK8,sK9))
      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
      | ~ v5_pre_topc(sK8,sK6,sK7)
      | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
      | ~ v1_funct_1(sK8) )
    & ( ( m1_subset_1(k2_tmap_1(sK6,sK7,sK8,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK7))))
        & v5_pre_topc(k2_tmap_1(sK6,sK7,sK8,sK10),sK10,sK7)
        & v1_funct_2(k2_tmap_1(sK6,sK7,sK8,sK10),u1_struct_0(sK10),u1_struct_0(sK7))
        & v1_funct_1(k2_tmap_1(sK6,sK7,sK8,sK10))
        & m1_subset_1(k2_tmap_1(sK6,sK7,sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7))))
        & v5_pre_topc(k2_tmap_1(sK6,sK7,sK8,sK9),sK9,sK7)
        & v1_funct_2(k2_tmap_1(sK6,sK7,sK8,sK9),u1_struct_0(sK9),u1_struct_0(sK7))
        & v1_funct_1(k2_tmap_1(sK6,sK7,sK8,sK9)) )
      | ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
        & v5_pre_topc(sK8,sK6,sK7)
        & v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
        & v1_funct_1(sK8) ) )
    & k1_tsep_1(sK6,sK9,sK10) = sK6
    & m1_pre_topc(sK10,sK6)
    & v1_borsuk_1(sK10,sK6)
    & ~ v2_struct_0(sK10)
    & m1_pre_topc(sK9,sK6)
    & v1_borsuk_1(sK9,sK6)
    & ~ v2_struct_0(sK9)
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    & v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
    & v1_funct_1(sK8)
    & l1_pre_topc(sK7)
    & v2_pre_topc(sK7)
    & ~ v2_struct_0(sK7)
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10])],[f78,f83,f82,f81,f80,f79])).

fof(f176,plain,
    ( m1_subset_1(k2_tmap_1(sK6,sK7,sK8,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK7))))
    | v5_pre_topc(sK8,sK6,sK7) ),
    inference(cnf_transformation,[],[f84])).

fof(f160,plain,
    ( m1_subset_1(k2_tmap_1(sK6,sK7,sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7))))
    | v5_pre_topc(sK8,sK6,sK7) ),
    inference(cnf_transformation,[],[f84])).

fof(f127,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f148,plain,
    ( v1_funct_1(k2_tmap_1(sK6,sK7,sK8,sK9))
    | v5_pre_topc(sK8,sK6,sK7) ),
    inference(cnf_transformation,[],[f84])).

fof(f152,plain,
    ( v1_funct_2(k2_tmap_1(sK6,sK7,sK8,sK9),u1_struct_0(sK9),u1_struct_0(sK7))
    | v5_pre_topc(sK8,sK6,sK7) ),
    inference(cnf_transformation,[],[f84])).

fof(f156,plain,
    ( v5_pre_topc(k2_tmap_1(sK6,sK7,sK8,sK9),sK9,sK7)
    | v5_pre_topc(sK8,sK6,sK7) ),
    inference(cnf_transformation,[],[f84])).

fof(f138,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
    inference(cnf_transformation,[],[f84])).

fof(f145,plain,(
    k1_tsep_1(sK6,sK9,sK10) = sK6 ),
    inference(cnf_transformation,[],[f84])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( r4_tsep_1(X0,X3,X4)
                          & k1_tsep_1(X0,X3,X4) = X0 )
                       => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v5_pre_topc(X2,X0,X1)
                            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X2) )
                        <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                            & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      | ~ r4_tsep_1(X0,X3,X4)
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      | ~ r4_tsep_1(X0,X3,X4)
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f61,plain,(
    ! [X3,X0,X2,X4,X1] :
      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v5_pre_topc(X2,X0,X1)
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
      <=> sP0(X1,X4,X2,X0,X3) )
      | ~ sP1(X3,X0,X2,X4,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( sP1(X3,X0,X2,X4,X1)
                      | ~ r4_tsep_1(X0,X3,X4)
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f55,f61,f60])).

fof(f128,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X3,X0,X2,X4,X1)
      | ~ r4_tsep_1(X0,X3,X4)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f130,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f84])).

fof(f131,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f84])).

fof(f132,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f84])).

fof(f139,plain,(
    ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f84])).

fof(f140,plain,(
    v1_borsuk_1(sK9,sK6) ),
    inference(cnf_transformation,[],[f84])).

fof(f141,plain,(
    m1_pre_topc(sK9,sK6) ),
    inference(cnf_transformation,[],[f84])).

fof(f142,plain,(
    ~ v2_struct_0(sK10) ),
    inference(cnf_transformation,[],[f84])).

fof(f143,plain,(
    v1_borsuk_1(sK10,sK6) ),
    inference(cnf_transformation,[],[f84])).

fof(f144,plain,(
    m1_pre_topc(sK10,sK6) ),
    inference(cnf_transformation,[],[f84])).

fof(f21,axiom,(
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

fof(f56,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f57,plain,(
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
    inference(flattening,[],[f56])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_borsuk_1(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f133,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f84])).

fof(f134,plain,(
    v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f84])).

fof(f135,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f84])).

fof(f136,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f84])).

fof(f137,plain,(
    v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f84])).

fof(f71,plain,(
    ! [X3,X0,X2,X4,X1] :
      ( ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v5_pre_topc(X2,X0,X1)
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X2) )
          | ~ sP0(X1,X4,X2,X0,X3) )
        & ( sP0(X1,X4,X2,X0,X3)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          | ~ v5_pre_topc(X2,X0,X1)
          | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          | ~ v1_funct_1(X2) ) )
      | ~ sP1(X3,X0,X2,X4,X1) ) ),
    inference(nnf_transformation,[],[f61])).

fof(f72,plain,(
    ! [X3,X0,X2,X4,X1] :
      ( ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v5_pre_topc(X2,X0,X1)
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X2) )
          | ~ sP0(X1,X4,X2,X0,X3) )
        & ( sP0(X1,X4,X2,X0,X3)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          | ~ v5_pre_topc(X2,X0,X1)
          | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          | ~ v1_funct_1(X2) ) )
      | ~ sP1(X3,X0,X2,X4,X1) ) ),
    inference(flattening,[],[f71])).

fof(f73,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
            & v5_pre_topc(X2,X1,X4)
            & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
            & v1_funct_1(X2) )
          | ~ sP0(X4,X3,X2,X1,X0) )
        & ( sP0(X4,X3,X2,X1,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
          | ~ v5_pre_topc(X2,X1,X4)
          | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
          | ~ v1_funct_1(X2) ) )
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f72])).

fof(f114,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X4,X3,X2,X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
      | ~ v5_pre_topc(X2,X1,X4)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
      | ~ v1_funct_1(X2)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f117,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X1,X4)
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f178,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK6,sK7,sK8,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK7))))
    | ~ v5_pre_topc(k2_tmap_1(sK6,sK7,sK8,sK10),sK10,sK7)
    | ~ v1_funct_2(k2_tmap_1(sK6,sK7,sK8,sK10),u1_struct_0(sK10),u1_struct_0(sK7))
    | ~ v1_funct_1(k2_tmap_1(sK6,sK7,sK8,sK10))
    | ~ m1_subset_1(k2_tmap_1(sK6,sK7,sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7))))
    | ~ v5_pre_topc(k2_tmap_1(sK6,sK7,sK8,sK9),sK9,sK7)
    | ~ v1_funct_2(k2_tmap_1(sK6,sK7,sK8,sK9),u1_struct_0(sK9),u1_struct_0(sK7))
    | ~ v1_funct_1(k2_tmap_1(sK6,sK7,sK8,sK9))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v5_pre_topc(sK8,sK6,sK7)
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f84])).

fof(f172,plain,
    ( v5_pre_topc(k2_tmap_1(sK6,sK7,sK8,sK10),sK10,sK7)
    | v5_pre_topc(sK8,sK6,sK7) ),
    inference(cnf_transformation,[],[f84])).

fof(f168,plain,
    ( v1_funct_2(k2_tmap_1(sK6,sK7,sK8,sK10),u1_struct_0(sK10),u1_struct_0(sK7))
    | v5_pre_topc(sK8,sK6,sK7) ),
    inference(cnf_transformation,[],[f84])).

fof(f164,plain,
    ( v1_funct_1(k2_tmap_1(sK6,sK7,sK8,sK10))
    | v5_pre_topc(sK8,sK6,sK7) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_40,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_12218,plain,
    ( ~ sP0(sK7,sK10,sK8,sK6,sK9)
    | v1_funct_2(k2_tmap_1(sK6,sK7,sK8,sK9),u1_struct_0(sK9),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_12240,plain,
    ( sP0(sK7,sK10,sK8,sK6,sK9) != iProver_top
    | v1_funct_2(k2_tmap_1(sK6,sK7,sK8,sK9),u1_struct_0(sK9),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12218])).

cnf(c_39,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_12219,plain,
    ( ~ sP0(sK7,sK10,sK8,sK6,sK9)
    | v5_pre_topc(k2_tmap_1(sK6,sK7,sK8,sK9),sK9,sK7) ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_12238,plain,
    ( sP0(sK7,sK10,sK8,sK6,sK9) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK6,sK7,sK8,sK9),sK9,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12219])).

cnf(c_38,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_12220,plain,
    ( ~ sP0(sK7,sK10,sK8,sK6,sK9)
    | m1_subset_1(k2_tmap_1(sK6,sK7,sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7)))) ),
    inference(instantiation,[status(thm)],[c_38])).

cnf(c_12236,plain,
    ( sP0(sK7,sK10,sK8,sK6,sK9) != iProver_top
    | m1_subset_1(k2_tmap_1(sK6,sK7,sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12220])).

cnf(c_36,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_12221,plain,
    ( ~ sP0(sK7,sK10,sK8,sK6,sK9)
    | v1_funct_2(k2_tmap_1(sK6,sK7,sK8,sK10),u1_struct_0(sK10),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_12234,plain,
    ( sP0(sK7,sK10,sK8,sK6,sK9) != iProver_top
    | v1_funct_2(k2_tmap_1(sK6,sK7,sK8,sK10),u1_struct_0(sK10),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12221])).

cnf(c_35,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_12222,plain,
    ( ~ sP0(sK7,sK10,sK8,sK6,sK9)
    | v5_pre_topc(k2_tmap_1(sK6,sK7,sK8,sK10),sK10,sK7) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_12232,plain,
    ( sP0(sK7,sK10,sK8,sK6,sK9) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK6,sK7,sK8,sK10),sK10,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12222])).

cnf(c_34,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_12223,plain,
    ( ~ sP0(sK7,sK10,sK8,sK6,sK9)
    | m1_subset_1(k2_tmap_1(sK6,sK7,sK8,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK7)))) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_12230,plain,
    ( sP0(sK7,sK10,sK8,sK6,sK9) != iProver_top
    | m1_subset_1(k2_tmap_1(sK6,sK7,sK8,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12223])).

cnf(c_41,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_12224,plain,
    ( ~ sP0(sK7,sK10,sK8,sK6,sK9)
    | v1_funct_1(k2_tmap_1(sK6,sK7,sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_12228,plain,
    ( sP0(sK7,sK10,sK8,sK6,sK9) != iProver_top
    | v1_funct_1(k2_tmap_1(sK6,sK7,sK8,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12224])).

cnf(c_37,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_12225,plain,
    ( ~ sP0(sK7,sK10,sK8,sK6,sK9)
    | v1_funct_1(k2_tmap_1(sK6,sK7,sK8,sK10)) ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_12226,plain,
    ( sP0(sK7,sK10,sK8,sK6,sK9) != iProver_top
    | v1_funct_1(k2_tmap_1(sK6,sK7,sK8,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12225])).

cnf(c_46,negated_conjecture,
    ( v5_pre_topc(sK8,sK6,sK7)
    | m1_subset_1(k2_tmap_1(sK6,sK7,sK8,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK7)))) ),
    inference(cnf_transformation,[],[f176])).

cnf(c_3801,plain,
    ( v5_pre_topc(sK8,sK6,sK7) = iProver_top
    | m1_subset_1(k2_tmap_1(sK6,sK7,sK8,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_62,negated_conjecture,
    ( v5_pre_topc(sK8,sK6,sK7)
    | m1_subset_1(k2_tmap_1(sK6,sK7,sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7)))) ),
    inference(cnf_transformation,[],[f160])).

cnf(c_3797,plain,
    ( v5_pre_topc(sK8,sK6,sK7) = iProver_top
    | m1_subset_1(k2_tmap_1(sK6,sK7,sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_62])).

cnf(c_33,plain,
    ( sP0(X0,X1,X2,X3,X4)
    | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
    | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
    | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
    | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
    | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
    | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_3812,plain,
    ( sP0(X0,X1,X2,X3,X4) = iProver_top
    | v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) != iProver_top
    | v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) != iProver_top
    | v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) != iProver_top
    | v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) != iProver_top
    | v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_10010,plain,
    ( sP0(sK7,X0,sK8,sK6,sK9) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK6,sK7,sK8,X0),X0,sK7) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK6,sK7,sK8,sK9),sK9,sK7) != iProver_top
    | v5_pre_topc(sK8,sK6,sK7) = iProver_top
    | v1_funct_2(k2_tmap_1(sK6,sK7,sK8,X0),u1_struct_0(X0),u1_struct_0(sK7)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK6,sK7,sK8,sK9),u1_struct_0(sK9),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK6,sK7,sK8,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK6,sK7,sK8,X0)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK6,sK7,sK8,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3797,c_3812])).

cnf(c_74,negated_conjecture,
    ( v5_pre_topc(sK8,sK6,sK7)
    | v1_funct_1(k2_tmap_1(sK6,sK7,sK8,sK9)) ),
    inference(cnf_transformation,[],[f148])).

cnf(c_110,plain,
    ( v5_pre_topc(sK8,sK6,sK7) = iProver_top
    | v1_funct_1(k2_tmap_1(sK6,sK7,sK8,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_74])).

cnf(c_70,negated_conjecture,
    ( v5_pre_topc(sK8,sK6,sK7)
    | v1_funct_2(k2_tmap_1(sK6,sK7,sK8,sK9),u1_struct_0(sK9),u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f152])).

cnf(c_114,plain,
    ( v5_pre_topc(sK8,sK6,sK7) = iProver_top
    | v1_funct_2(k2_tmap_1(sK6,sK7,sK8,sK9),u1_struct_0(sK9),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_70])).

cnf(c_66,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(sK6,sK7,sK8,sK9),sK9,sK7)
    | v5_pre_topc(sK8,sK6,sK7) ),
    inference(cnf_transformation,[],[f156])).

cnf(c_118,plain,
    ( v5_pre_topc(k2_tmap_1(sK6,sK7,sK8,sK9),sK9,sK7) = iProver_top
    | v5_pre_topc(sK8,sK6,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_66])).

cnf(c_12173,plain,
    ( v1_funct_1(k2_tmap_1(sK6,sK7,sK8,X0)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK6,sK7,sK8,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7)))) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK6,sK7,sK8,X0),X0,sK7) != iProver_top
    | sP0(sK7,X0,sK8,sK6,sK9) = iProver_top
    | v5_pre_topc(sK8,sK6,sK7) = iProver_top
    | v1_funct_2(k2_tmap_1(sK6,sK7,sK8,X0),u1_struct_0(X0),u1_struct_0(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10010,c_110,c_114,c_118])).

cnf(c_12174,plain,
    ( sP0(sK7,X0,sK8,sK6,sK9) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK6,sK7,sK8,X0),X0,sK7) != iProver_top
    | v5_pre_topc(sK8,sK6,sK7) = iProver_top
    | v1_funct_2(k2_tmap_1(sK6,sK7,sK8,X0),u1_struct_0(X0),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK6,sK7,sK8,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK7)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK6,sK7,sK8,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_12173])).

cnf(c_12185,plain,
    ( sP0(sK7,sK10,sK8,sK6,sK9) = iProver_top
    | v5_pre_topc(k2_tmap_1(sK6,sK7,sK8,sK10),sK10,sK7) != iProver_top
    | v5_pre_topc(sK8,sK6,sK7) = iProver_top
    | v1_funct_2(k2_tmap_1(sK6,sK7,sK8,sK10),u1_struct_0(sK10),u1_struct_0(sK7)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK6,sK7,sK8,sK10)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3801,c_12174])).

cnf(c_84,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_3787,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_84])).

cnf(c_77,negated_conjecture,
    ( k1_tsep_1(sK6,sK9,sK10) = sK6 ),
    inference(cnf_transformation,[],[f145])).

cnf(c_42,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ r4_tsep_1(X1,X0,X3)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | k1_tsep_1(X1,X0,X3) != X1 ),
    inference(cnf_transformation,[],[f128])).

cnf(c_3803,plain,
    ( k1_tsep_1(X0,X1,X2) != X0
    | sP1(X1,X0,X3,X2,X4) = iProver_top
    | r4_tsep_1(X0,X1,X2) != iProver_top
    | v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X4)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X4)))) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X4) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X4) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_7408,plain,
    ( sP1(sK9,sK6,X0,sK10,X1) = iProver_top
    | r4_tsep_1(sK6,sK9,sK10) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) != iProver_top
    | m1_pre_topc(sK9,sK6) != iProver_top
    | m1_pre_topc(sK10,sK6) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_77,c_3803])).

cnf(c_92,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_93,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_92])).

cnf(c_91,negated_conjecture,
    ( v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_94,plain,
    ( v2_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_91])).

cnf(c_90,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_95,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_90])).

cnf(c_83,negated_conjecture,
    ( ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_102,plain,
    ( v2_struct_0(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_83])).

cnf(c_82,negated_conjecture,
    ( v1_borsuk_1(sK9,sK6) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_103,plain,
    ( v1_borsuk_1(sK9,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_82])).

cnf(c_81,negated_conjecture,
    ( m1_pre_topc(sK9,sK6) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_104,plain,
    ( m1_pre_topc(sK9,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_81])).

cnf(c_80,negated_conjecture,
    ( ~ v2_struct_0(sK10) ),
    inference(cnf_transformation,[],[f142])).

cnf(c_105,plain,
    ( v2_struct_0(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_80])).

cnf(c_79,negated_conjecture,
    ( v1_borsuk_1(sK10,sK6) ),
    inference(cnf_transformation,[],[f143])).

cnf(c_106,plain,
    ( v1_borsuk_1(sK10,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_79])).

cnf(c_78,negated_conjecture,
    ( m1_pre_topc(sK10,sK6) ),
    inference(cnf_transformation,[],[f144])).

cnf(c_107,plain,
    ( m1_pre_topc(sK10,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_78])).

cnf(c_43,plain,
    ( r4_tsep_1(X0,X1,X2)
    | ~ v1_borsuk_1(X2,X0)
    | ~ v1_borsuk_1(X1,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_pre_topc(X2,X0)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_4706,plain,
    ( r4_tsep_1(sK6,X0,sK10)
    | ~ v1_borsuk_1(X0,sK6)
    | ~ v1_borsuk_1(sK10,sK6)
    | ~ m1_pre_topc(X0,sK6)
    | ~ m1_pre_topc(sK10,sK6)
    | v2_struct_0(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(c_4856,plain,
    ( r4_tsep_1(sK6,sK9,sK10)
    | ~ v1_borsuk_1(sK9,sK6)
    | ~ v1_borsuk_1(sK10,sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | ~ m1_pre_topc(sK10,sK6)
    | v2_struct_0(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_4706])).

cnf(c_4857,plain,
    ( r4_tsep_1(sK6,sK9,sK10) = iProver_top
    | v1_borsuk_1(sK9,sK6) != iProver_top
    | v1_borsuk_1(sK10,sK6) != iProver_top
    | m1_pre_topc(sK9,sK6) != iProver_top
    | m1_pre_topc(sK10,sK6) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4856])).

cnf(c_7492,plain,
    ( l1_pre_topc(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(X1)) != iProver_top
    | sP1(sK9,sK6,X0,sK10,X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7408,c_93,c_94,c_95,c_102,c_103,c_104,c_105,c_106,c_107,c_4857])).

cnf(c_7493,plain,
    ( sP1(sK9,sK6,X0,sK10,X1) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK6),u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_7492])).

cnf(c_7505,plain,
    ( sP1(sK9,sK6,sK8,sK10,sK7) = iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3787,c_7493])).

cnf(c_89,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_96,plain,
    ( v2_struct_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_89])).

cnf(c_88,negated_conjecture,
    ( v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_97,plain,
    ( v2_pre_topc(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_88])).

cnf(c_87,negated_conjecture,
    ( l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_98,plain,
    ( l1_pre_topc(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_87])).

cnf(c_86,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_99,plain,
    ( v1_funct_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_86])).

cnf(c_85,negated_conjecture,
    ( v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_100,plain,
    ( v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_85])).

cnf(c_101,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_84])).

cnf(c_4741,plain,
    ( sP1(X0,X1,sK8,X2,X3)
    | ~ r4_tsep_1(X1,X0,X2)
    | ~ v1_funct_2(sK8,u1_struct_0(X1),u1_struct_0(X3))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v1_funct_1(sK8)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tsep_1(X1,X0,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_5313,plain,
    ( sP1(sK9,sK6,sK8,X0,X1)
    | ~ r4_tsep_1(sK6,sK9,X0)
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(X1))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | ~ v1_funct_1(sK8)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK9)
    | v2_struct_0(sK6)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK6)
    | k1_tsep_1(sK6,sK9,X0) != sK6 ),
    inference(instantiation,[status(thm)],[c_4741])).

cnf(c_6191,plain,
    ( sP1(sK9,sK6,sK8,sK10,X0)
    | ~ r4_tsep_1(sK6,sK9,sK10)
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(X0))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0))))
    | ~ m1_pre_topc(sK9,sK6)
    | ~ m1_pre_topc(sK10,sK6)
    | ~ v1_funct_1(sK8)
    | v2_struct_0(X0)
    | v2_struct_0(sK9)
    | v2_struct_0(sK10)
    | v2_struct_0(sK6)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK6)
    | k1_tsep_1(sK6,sK9,sK10) != sK6 ),
    inference(instantiation,[status(thm)],[c_5313])).

cnf(c_6192,plain,
    ( k1_tsep_1(sK6,sK9,sK10) != sK6
    | sP1(sK9,sK6,sK8,sK10,X0) = iProver_top
    | r4_tsep_1(sK6,sK9,sK10) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
    | m1_pre_topc(sK9,sK6) != iProver_top
    | m1_pre_topc(sK10,sK6) != iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6191])).

cnf(c_6194,plain,
    ( k1_tsep_1(sK6,sK9,sK10) != sK6
    | sP1(sK9,sK6,sK8,sK10,sK7) = iProver_top
    | r4_tsep_1(sK6,sK9,sK10) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7)))) != iProver_top
    | m1_pre_topc(sK9,sK6) != iProver_top
    | m1_pre_topc(sK10,sK6) != iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6192])).

cnf(c_7948,plain,
    ( sP1(sK9,sK6,sK8,sK10,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7505,c_93,c_94,c_95,c_96,c_97,c_98,c_99,c_100,c_101,c_102,c_103,c_104,c_105,c_106,c_107,c_77,c_4857,c_6194])).

cnf(c_32,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | sP0(X4,X3,X2,X1,X0)
    | ~ v5_pre_topc(X2,X1,X4)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_3813,plain,
    ( sP1(X0,X1,X2,X3,X4) != iProver_top
    | sP0(X4,X3,X2,X1,X0) = iProver_top
    | v5_pre_topc(X2,X1,X4) != iProver_top
    | v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X4)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4)))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_11966,plain,
    ( sP1(X0,sK6,sK8,X1,sK7) != iProver_top
    | sP0(sK7,X1,sK8,sK6,X0) = iProver_top
    | v5_pre_topc(sK8,sK6,sK7) != iProver_top
    | v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7)) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_3787,c_3813])).

cnf(c_12134,plain,
    ( sP1(X0,sK6,sK8,X1,sK7) != iProver_top
    | sP0(sK7,X1,sK8,sK6,X0) = iProver_top
    | v5_pre_topc(sK8,sK6,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11966,c_99,c_100])).

cnf(c_12143,plain,
    ( sP0(sK7,sK10,sK8,sK6,sK9) = iProver_top
    | v5_pre_topc(sK8,sK6,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_7948,c_12134])).

cnf(c_29,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v5_pre_topc(X2,X1,X4) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_8155,plain,
    ( ~ sP1(sK9,sK6,sK8,sK10,X0)
    | ~ sP0(X0,sK10,sK8,sK6,sK9)
    | v5_pre_topc(sK8,sK6,X0) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_8160,plain,
    ( sP1(sK9,sK6,sK8,sK10,X0) != iProver_top
    | sP0(X0,sK10,sK8,sK6,sK9) != iProver_top
    | v5_pre_topc(sK8,sK6,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8155])).

cnf(c_8162,plain,
    ( sP1(sK9,sK6,sK8,sK10,sK7) != iProver_top
    | sP0(sK7,sK10,sK8,sK6,sK9) != iProver_top
    | v5_pre_topc(sK8,sK6,sK7) = iProver_top ),
    inference(instantiation,[status(thm)],[c_8160])).

cnf(c_44,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(sK6,sK7,sK8,sK9),sK9,sK7)
    | ~ v5_pre_topc(k2_tmap_1(sK6,sK7,sK8,sK10),sK10,sK7)
    | ~ v5_pre_topc(sK8,sK6,sK7)
    | ~ v1_funct_2(k2_tmap_1(sK6,sK7,sK8,sK9),u1_struct_0(sK9),u1_struct_0(sK7))
    | ~ v1_funct_2(k2_tmap_1(sK6,sK7,sK8,sK10),u1_struct_0(sK10),u1_struct_0(sK7))
    | ~ v1_funct_2(sK8,u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ m1_subset_1(k2_tmap_1(sK6,sK7,sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7))))
    | ~ m1_subset_1(k2_tmap_1(sK6,sK7,sK8,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK7))))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK7))))
    | ~ v1_funct_1(k2_tmap_1(sK6,sK7,sK8,sK9))
    | ~ v1_funct_1(k2_tmap_1(sK6,sK7,sK8,sK10))
    | ~ v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f178])).

cnf(c_583,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK6,sK7,sK8,sK10))
    | ~ v1_funct_1(k2_tmap_1(sK6,sK7,sK8,sK9))
    | ~ v1_funct_2(k2_tmap_1(sK6,sK7,sK8,sK10),u1_struct_0(sK10),u1_struct_0(sK7))
    | ~ v1_funct_2(k2_tmap_1(sK6,sK7,sK8,sK9),u1_struct_0(sK9),u1_struct_0(sK7))
    | ~ v5_pre_topc(sK8,sK6,sK7)
    | ~ v5_pre_topc(k2_tmap_1(sK6,sK7,sK8,sK10),sK10,sK7)
    | ~ v5_pre_topc(k2_tmap_1(sK6,sK7,sK8,sK9),sK9,sK7)
    | ~ m1_subset_1(k2_tmap_1(sK6,sK7,sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7))))
    | ~ m1_subset_1(k2_tmap_1(sK6,sK7,sK8,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK7)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_44,c_86,c_85,c_84])).

cnf(c_584,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(sK6,sK7,sK8,sK9),sK9,sK7)
    | ~ v5_pre_topc(k2_tmap_1(sK6,sK7,sK8,sK10),sK10,sK7)
    | ~ v5_pre_topc(sK8,sK6,sK7)
    | ~ v1_funct_2(k2_tmap_1(sK6,sK7,sK8,sK9),u1_struct_0(sK9),u1_struct_0(sK7))
    | ~ v1_funct_2(k2_tmap_1(sK6,sK7,sK8,sK10),u1_struct_0(sK10),u1_struct_0(sK7))
    | ~ m1_subset_1(k2_tmap_1(sK6,sK7,sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7))))
    | ~ m1_subset_1(k2_tmap_1(sK6,sK7,sK8,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK7))))
    | ~ v1_funct_1(k2_tmap_1(sK6,sK7,sK8,sK9))
    | ~ v1_funct_1(k2_tmap_1(sK6,sK7,sK8,sK10)) ),
    inference(renaming,[status(thm)],[c_583])).

cnf(c_585,plain,
    ( v5_pre_topc(k2_tmap_1(sK6,sK7,sK8,sK9),sK9,sK7) != iProver_top
    | v5_pre_topc(k2_tmap_1(sK6,sK7,sK8,sK10),sK10,sK7) != iProver_top
    | v5_pre_topc(sK8,sK6,sK7) != iProver_top
    | v1_funct_2(k2_tmap_1(sK6,sK7,sK8,sK9),u1_struct_0(sK9),u1_struct_0(sK7)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK6,sK7,sK8,sK10),u1_struct_0(sK10),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK6,sK7,sK8,sK9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK7)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK6,sK7,sK8,sK10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK10),u1_struct_0(sK7)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK6,sK7,sK8,sK9)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK6,sK7,sK8,sK10)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_584])).

cnf(c_50,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(sK6,sK7,sK8,sK10),sK10,sK7)
    | v5_pre_topc(sK8,sK6,sK7) ),
    inference(cnf_transformation,[],[f172])).

cnf(c_134,plain,
    ( v5_pre_topc(k2_tmap_1(sK6,sK7,sK8,sK10),sK10,sK7) = iProver_top
    | v5_pre_topc(sK8,sK6,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_54,negated_conjecture,
    ( v5_pre_topc(sK8,sK6,sK7)
    | v1_funct_2(k2_tmap_1(sK6,sK7,sK8,sK10),u1_struct_0(sK10),u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f168])).

cnf(c_130,plain,
    ( v5_pre_topc(sK8,sK6,sK7) = iProver_top
    | v1_funct_2(k2_tmap_1(sK6,sK7,sK8,sK10),u1_struct_0(sK10),u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_58,negated_conjecture,
    ( v5_pre_topc(sK8,sK6,sK7)
    | v1_funct_1(k2_tmap_1(sK6,sK7,sK8,sK10)) ),
    inference(cnf_transformation,[],[f164])).

cnf(c_126,plain,
    ( v5_pre_topc(sK8,sK6,sK7) = iProver_top
    | v1_funct_1(k2_tmap_1(sK6,sK7,sK8,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12240,c_12238,c_12236,c_12234,c_12232,c_12230,c_12228,c_12226,c_12185,c_12143,c_8162,c_6194,c_4857,c_585,c_134,c_130,c_126,c_77,c_107,c_106,c_105,c_104,c_103,c_102,c_101,c_100,c_99,c_98,c_97,c_96,c_95,c_94,c_93])).


%------------------------------------------------------------------------------
