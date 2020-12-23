%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:45 EST 2020

% Result     : Theorem 1.70s
% Output     : Refutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :  333 (38694 expanded)
%              Number of leaves         :   10 (16027 expanded)
%              Depth                    :   90
%              Number of atoms          : 3778 (1515925 expanded)
%              Number of equality atoms :   37 (46127 expanded)
%              Maximal formula depth    :   29 (  12 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f407,plain,(
    $false ),
    inference(subsumption_resolution,[],[f406,f28])).

fof(f28,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f25])).

% (19967)Refutation not found, incomplete strategy% (19967)------------------------------
% (19967)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19967)Termination reason: Refutation not found, incomplete strategy

% (19967)Memory used [KB]: 11769
% (19967)Time elapsed: 0.188 s
% (19967)------------------------------
% (19967)------------------------------
fof(f25,plain,
    ( ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK2) )
    & ( ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
        & v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
        & v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
        & v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
        & m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        & v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
        & v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        & v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) )
      | ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v5_pre_topc(sK2,sK0,sK1)
        & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(sK2) ) )
    & r4_tsep_1(sK0,sK3,sK4)
    & sK0 = k1_tsep_1(sK0,sK3,sK4)
    & m1_pre_topc(sK4,sK0)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f19,f24,f23,f22,f21,f20])).

fof(f20,plain,
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
                        & r4_tsep_1(X0,X3,X4)
                        & k1_tsep_1(X0,X3,X4) = X0
                        & m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                    & m1_pre_topc(X3,X0)
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
                      ( ( ~ m1_subset_1(k2_tmap_1(sK0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(sK0,X1,X2,X4),X4,X1)
                        | ~ v1_funct_2(k2_tmap_1(sK0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(sK0,X1,X2,X4))
                        | ~ m1_subset_1(k2_tmap_1(sK0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(sK0,X1,X2,X3),X3,X1)
                        | ~ v1_funct_2(k2_tmap_1(sK0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(sK0,X1,X2,X3))
                        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                        | ~ v5_pre_topc(X2,sK0,X1)
                        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
                        | ~ v1_funct_1(X2) )
                      & ( ( m1_subset_1(k2_tmap_1(sK0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(sK0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(sK0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(sK0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(sK0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(sK0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(sK0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(sK0,X1,X2,X3)) )
                        | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,sK0,X1)
                          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
                          & v1_funct_1(X2) ) )
                      & r4_tsep_1(sK0,X3,X4)
                      & sK0 = k1_tsep_1(sK0,X3,X4)
                      & m1_pre_topc(X4,sK0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ( ~ m1_subset_1(k2_tmap_1(sK0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                      | ~ v5_pre_topc(k2_tmap_1(sK0,X1,X2,X4),X4,X1)
                      | ~ v1_funct_2(k2_tmap_1(sK0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                      | ~ v1_funct_1(k2_tmap_1(sK0,X1,X2,X4))
                      | ~ m1_subset_1(k2_tmap_1(sK0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v5_pre_topc(k2_tmap_1(sK0,X1,X2,X3),X3,X1)
                      | ~ v1_funct_2(k2_tmap_1(sK0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(k2_tmap_1(sK0,X1,X2,X3))
                      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X2,sK0,X1)
                      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
                      | ~ v1_funct_1(X2) )
                    & ( ( m1_subset_1(k2_tmap_1(sK0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                        & v5_pre_topc(k2_tmap_1(sK0,X1,X2,X4),X4,X1)
                        & v1_funct_2(k2_tmap_1(sK0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                        & v1_funct_1(k2_tmap_1(sK0,X1,X2,X4))
                        & m1_subset_1(k2_tmap_1(sK0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v5_pre_topc(k2_tmap_1(sK0,X1,X2,X3),X3,X1)
                        & v1_funct_2(k2_tmap_1(sK0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(k2_tmap_1(sK0,X1,X2,X3)) )
                      | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                        & v5_pre_topc(X2,sK0,X1)
                        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
                        & v1_funct_1(X2) ) )
                    & r4_tsep_1(sK0,X3,X4)
                    & sK0 = k1_tsep_1(sK0,X3,X4)
                    & m1_pre_topc(X4,sK0)
                    & ~ v2_struct_0(X4) )
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
                    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,X2,X4),X4,sK1)
                    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,X2,X4),u1_struct_0(X4),u1_struct_0(sK1))
                    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,X2,X4))
                    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,X2,X3),X3,sK1)
                    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,X2,X3),u1_struct_0(X3),u1_struct_0(sK1))
                    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,X2,X3))
                    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                    | ~ v5_pre_topc(X2,sK0,sK1)
                    | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
                    | ~ v1_funct_1(X2) )
                  & ( ( m1_subset_1(k2_tmap_1(sK0,sK1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
                      & v5_pre_topc(k2_tmap_1(sK0,sK1,X2,X4),X4,sK1)
                      & v1_funct_2(k2_tmap_1(sK0,sK1,X2,X4),u1_struct_0(X4),u1_struct_0(sK1))
                      & v1_funct_1(k2_tmap_1(sK0,sK1,X2,X4))
                      & m1_subset_1(k2_tmap_1(sK0,sK1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                      & v5_pre_topc(k2_tmap_1(sK0,sK1,X2,X3),X3,sK1)
                      & v1_funct_2(k2_tmap_1(sK0,sK1,X2,X3),u1_struct_0(X3),u1_struct_0(sK1))
                      & v1_funct_1(k2_tmap_1(sK0,sK1,X2,X3)) )
                    | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                      & v5_pre_topc(X2,sK0,sK1)
                      & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
                      & v1_funct_1(X2) ) )
                  & r4_tsep_1(sK0,X3,X4)
                  & sK0 = k1_tsep_1(sK0,X3,X4)
                  & m1_pre_topc(X4,sK0)
                  & ~ v2_struct_0(X4) )
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
                  | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,X2,X4),X4,sK1)
                  | ~ v1_funct_2(k2_tmap_1(sK0,sK1,X2,X4),u1_struct_0(X4),u1_struct_0(sK1))
                  | ~ v1_funct_1(k2_tmap_1(sK0,sK1,X2,X4))
                  | ~ m1_subset_1(k2_tmap_1(sK0,sK1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                  | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,X2,X3),X3,sK1)
                  | ~ v1_funct_2(k2_tmap_1(sK0,sK1,X2,X3),u1_struct_0(X3),u1_struct_0(sK1))
                  | ~ v1_funct_1(k2_tmap_1(sK0,sK1,X2,X3))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                  | ~ v5_pre_topc(X2,sK0,sK1)
                  | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
                  | ~ v1_funct_1(X2) )
                & ( ( m1_subset_1(k2_tmap_1(sK0,sK1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
                    & v5_pre_topc(k2_tmap_1(sK0,sK1,X2,X4),X4,sK1)
                    & v1_funct_2(k2_tmap_1(sK0,sK1,X2,X4),u1_struct_0(X4),u1_struct_0(sK1))
                    & v1_funct_1(k2_tmap_1(sK0,sK1,X2,X4))
                    & m1_subset_1(k2_tmap_1(sK0,sK1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                    & v5_pre_topc(k2_tmap_1(sK0,sK1,X2,X3),X3,sK1)
                    & v1_funct_2(k2_tmap_1(sK0,sK1,X2,X3),u1_struct_0(X3),u1_struct_0(sK1))
                    & v1_funct_1(k2_tmap_1(sK0,sK1,X2,X3)) )
                  | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                    & v5_pre_topc(X2,sK0,sK1)
                    & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
                    & v1_funct_1(X2) ) )
                & r4_tsep_1(sK0,X3,X4)
                & sK0 = k1_tsep_1(sK0,X3,X4)
                & m1_pre_topc(X4,sK0)
                & ~ v2_struct_0(X4) )
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
                | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X4),X4,sK1)
                | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X4),u1_struct_0(X4),u1_struct_0(sK1))
                | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X4))
                | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X3),X3,sK1)
                | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X3),u1_struct_0(X3),u1_struct_0(sK1))
                | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X3))
                | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                | ~ v5_pre_topc(sK2,sK0,sK1)
                | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
                | ~ v1_funct_1(sK2) )
              & ( ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
                  & v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X4),X4,sK1)
                  & v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X4),u1_struct_0(X4),u1_struct_0(sK1))
                  & v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X4))
                  & m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                  & v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X3),X3,sK1)
                  & v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X3),u1_struct_0(X3),u1_struct_0(sK1))
                  & v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X3)) )
                | ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                  & v5_pre_topc(sK2,sK0,sK1)
                  & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
                  & v1_funct_1(sK2) ) )
              & r4_tsep_1(sK0,X3,X4)
              & sK0 = k1_tsep_1(sK0,X3,X4)
              & m1_pre_topc(X4,sK0)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
              | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X4),X4,sK1)
              | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X4),u1_struct_0(X4),u1_struct_0(sK1))
              | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X4))
              | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
              | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X3),X3,sK1)
              | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X3),u1_struct_0(X3),u1_struct_0(sK1))
              | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X3))
              | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
              | ~ v5_pre_topc(sK2,sK0,sK1)
              | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
              | ~ v1_funct_1(sK2) )
            & ( ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
                & v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X4),X4,sK1)
                & v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X4),u1_struct_0(X4),u1_struct_0(sK1))
                & v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X4))
                & m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                & v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X3),X3,sK1)
                & v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X3),u1_struct_0(X3),u1_struct_0(sK1))
                & v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X3)) )
              | ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                & v5_pre_topc(sK2,sK0,sK1)
                & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
                & v1_funct_1(sK2) ) )
            & r4_tsep_1(sK0,X3,X4)
            & sK0 = k1_tsep_1(sK0,X3,X4)
            & m1_pre_topc(X4,sK0)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
            | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X4),X4,sK1)
            | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X4),u1_struct_0(X4),u1_struct_0(sK1))
            | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X4))
            | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
            | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
            | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
            | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
            | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
            | ~ v5_pre_topc(sK2,sK0,sK1)
            | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
            | ~ v1_funct_1(sK2) )
          & ( ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
              & v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X4),X4,sK1)
              & v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X4),u1_struct_0(X4),u1_struct_0(sK1))
              & v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X4))
              & m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
              & v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
              & v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
              & v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) )
            | ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
              & v5_pre_topc(sK2,sK0,sK1)
              & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
              & v1_funct_1(sK2) ) )
          & r4_tsep_1(sK0,sK3,X4)
          & sK0 = k1_tsep_1(sK0,sK3,X4)
          & m1_pre_topc(X4,sK0)
          & ~ v2_struct_0(X4) )
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X4] :
        ( ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
          | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X4),X4,sK1)
          | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X4),u1_struct_0(X4),u1_struct_0(sK1))
          | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X4))
          | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
          | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
          | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
          | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
          | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          | ~ v5_pre_topc(sK2,sK0,sK1)
          | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
          | ~ v1_funct_1(sK2) )
        & ( ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
            & v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X4),X4,sK1)
            & v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X4),u1_struct_0(X4),u1_struct_0(sK1))
            & v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X4))
            & m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
            & v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
            & v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
            & v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) )
          | ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
            & v5_pre_topc(sK2,sK0,sK1)
            & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
            & v1_funct_1(sK2) ) )
        & r4_tsep_1(sK0,sK3,X4)
        & sK0 = k1_tsep_1(sK0,sK3,X4)
        & m1_pre_topc(X4,sK0)
        & ~ v2_struct_0(X4) )
   => ( ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2) )
      & ( ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
          & v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
          & v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
          & v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
          & m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
          & v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
          & v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
          & v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) )
        | ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v5_pre_topc(sK2,sK0,sK1)
          & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(sK2) ) )
      & r4_tsep_1(sK0,sK3,sK4)
      & sK0 = k1_tsep_1(sK0,sK3,sK4)
      & m1_pre_topc(sK4,sK0)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
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
                      & r4_tsep_1(X0,X3,X4)
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
                      & r4_tsep_1(X0,X3,X4)
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
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
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
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
                      & r4_tsep_1(X0,X3,X4)
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
                      & r4_tsep_1(X0,X3,X4)
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
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
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
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
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_tmap_1)).

fof(f406,plain,(
    v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f405,f29])).

fof(f29,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f405,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f404,f30])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f404,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f403,f36])).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f25])).

fof(f403,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f402,f110])).

fof(f110,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(subsumption_resolution,[],[f109,f28])).

fof(f109,plain,
    ( m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f108,f30])).

fof(f108,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f107,f37])).

fof(f37,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f107,plain,
    ( m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f106,f38])).

fof(f38,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f106,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f105,f39])).

fof(f39,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f105,plain,
    ( m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f104,f40])).

fof(f40,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f104,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f91,f41])).

fof(f41,plain,(
    sK0 = k1_tsep_1(sK0,sK3,sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(f402,plain,
    ( ~ m1_pre_topc(sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f401,f38])).

fof(f401,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f400,f34])).

fof(f34,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f400,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f399,f35])).

fof(f35,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f399,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f398,f348])).

fof(f348,plain,(
    v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f45,f347])).

fof(f347,plain,(
    ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f346,f34])).

fof(f346,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f345,f35])).

fof(f345,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f344,f36])).

fof(f344,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(duplicate_literal_removal,[],[f343])).

fof(f343,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f339,f192])).

fof(f192,plain,(
    ! [X0] :
      ( v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK3),sK3,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f191,f28])).

fof(f191,plain,(
    ! [X0] :
      ( v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK3),sK3,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f190,f29])).

fof(f190,plain,(
    ! [X0] :
      ( v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK3),sK3,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f189,f30])).

fof(f189,plain,(
    ! [X0] :
      ( v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK3),sK3,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f188,f110])).

fof(f188,plain,(
    ! [X0] :
      ( v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK3),sK3,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f187,f38])).

fof(f187,plain,(
    ! [X0] :
      ( v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK3),sK3,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f186,f31])).

fof(f31,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f186,plain,(
    ! [X0] :
      ( v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK3),sK3,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f185,f32])).

fof(f32,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f185,plain,(
    ! [X0] :
      ( v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK3),sK3,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f184,f33])).

fof(f33,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f184,plain,(
    ! [X0] :
      ( v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK3),sK3,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f183])).

fof(f183,plain,(
    ! [X0] :
      ( v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK3),sK3,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(sK3,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f182,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( k2_tmap_1(X0,sK1,X1,X2) = k3_tmap_1(sK0,sK1,X0,X2,X1)
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | ~ m1_pre_topc(X2,sK0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f128,f31])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( k2_tmap_1(X0,sK1,X1,X2) = k3_tmap_1(sK0,sK1,X0,X2,X1)
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | ~ m1_pre_topc(X2,sK0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f127,f32])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( k2_tmap_1(X0,sK1,X1,X2) = k3_tmap_1(sK0,sK1,X0,X2,X1)
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | ~ m1_pre_topc(X2,sK0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X2,X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f126,f33])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( k2_tmap_1(X0,sK1,X1,X2) = k3_tmap_1(sK0,sK1,X0,X2,X1)
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | ~ m1_pre_topc(X2,sK0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( k2_tmap_1(X0,sK1,X1,X2) = k3_tmap_1(sK0,sK1,X0,X2,X1)
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | ~ m1_pre_topc(X2,sK0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f120,f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( k3_tmap_1(sK0,sK1,X1,X2,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(sK1),X0,u1_struct_0(X2))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(X2,sK0)
      | ~ m1_pre_topc(X1,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X2,X1) ) ),
    inference(subsumption_resolution,[],[f119,f28])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(X2,sK0)
      | ~ m1_pre_topc(X1,sK0)
      | k3_tmap_1(sK0,sK1,X1,X2,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(sK1),X0,u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f117,f29])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(X2,sK0)
      | ~ m1_pre_topc(X1,sK0)
      | k3_tmap_1(sK0,sK1,X1,X2,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(sK1),X0,u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X1)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f116,f30])).

fof(f116,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ l1_pre_topc(X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
      | ~ v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK1))
      | ~ v1_funct_1(X6)
      | ~ m1_pre_topc(X4,X7)
      | ~ m1_pre_topc(X5,X7)
      | k3_tmap_1(X7,sK1,X5,X4,X6) = k2_partfun1(u1_struct_0(X5),u1_struct_0(sK1),X6,u1_struct_0(X4))
      | ~ m1_pre_topc(X4,X5)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7) ) ),
    inference(subsumption_resolution,[],[f115,f31])).

fof(f115,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_pre_topc(X4,X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
      | ~ v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK1))
      | ~ v1_funct_1(X6)
      | ~ m1_pre_topc(X4,X7)
      | ~ m1_pre_topc(X5,X7)
      | k3_tmap_1(X7,sK1,X5,X4,X6) = k2_partfun1(u1_struct_0(X5),u1_struct_0(sK1),X6,u1_struct_0(X4))
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7) ) ),
    inference(subsumption_resolution,[],[f112,f32])).

fof(f112,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_pre_topc(X4,X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
      | ~ v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK1))
      | ~ v1_funct_1(X6)
      | ~ m1_pre_topc(X4,X7)
      | ~ m1_pre_topc(X5,X7)
      | k3_tmap_1(X7,sK1,X5,X4,X6) = k2_partfun1(u1_struct_0(X5),u1_struct_0(sK1),X6,u1_struct_0(X4))
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7) ) ),
    inference(resolution,[],[f76,f33])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f182,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK3,X0),sK3,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f181,f28])).

fof(f181,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK3,X0),sK3,X1)
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f180,f29])).

fof(f180,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK3,X0),sK3,X1)
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f179,f30])).

fof(f179,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK3,X0),sK3,X1)
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f178,f37])).

fof(f178,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK3,X0),sK3,X1)
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f177,f38])).

fof(f177,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK3,X0),sK3,X1)
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f176,f39])).

fof(f176,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK3,X0),sK3,X1)
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f175,f40])).

fof(f175,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK3,X0),sK3,X1)
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f174,f42])).

fof(f42,plain,(
    r4_tsep_1(sK0,sK3,sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f174,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK3,X0),sK3,X1)
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f94,f41])).

fof(f94,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
      | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
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
    inference(duplicate_literal_removal,[],[f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
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
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(X4) )
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
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          | ~ v1_funct_1(X4) ) )
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(X4) )
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
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          | ~ v1_funct_1(X4) ) )
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_tmap_1)).

fof(f339,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f338,f34])).

fof(f338,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f337,f35])).

fof(f337,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f336,f36])).

fof(f336,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(duplicate_literal_removal,[],[f335])).

fof(f335,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f331,f211])).

fof(f211,plain,(
    ! [X0] :
      ( v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f210,f28])).

fof(f210,plain,(
    ! [X0] :
      ( v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f209,f29])).

fof(f209,plain,(
    ! [X0] :
      ( v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f208,f30])).

fof(f208,plain,(
    ! [X0] :
      ( v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f207,f110])).

fof(f207,plain,(
    ! [X0] :
      ( v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f206,f40])).

fof(f206,plain,(
    ! [X0] :
      ( v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f205,f31])).

fof(f205,plain,(
    ! [X0] :
      ( v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f204,f32])).

fof(f204,plain,(
    ! [X0] :
      ( v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f203,f33])).

fof(f203,plain,(
    ! [X0] :
      ( v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f202])).

fof(f202,plain,(
    ! [X0] :
      ( v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(sK4,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f201,f129])).

fof(f201,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK4,X0),sK4,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f200,f28])).

fof(f200,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK4,X0),sK4,X1)
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f199,f29])).

fof(f199,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK4,X0),sK4,X1)
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f198,f30])).

fof(f198,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK4,X0),sK4,X1)
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f197,f37])).

fof(f197,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK4,X0),sK4,X1)
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f196,f38])).

fof(f196,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK4,X0),sK4,X1)
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f195,f39])).

fof(f195,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK4,X0),sK4,X1)
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f194,f40])).

fof(f194,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK4,X0),sK4,X1)
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f193,f42])).

fof(f193,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK4,X0),sK4,X1)
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f98,f41])).

fof(f98,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
      | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
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
    inference(duplicate_literal_removal,[],[f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
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
    inference(cnf_transformation,[],[f27])).

fof(f331,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f330,f34])).

fof(f330,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f329,f35])).

fof(f329,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f328,f36])).

fof(f328,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(duplicate_literal_removal,[],[f327])).

fof(f327,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f324,f272])).

fof(f272,plain,(
    ! [X0] :
      ( m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f271,f28])).

fof(f271,plain,(
    ! [X0] :
      ( m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f270,f29])).

fof(f270,plain,(
    ! [X0] :
      ( m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f269,f30])).

fof(f269,plain,(
    ! [X0] :
      ( m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f268,f110])).

fof(f268,plain,(
    ! [X0] :
      ( m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f267,f38])).

fof(f267,plain,(
    ! [X0] :
      ( m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f266,f31])).

fof(f266,plain,(
    ! [X0] :
      ( m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f265,f32])).

fof(f265,plain,(
    ! [X0] :
      ( m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f261,f33])).

fof(f261,plain,(
    ! [X0] :
      ( m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f260])).

fof(f260,plain,(
    ! [X0] :
      ( m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(sK3,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f258,f129])).

fof(f258,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f257,f28])).

fof(f257,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f256,f29])).

fof(f256,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f255,f30])).

fof(f255,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f254,f37])).

fof(f254,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f253,f38])).

fof(f253,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f252,f39])).

fof(f252,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f251,f40])).

fof(f251,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f250,f42])).

fof(f250,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f95,f41])).

fof(f95,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
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
    inference(duplicate_literal_removal,[],[f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
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
    inference(cnf_transformation,[],[f27])).

fof(f324,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f323,f34])).

fof(f323,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f322,f35])).

fof(f322,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f321,f36])).

fof(f321,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(duplicate_literal_removal,[],[f320])).

fof(f320,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f317,f295])).

fof(f295,plain,(
    ! [X0] :
      ( m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f294,f28])).

fof(f294,plain,(
    ! [X0] :
      ( m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f293,f29])).

fof(f293,plain,(
    ! [X0] :
      ( m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f292,f30])).

fof(f292,plain,(
    ! [X0] :
      ( m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f291,f110])).

fof(f291,plain,(
    ! [X0] :
      ( m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f290,f40])).

fof(f290,plain,(
    ! [X0] :
      ( m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f289,f31])).

fof(f289,plain,(
    ! [X0] :
      ( m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f288,f32])).

fof(f288,plain,(
    ! [X0] :
      ( m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f284,f33])).

fof(f284,plain,(
    ! [X0] :
      ( m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f283])).

fof(f283,plain,(
    ! [X0] :
      ( m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(sK4,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f281,f129])).

fof(f281,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f280,f28])).

fof(f280,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f279,f29])).

fof(f279,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f278,f30])).

fof(f278,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f277,f37])).

fof(f277,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f276,f38])).

fof(f276,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f275,f39])).

fof(f275,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f274,f40])).

fof(f274,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f273,f42])).

fof(f273,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f99,f41])).

fof(f99,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
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
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
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
    inference(cnf_transformation,[],[f27])).

fof(f317,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f316,f34])).

fof(f316,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f315,f35])).

fof(f315,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f314,f36])).

fof(f314,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(duplicate_literal_removal,[],[f313])).

fof(f313,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f311,f230])).

fof(f230,plain,(
    ! [X0] :
      ( v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f229,f28])).

fof(f229,plain,(
    ! [X0] :
      ( v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f228,f29])).

fof(f228,plain,(
    ! [X0] :
      ( v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f227,f30])).

fof(f227,plain,(
    ! [X0] :
      ( v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f226,f110])).

% (19973)Refutation not found, incomplete strategy% (19973)------------------------------
% (19973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f226,plain,(
    ! [X0] :
      ( v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f225,f38])).

fof(f225,plain,(
    ! [X0] :
      ( v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f224,f31])).

fof(f224,plain,(
    ! [X0] :
      ( v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f223,f32])).

fof(f223,plain,(
    ! [X0] :
      ( v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f222,f33])).

fof(f222,plain,(
    ! [X0] :
      ( v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f221])).

fof(f221,plain,(
    ! [X0] :
      ( v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(sK3,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f220,f129])).

fof(f220,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f219,f28])).

fof(f219,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(X1))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f218,f29])).

fof(f218,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(X1))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f217,f30])).

fof(f217,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(X1))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f216,f37])).

fof(f216,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(X1))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f215,f38])).

fof(f215,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(X1))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f214,f39])).

fof(f214,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(X1))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f213,f40])).

fof(f213,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(X1))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f212,f42])).

fof(f212,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(X1))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f93,f41])).

fof(f93,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
      | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
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
    inference(duplicate_literal_removal,[],[f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
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
    inference(cnf_transformation,[],[f27])).

fof(f311,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f310,f34])).

fof(f310,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f309,f35])).

fof(f309,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f308,f36])).

fof(f308,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(duplicate_literal_removal,[],[f307])).

fof(f307,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f305,f249])).

fof(f249,plain,(
    ! [X0] :
      ( v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f248,f28])).

fof(f248,plain,(
    ! [X0] :
      ( v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f247,f29])).

fof(f247,plain,(
    ! [X0] :
      ( v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f246,f30])).

fof(f246,plain,(
    ! [X0] :
      ( v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f245,f110])).

fof(f245,plain,(
    ! [X0] :
      ( v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f244,f40])).

fof(f244,plain,(
    ! [X0] :
      ( v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f243,f31])).

fof(f243,plain,(
    ! [X0] :
      ( v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f242,f32])).

fof(f242,plain,(
    ! [X0] :
      ( v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f241,f33])).

fof(f241,plain,(
    ! [X0] :
      ( v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f240])).

fof(f240,plain,(
    ! [X0] :
      ( v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(sK4,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f239,f129])).

fof(f239,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK4,X0),u1_struct_0(sK4),u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f238,f28])).

fof(f238,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK4,X0),u1_struct_0(sK4),u1_struct_0(X1))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f237,f29])).

fof(f237,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK4,X0),u1_struct_0(sK4),u1_struct_0(X1))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f236,f30])).

fof(f236,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK4,X0),u1_struct_0(sK4),u1_struct_0(X1))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f235,f37])).

fof(f235,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK4,X0),u1_struct_0(sK4),u1_struct_0(X1))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f234,f38])).

fof(f234,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK4,X0),u1_struct_0(sK4),u1_struct_0(X1))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f233,f39])).

fof(f233,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK4,X0),u1_struct_0(sK4),u1_struct_0(X1))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f232,f40])).

fof(f232,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK4,X0),u1_struct_0(sK4),u1_struct_0(X1))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f231,f42])).

fof(f231,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK4,X0),u1_struct_0(sK4),u1_struct_0(X1))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f97,f41])).

fof(f97,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
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
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
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
    inference(cnf_transformation,[],[f27])).

fof(f305,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f304,f34])).

fof(f304,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f303,f35])).

fof(f303,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f302,f36])).

fof(f302,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(duplicate_literal_removal,[],[f301])).

fof(f301,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f300,f154])).

fof(f154,plain,(
    ! [X0] :
      ( v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f153,f28])).

fof(f153,plain,(
    ! [X0] :
      ( v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f152,f29])).

fof(f152,plain,(
    ! [X0] :
      ( v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f151,f30])).

fof(f151,plain,(
    ! [X0] :
      ( v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f150,f110])).

fof(f150,plain,(
    ! [X0] :
      ( v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f149,f38])).

fof(f149,plain,(
    ! [X0] :
      ( v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f148,f31])).

fof(f148,plain,(
    ! [X0] :
      ( v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f147,f32])).

fof(f147,plain,(
    ! [X0] :
      ( v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f146,f33])).

fof(f146,plain,(
    ! [X0] :
      ( v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f145])).

fof(f145,plain,(
    ! [X0] :
      ( v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(sK3,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f144,f129])).

fof(f144,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f143,f28])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f142,f29])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f141,f30])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f140,f37])).

fof(f140,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f139,f38])).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f138,f39])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f137,f40])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f136,f42])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f92,f41])).

fof(f92,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))
      | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
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
    inference(duplicate_literal_removal,[],[f77])).

% (19973)Termination reason: Refutation not found, incomplete strategy
fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
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
    inference(cnf_transformation,[],[f27])).

% (19973)Memory used [KB]: 2430
% (19973)Time elapsed: 0.204 s
% (19973)------------------------------
% (19973)------------------------------
fof(f300,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f299,f34])).

fof(f299,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f298,f35])).

fof(f298,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f297,f36])).

fof(f297,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(duplicate_literal_removal,[],[f296])).

fof(f296,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f102,f173])).

fof(f173,plain,(
    ! [X0] :
      ( v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f172,f28])).

fof(f172,plain,(
    ! [X0] :
      ( v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f171,f29])).

fof(f171,plain,(
    ! [X0] :
      ( v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f170,f30])).

fof(f170,plain,(
    ! [X0] :
      ( v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f169,f110])).

fof(f169,plain,(
    ! [X0] :
      ( v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f168,f40])).

fof(f168,plain,(
    ! [X0] :
      ( v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f167,f31])).

fof(f167,plain,(
    ! [X0] :
      ( v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f166,f32])).

fof(f166,plain,(
    ! [X0] :
      ( v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f165,f33])).

fof(f165,plain,(
    ! [X0] :
      ( v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f164])).

fof(f164,plain,(
    ! [X0] :
      ( v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(sK4,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f163,f129])).

fof(f163,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f162,f28])).

fof(f162,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f161,f29])).

fof(f161,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f160,f30])).

fof(f160,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f159,f37])).

fof(f159,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f158,f38])).

fof(f158,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f157,f39])).

fof(f157,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f156,f40])).

fof(f156,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f155,f42])).

fof(f155,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0))
      | ~ v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f96,f41])).

fof(f96,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
      | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
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
    inference(duplicate_literal_removal,[],[f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
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
    inference(cnf_transformation,[],[f27])).

fof(f102,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f101,f34])).

fof(f101,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f100,f35])).

fof(f100,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f75,f36])).

fof(f75,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f45,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f25])).

fof(f398,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f397,f349])).

fof(f349,plain,(
    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f49,f347])).

fof(f49,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f397,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f396,f351])).

fof(f351,plain,(
    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f57,f347])).

fof(f57,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f25])).

fof(f396,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f395,f350])).

fof(f350,plain,(
    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) ),
    inference(subsumption_resolution,[],[f53,f347])).

fof(f53,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f395,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f394])).

fof(f394,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f392,f129])).

fof(f392,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) ),
    inference(subsumption_resolution,[],[f391,f34])).

fof(f391,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f390,f35])).

fof(f390,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f389,f355])).

fof(f355,plain,(
    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f73,f347])).

fof(f73,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f25])).

fof(f389,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f388,f352])).

fof(f352,plain,(
    v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) ),
    inference(subsumption_resolution,[],[f61,f347])).

fof(f61,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) ),
    inference(cnf_transformation,[],[f25])).

fof(f388,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f387,f353])).

fof(f353,plain,(
    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f65,f347])).

fof(f65,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f387,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f386,f354])).

fof(f354,plain,(
    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) ),
    inference(subsumption_resolution,[],[f69,f347])).

fof(f69,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f386,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f385,f36])).

fof(f385,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f384,f347])).

fof(f384,plain,(
    ! [X0] :
      ( v5_pre_topc(X0,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1)
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4))
      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,X0),sK3,sK1)
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0))
      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f383,f28])).

fof(f383,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1)
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4))
      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,X0),sK3,sK1)
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0))
      | v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f382,f29])).

fof(f382,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1)
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4))
      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,X0),sK3,sK1)
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0))
      | v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f381,f30])).

fof(f381,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1)
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4))
      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,X0),sK3,sK1)
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0))
      | v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f380,f110])).

fof(f380,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1)
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4))
      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,X0),sK3,sK1)
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0))
      | v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f379,f40])).

fof(f379,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1)
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4))
      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,X0),sK3,sK1)
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0))
      | v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f378,f31])).

fof(f378,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1)
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4))
      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,X0),sK3,sK1)
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0))
      | v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f377,f32])).

fof(f377,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1)
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4))
      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,X0),sK3,sK1)
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0))
      | v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f375,f33])).

fof(f375,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1)
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4))
      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,X0),sK3,sK1)
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0))
      | v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f374])).

fof(f374,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1)
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4))
      | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,X0),sK3,sK1)
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0))
      | v5_pre_topc(X0,sK0,sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ m1_pre_topc(sK0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(sK4,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f372,f129])).

fof(f372,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK4,X0),sK4,X1)
      | ~ v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK4,X0),u1_struct_0(sK4),u1_struct_0(X1))
      | ~ v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0))
      | ~ m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK3,X0),sK3,X1)
      | ~ v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(X1))
      | ~ v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0))
      | v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f371,f28])).

fof(f371,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | ~ m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK4,X0),sK4,X1)
      | ~ v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK4,X0),u1_struct_0(sK4),u1_struct_0(X1))
      | ~ v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0))
      | ~ m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK3,X0),sK3,X1)
      | ~ v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(X1))
      | ~ v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0))
      | v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f370,f29])).

fof(f370,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | ~ m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK4,X0),sK4,X1)
      | ~ v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK4,X0),u1_struct_0(sK4),u1_struct_0(X1))
      | ~ v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0))
      | ~ m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK3,X0),sK3,X1)
      | ~ v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(X1))
      | ~ v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0))
      | v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f369,f30])).

fof(f369,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | ~ m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK4,X0),sK4,X1)
      | ~ v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK4,X0),u1_struct_0(sK4),u1_struct_0(X1))
      | ~ v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0))
      | ~ m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK3,X0),sK3,X1)
      | ~ v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(X1))
      | ~ v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0))
      | v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f368,f37])).

fof(f368,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | ~ m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK4,X0),sK4,X1)
      | ~ v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK4,X0),u1_struct_0(sK4),u1_struct_0(X1))
      | ~ v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0))
      | ~ m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK3,X0),sK3,X1)
      | ~ v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(X1))
      | ~ v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0))
      | v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f367,f38])).

fof(f367,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | ~ m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK4,X0),sK4,X1)
      | ~ v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK4,X0),u1_struct_0(sK4),u1_struct_0(X1))
      | ~ v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0))
      | ~ m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK3,X0),sK3,X1)
      | ~ v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(X1))
      | ~ v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0))
      | v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f366,f39])).

fof(f366,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | ~ m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK4,X0),sK4,X1)
      | ~ v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK4,X0),u1_struct_0(sK4),u1_struct_0(X1))
      | ~ v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0))
      | ~ m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK3,X0),sK3,X1)
      | ~ v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(X1))
      | ~ v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0))
      | v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f365,f40])).

fof(f365,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | ~ m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK4,X0),sK4,X1)
      | ~ v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK4,X0),u1_struct_0(sK4),u1_struct_0(X1))
      | ~ v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0))
      | ~ m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK3,X0),sK3,X1)
      | ~ v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(X1))
      | ~ v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0))
      | v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f364,f42])).

fof(f364,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | ~ m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK4,X0),sK4,X1)
      | ~ v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK4,X0),u1_struct_0(sK4),u1_struct_0(X1))
      | ~ v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0))
      | ~ m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK3,X0),sK3,X1)
      | ~ v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(X1))
      | ~ v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0))
      | v5_pre_topc(X0,sK0,X1)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f87,f41])).

fof(f87,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
      | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
      | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
      | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))
      | v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
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
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:01:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (19961)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.51  % (19978)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.51  % (19960)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.51  % (19958)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.51  % (19957)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.51  % (19965)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.51  % (19964)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (19974)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.52  % (19960)Refutation not found, incomplete strategy% (19960)------------------------------
% 0.21/0.52  % (19960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (19966)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.52  % (19959)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.52  % (19975)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.52  % (19979)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.52  % (19964)Refutation not found, incomplete strategy% (19964)------------------------------
% 0.21/0.52  % (19964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (19964)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (19964)Memory used [KB]: 6396
% 0.21/0.52  % (19964)Time elapsed: 0.100 s
% 0.21/0.52  % (19964)------------------------------
% 0.21/0.52  % (19964)------------------------------
% 0.21/0.52  % (19968)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.52  % (19967)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.52  % (19969)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.52  % (19960)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (19960)Memory used [KB]: 10618
% 0.21/0.52  % (19960)Time elapsed: 0.100 s
% 0.21/0.52  % (19960)------------------------------
% 0.21/0.52  % (19960)------------------------------
% 0.21/0.53  % (19977)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.53  % (19963)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.53  % (19973)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.54  % (19972)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.54  % (19971)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.55  % (19962)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.55  % (19976)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.56  % (19980)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 1.37/0.56  % (19970)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 1.37/0.56  % (19980)Refutation not found, incomplete strategy% (19980)------------------------------
% 1.37/0.56  % (19980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.56  % (19980)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.56  
% 1.37/0.56  % (19980)Memory used [KB]: 10746
% 1.37/0.56  % (19980)Time elapsed: 0.151 s
% 1.37/0.56  % (19980)------------------------------
% 1.37/0.56  % (19980)------------------------------
% 1.37/0.56  % (19977)Refutation not found, incomplete strategy% (19977)------------------------------
% 1.37/0.56  % (19977)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.56  % (19977)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.56  
% 1.37/0.56  % (19977)Memory used [KB]: 6396
% 1.37/0.56  % (19977)Time elapsed: 0.150 s
% 1.37/0.56  % (19977)------------------------------
% 1.37/0.56  % (19977)------------------------------
% 1.37/0.57  % (19965)Refutation not found, incomplete strategy% (19965)------------------------------
% 1.37/0.57  % (19965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.57  % (19965)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.57  
% 1.37/0.57  % (19965)Memory used [KB]: 11257
% 1.37/0.57  % (19965)Time elapsed: 0.143 s
% 1.37/0.57  % (19965)------------------------------
% 1.37/0.57  % (19965)------------------------------
% 1.70/0.59  % (19976)Refutation found. Thanks to Tanya!
% 1.70/0.59  % SZS status Theorem for theBenchmark
% 1.70/0.59  % SZS output start Proof for theBenchmark
% 1.70/0.59  fof(f407,plain,(
% 1.70/0.59    $false),
% 1.70/0.59    inference(subsumption_resolution,[],[f406,f28])).
% 1.70/0.59  fof(f28,plain,(
% 1.70/0.59    ~v2_struct_0(sK0)),
% 1.70/0.59    inference(cnf_transformation,[],[f25])).
% 1.70/0.60  % (19967)Refutation not found, incomplete strategy% (19967)------------------------------
% 1.70/0.60  % (19967)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.60  % (19967)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.60  
% 1.70/0.60  % (19967)Memory used [KB]: 11769
% 1.70/0.60  % (19967)Time elapsed: 0.188 s
% 1.70/0.60  % (19967)------------------------------
% 1.70/0.60  % (19967)------------------------------
% 1.70/0.60  fof(f25,plain,(
% 1.70/0.60    (((((~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)) & ((m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) & v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) & v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) & v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) & m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) & v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))) | (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v5_pre_topc(sK2,sK0,sK1) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))) & r4_tsep_1(sK0,sK3,sK4) & sK0 = k1_tsep_1(sK0,sK3,sK4) & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.70/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f19,f24,f23,f22,f21,f20])).
% 1.70/0.60  fof(f20,plain,(
% 1.70/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(sK0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(sK0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(sK0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,sK0,X1) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(sK0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(sK0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(sK0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(sK0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v5_pre_topc(X2,sK0,X1) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(sK0,X3,X4) & sK0 = k1_tsep_1(sK0,X3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.70/0.60    introduced(choice_axiom,[])).
% 1.70/0.60  fof(f21,plain,(
% 1.70/0.60    ? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(sK0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(sK0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(sK0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,sK0,X1) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(sK0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(sK0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(sK0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(sK0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v5_pre_topc(X2,sK0,X1) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(sK0,X3,X4) & sK0 = k1_tsep_1(sK0,X3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK0,sK1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,X2,X4),X4,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,X2,X4),u1_struct_0(X4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,X2,X4)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,X2,X3),X3,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,X2,X3),u1_struct_0(X3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X2,sK0,sK1) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(sK0,sK1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) & v5_pre_topc(k2_tmap_1(sK0,sK1,X2,X4),X4,sK1) & v1_funct_2(k2_tmap_1(sK0,sK1,X2,X4),u1_struct_0(X4),u1_struct_0(sK1)) & v1_funct_1(k2_tmap_1(sK0,sK1,X2,X4)) & m1_subset_1(k2_tmap_1(sK0,sK1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v5_pre_topc(k2_tmap_1(sK0,sK1,X2,X3),X3,sK1) & v1_funct_2(k2_tmap_1(sK0,sK1,X2,X3),u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(k2_tmap_1(sK0,sK1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v5_pre_topc(X2,sK0,sK1) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2))) & r4_tsep_1(sK0,X3,X4) & sK0 = k1_tsep_1(sK0,X3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.70/0.60    introduced(choice_axiom,[])).
% 1.70/0.60  fof(f22,plain,(
% 1.70/0.60    ? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK0,sK1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,X2,X4),X4,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,X2,X4),u1_struct_0(X4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,X2,X4)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,X2,X3),X3,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,X2,X3),u1_struct_0(X3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X2,sK0,sK1) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(sK0,sK1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) & v5_pre_topc(k2_tmap_1(sK0,sK1,X2,X4),X4,sK1) & v1_funct_2(k2_tmap_1(sK0,sK1,X2,X4),u1_struct_0(X4),u1_struct_0(sK1)) & v1_funct_1(k2_tmap_1(sK0,sK1,X2,X4)) & m1_subset_1(k2_tmap_1(sK0,sK1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v5_pre_topc(k2_tmap_1(sK0,sK1,X2,X3),X3,sK1) & v1_funct_2(k2_tmap_1(sK0,sK1,X2,X3),u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(k2_tmap_1(sK0,sK1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v5_pre_topc(X2,sK0,sK1) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2))) & r4_tsep_1(sK0,X3,X4) & sK0 = k1_tsep_1(sK0,X3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X4),X4,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X4),u1_struct_0(X4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X4)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X3),X3,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X3),u1_struct_0(X3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X3)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)) & ((m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) & v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X4),X4,sK1) & v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X4),u1_struct_0(X4),u1_struct_0(sK1)) & v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X4)) & m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X3),X3,sK1) & v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X3),u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X3))) | (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v5_pre_topc(sK2,sK0,sK1) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))) & r4_tsep_1(sK0,X3,X4) & sK0 = k1_tsep_1(sK0,X3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 1.70/0.60    introduced(choice_axiom,[])).
% 1.70/0.60  fof(f23,plain,(
% 1.70/0.60    ? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X4),X4,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X4),u1_struct_0(X4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X4)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X3),X3,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X3),u1_struct_0(X3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X3)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)) & ((m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) & v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X4),X4,sK1) & v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X4),u1_struct_0(X4),u1_struct_0(sK1)) & v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X4)) & m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X3),X3,sK1) & v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X3),u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X3))) | (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v5_pre_topc(sK2,sK0,sK1) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))) & r4_tsep_1(sK0,X3,X4) & sK0 = k1_tsep_1(sK0,X3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : ((~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X4),X4,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X4),u1_struct_0(X4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X4)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)) & ((m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) & v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X4),X4,sK1) & v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X4),u1_struct_0(X4),u1_struct_0(sK1)) & v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X4)) & m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) & v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))) | (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v5_pre_topc(sK2,sK0,sK1) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))) & r4_tsep_1(sK0,sK3,X4) & sK0 = k1_tsep_1(sK0,sK3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 1.70/0.60    introduced(choice_axiom,[])).
% 1.70/0.60  fof(f24,plain,(
% 1.70/0.60    ? [X4] : ((~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X4),X4,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X4),u1_struct_0(X4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X4)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)) & ((m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1)))) & v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X4),X4,sK1) & v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X4),u1_struct_0(X4),u1_struct_0(sK1)) & v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X4)) & m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) & v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))) | (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v5_pre_topc(sK2,sK0,sK1) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))) & r4_tsep_1(sK0,sK3,X4) & sK0 = k1_tsep_1(sK0,sK3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) => ((~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)) & ((m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) & v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) & v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) & v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) & m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) & v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))) | (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v5_pre_topc(sK2,sK0,sK1) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))) & r4_tsep_1(sK0,sK3,sK4) & sK0 = k1_tsep_1(sK0,sK3,sK4) & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4))),
% 1.70/0.60    introduced(choice_axiom,[])).
% 1.70/0.60  fof(f19,plain,(
% 1.70/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.70/0.60    inference(flattening,[],[f18])).
% 1.70/0.60  fof(f18,plain,(
% 1.70/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.70/0.60    inference(nnf_transformation,[],[f9])).
% 1.70/0.60  fof(f9,plain,(
% 1.70/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.70/0.60    inference(flattening,[],[f8])).
% 1.70/0.60  fof(f8,plain,(
% 1.70/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & (r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0)) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.70/0.60    inference(ennf_transformation,[],[f6])).
% 1.70/0.60  fof(f6,negated_conjecture,(
% 1.70/0.60    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 1.70/0.60    inference(negated_conjecture,[],[f5])).
% 1.70/0.60  fof(f5,conjecture,(
% 1.70/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 1.70/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_tmap_1)).
% 1.70/0.60  fof(f406,plain,(
% 1.70/0.60    v2_struct_0(sK0)),
% 1.70/0.60    inference(subsumption_resolution,[],[f405,f29])).
% 1.70/0.60  fof(f29,plain,(
% 1.70/0.60    v2_pre_topc(sK0)),
% 1.70/0.60    inference(cnf_transformation,[],[f25])).
% 1.70/0.60  fof(f405,plain,(
% 1.70/0.60    ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.70/0.60    inference(subsumption_resolution,[],[f404,f30])).
% 1.70/0.60  fof(f30,plain,(
% 1.70/0.60    l1_pre_topc(sK0)),
% 1.70/0.60    inference(cnf_transformation,[],[f25])).
% 1.70/0.60  fof(f404,plain,(
% 1.70/0.60    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.70/0.60    inference(subsumption_resolution,[],[f403,f36])).
% 1.70/0.60  fof(f36,plain,(
% 1.70/0.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.70/0.60    inference(cnf_transformation,[],[f25])).
% 1.70/0.60  fof(f403,plain,(
% 1.70/0.60    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.70/0.60    inference(subsumption_resolution,[],[f402,f110])).
% 1.70/0.60  fof(f110,plain,(
% 1.70/0.60    m1_pre_topc(sK0,sK0)),
% 1.70/0.60    inference(subsumption_resolution,[],[f109,f28])).
% 1.70/0.60  fof(f109,plain,(
% 1.70/0.60    m1_pre_topc(sK0,sK0) | v2_struct_0(sK0)),
% 1.70/0.60    inference(subsumption_resolution,[],[f108,f30])).
% 1.70/0.60  fof(f108,plain,(
% 1.70/0.60    m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.70/0.60    inference(subsumption_resolution,[],[f107,f37])).
% 1.70/0.60  fof(f37,plain,(
% 1.70/0.60    ~v2_struct_0(sK3)),
% 1.70/0.60    inference(cnf_transformation,[],[f25])).
% 1.70/0.60  fof(f107,plain,(
% 1.70/0.60    m1_pre_topc(sK0,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.70/0.60    inference(subsumption_resolution,[],[f106,f38])).
% 1.70/0.60  fof(f38,plain,(
% 1.70/0.60    m1_pre_topc(sK3,sK0)),
% 1.70/0.60    inference(cnf_transformation,[],[f25])).
% 1.70/0.60  fof(f106,plain,(
% 1.70/0.60    m1_pre_topc(sK0,sK0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.70/0.60    inference(subsumption_resolution,[],[f105,f39])).
% 1.70/0.60  fof(f39,plain,(
% 1.70/0.60    ~v2_struct_0(sK4)),
% 1.70/0.60    inference(cnf_transformation,[],[f25])).
% 1.70/0.60  fof(f105,plain,(
% 1.70/0.60    m1_pre_topc(sK0,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.70/0.60    inference(subsumption_resolution,[],[f104,f40])).
% 1.70/0.60  fof(f40,plain,(
% 1.70/0.60    m1_pre_topc(sK4,sK0)),
% 1.70/0.60    inference(cnf_transformation,[],[f25])).
% 1.70/0.60  fof(f104,plain,(
% 1.70/0.60    m1_pre_topc(sK0,sK0) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.70/0.60    inference(superposition,[],[f91,f41])).
% 1.70/0.60  fof(f41,plain,(
% 1.70/0.60    sK0 = k1_tsep_1(sK0,sK3,sK4)),
% 1.70/0.60    inference(cnf_transformation,[],[f25])).
% 1.70/0.60  fof(f91,plain,(
% 1.70/0.60    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.60    inference(cnf_transformation,[],[f17])).
% 1.70/0.60  fof(f17,plain,(
% 1.70/0.60    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.70/0.60    inference(flattening,[],[f16])).
% 1.70/0.60  fof(f16,plain,(
% 1.70/0.60    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.70/0.60    inference(ennf_transformation,[],[f7])).
% 1.70/0.60  fof(f7,plain,(
% 1.70/0.60    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 1.70/0.60    inference(pure_predicate_removal,[],[f3])).
% 1.70/0.60  fof(f3,axiom,(
% 1.70/0.60    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 1.70/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 1.70/0.60  fof(f402,plain,(
% 1.70/0.60    ~m1_pre_topc(sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.70/0.60    inference(subsumption_resolution,[],[f401,f38])).
% 1.70/0.60  fof(f401,plain,(
% 1.70/0.60    ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.70/0.60    inference(subsumption_resolution,[],[f400,f34])).
% 1.70/0.60  fof(f34,plain,(
% 1.70/0.60    v1_funct_1(sK2)),
% 1.70/0.60    inference(cnf_transformation,[],[f25])).
% 1.70/0.60  fof(f400,plain,(
% 1.70/0.60    ~v1_funct_1(sK2) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.70/0.60    inference(subsumption_resolution,[],[f399,f35])).
% 1.70/0.60  fof(f35,plain,(
% 1.70/0.60    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.70/0.60    inference(cnf_transformation,[],[f25])).
% 1.70/0.60  fof(f399,plain,(
% 1.70/0.60    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.70/0.60    inference(subsumption_resolution,[],[f398,f348])).
% 1.70/0.60  fof(f348,plain,(
% 1.70/0.60    v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))),
% 1.70/0.60    inference(subsumption_resolution,[],[f45,f347])).
% 1.70/0.60  fof(f347,plain,(
% 1.70/0.60    ~v5_pre_topc(sK2,sK0,sK1)),
% 1.70/0.60    inference(subsumption_resolution,[],[f346,f34])).
% 1.70/0.60  fof(f346,plain,(
% 1.70/0.60    ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.70/0.60    inference(subsumption_resolution,[],[f345,f35])).
% 1.70/0.60  fof(f345,plain,(
% 1.70/0.60    ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.60    inference(subsumption_resolution,[],[f344,f36])).
% 1.70/0.60  fof(f344,plain,(
% 1.70/0.60    ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.60    inference(duplicate_literal_removal,[],[f343])).
% 1.70/0.60  fof(f343,plain,(
% 1.70/0.60    ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.60    inference(resolution,[],[f339,f192])).
% 1.70/0.60  fof(f192,plain,(
% 1.70/0.60    ( ! [X0] : (v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK3),sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0)) )),
% 1.70/0.60    inference(subsumption_resolution,[],[f191,f28])).
% 1.70/0.60  fof(f191,plain,(
% 1.70/0.60    ( ! [X0] : (v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK3),sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | v2_struct_0(sK0)) )),
% 1.70/0.60    inference(subsumption_resolution,[],[f190,f29])).
% 1.70/0.60  fof(f190,plain,(
% 1.70/0.60    ( ! [X0] : (v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK3),sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.60    inference(subsumption_resolution,[],[f189,f30])).
% 1.70/0.60  fof(f189,plain,(
% 1.70/0.60    ( ! [X0] : (v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK3),sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.60    inference(subsumption_resolution,[],[f188,f110])).
% 1.70/0.60  fof(f188,plain,(
% 1.70/0.60    ( ! [X0] : (v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK3),sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.60    inference(subsumption_resolution,[],[f187,f38])).
% 1.70/0.60  fof(f187,plain,(
% 1.70/0.60    ( ! [X0] : (v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK3),sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.60    inference(subsumption_resolution,[],[f186,f31])).
% 1.70/0.60  fof(f31,plain,(
% 1.70/0.60    ~v2_struct_0(sK1)),
% 1.70/0.60    inference(cnf_transformation,[],[f25])).
% 1.70/0.60  fof(f186,plain,(
% 1.70/0.60    ( ! [X0] : (v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK3),sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.60    inference(subsumption_resolution,[],[f185,f32])).
% 1.70/0.60  fof(f32,plain,(
% 1.70/0.60    v2_pre_topc(sK1)),
% 1.70/0.60    inference(cnf_transformation,[],[f25])).
% 1.70/0.60  fof(f185,plain,(
% 1.70/0.60    ( ! [X0] : (v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK3),sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.60    inference(subsumption_resolution,[],[f184,f33])).
% 1.70/0.60  fof(f33,plain,(
% 1.70/0.60    l1_pre_topc(sK1)),
% 1.70/0.60    inference(cnf_transformation,[],[f25])).
% 1.70/0.60  fof(f184,plain,(
% 1.70/0.60    ( ! [X0] : (v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK3),sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.60    inference(duplicate_literal_removal,[],[f183])).
% 1.70/0.60  fof(f183,plain,(
% 1.70/0.60    ( ! [X0] : (v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK3),sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.60    inference(superposition,[],[f182,f129])).
% 1.70/0.60  fof(f129,plain,(
% 1.70/0.60    ( ! [X2,X0,X1] : (k2_tmap_1(X0,sK1,X1,X2) = k3_tmap_1(sK0,sK1,X0,X2,X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.60    inference(subsumption_resolution,[],[f128,f31])).
% 1.70/0.60  fof(f128,plain,(
% 1.70/0.60    ( ! [X2,X0,X1] : (k2_tmap_1(X0,sK1,X1,X2) = k3_tmap_1(sK0,sK1,X0,X2,X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~m1_pre_topc(X2,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.60    inference(subsumption_resolution,[],[f127,f32])).
% 1.70/0.60  fof(f127,plain,(
% 1.70/0.60    ( ! [X2,X0,X1] : (k2_tmap_1(X0,sK1,X1,X2) = k3_tmap_1(sK0,sK1,X0,X2,X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~m1_pre_topc(X2,X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.60    inference(subsumption_resolution,[],[f126,f33])).
% 1.70/0.60  fof(f126,plain,(
% 1.70/0.60    ( ! [X2,X0,X1] : (k2_tmap_1(X0,sK1,X1,X2) = k3_tmap_1(sK0,sK1,X0,X2,X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.60    inference(duplicate_literal_removal,[],[f123])).
% 1.70/0.60  fof(f123,plain,(
% 1.70/0.60    ( ! [X2,X0,X1] : (k2_tmap_1(X0,sK1,X1,X2) = k3_tmap_1(sK0,sK1,X0,X2,X1) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.60    inference(superposition,[],[f120,f89])).
% 1.70/0.60  fof(f89,plain,(
% 1.70/0.60    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.60    inference(cnf_transformation,[],[f15])).
% 1.70/0.60  fof(f15,plain,(
% 1.70/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.70/0.60    inference(flattening,[],[f14])).
% 1.70/0.60  fof(f14,plain,(
% 1.70/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.70/0.60    inference(ennf_transformation,[],[f1])).
% 1.70/0.60  fof(f1,axiom,(
% 1.70/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 1.70/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 1.70/0.60  fof(f120,plain,(
% 1.70/0.60    ( ! [X2,X0,X1] : (k3_tmap_1(sK0,sK1,X1,X2,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(sK1),X0,u1_struct_0(X2)) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~m1_pre_topc(X2,X1)) )),
% 1.70/0.60    inference(subsumption_resolution,[],[f119,f28])).
% 1.70/0.60  fof(f119,plain,(
% 1.70/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X1,sK0) | k3_tmap_1(sK0,sK1,X1,X2,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(sK1),X0,u1_struct_0(X2)) | ~m1_pre_topc(X2,X1) | v2_struct_0(sK0)) )),
% 1.70/0.60    inference(subsumption_resolution,[],[f117,f29])).
% 1.70/0.60  fof(f117,plain,(
% 1.70/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X1,sK0) | k3_tmap_1(sK0,sK1,X1,X2,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(sK1),X0,u1_struct_0(X2)) | ~m1_pre_topc(X2,X1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.60    inference(resolution,[],[f116,f30])).
% 1.70/0.60  fof(f116,plain,(
% 1.70/0.60    ( ! [X6,X4,X7,X5] : (~l1_pre_topc(X7) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | ~v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK1)) | ~v1_funct_1(X6) | ~m1_pre_topc(X4,X7) | ~m1_pre_topc(X5,X7) | k3_tmap_1(X7,sK1,X5,X4,X6) = k2_partfun1(u1_struct_0(X5),u1_struct_0(sK1),X6,u1_struct_0(X4)) | ~m1_pre_topc(X4,X5) | ~v2_pre_topc(X7) | v2_struct_0(X7)) )),
% 1.70/0.60    inference(subsumption_resolution,[],[f115,f31])).
% 1.70/0.60  fof(f115,plain,(
% 1.70/0.60    ( ! [X6,X4,X7,X5] : (~m1_pre_topc(X4,X5) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | ~v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK1)) | ~v1_funct_1(X6) | ~m1_pre_topc(X4,X7) | ~m1_pre_topc(X5,X7) | k3_tmap_1(X7,sK1,X5,X4,X6) = k2_partfun1(u1_struct_0(X5),u1_struct_0(sK1),X6,u1_struct_0(X4)) | v2_struct_0(sK1) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7)) )),
% 1.70/0.60    inference(subsumption_resolution,[],[f112,f32])).
% 1.70/0.60  fof(f112,plain,(
% 1.70/0.60    ( ! [X6,X4,X7,X5] : (~m1_pre_topc(X4,X5) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | ~v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK1)) | ~v1_funct_1(X6) | ~m1_pre_topc(X4,X7) | ~m1_pre_topc(X5,X7) | k3_tmap_1(X7,sK1,X5,X4,X6) = k2_partfun1(u1_struct_0(X5),u1_struct_0(sK1),X6,u1_struct_0(X4)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7)) )),
% 1.70/0.60    inference(resolution,[],[f76,f33])).
% 1.70/0.60  fof(f76,plain,(
% 1.70/0.60    ( ! [X4,X2,X0,X3,X1] : (~l1_pre_topc(X1) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.60    inference(cnf_transformation,[],[f11])).
% 1.70/0.60  fof(f11,plain,(
% 1.70/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.70/0.60    inference(flattening,[],[f10])).
% 1.70/0.60  fof(f10,plain,(
% 1.70/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.70/0.60    inference(ennf_transformation,[],[f2])).
% 1.70/0.60  fof(f2,axiom,(
% 1.70/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 1.70/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).
% 1.70/0.60  fof(f182,plain,(
% 1.70/0.60    ( ! [X0,X1] : (v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK3,X0),sK3,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.70/0.60    inference(subsumption_resolution,[],[f181,f28])).
% 1.70/0.60  fof(f181,plain,(
% 1.70/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK3,X0),sK3,X1) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | v2_struct_0(sK0)) )),
% 1.70/0.60    inference(subsumption_resolution,[],[f180,f29])).
% 1.70/0.60  fof(f180,plain,(
% 1.70/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK3,X0),sK3,X1) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.60    inference(subsumption_resolution,[],[f179,f30])).
% 1.70/0.60  fof(f179,plain,(
% 1.70/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK3,X0),sK3,X1) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.60    inference(subsumption_resolution,[],[f178,f37])).
% 1.70/0.60  fof(f178,plain,(
% 1.70/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK3,X0),sK3,X1) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.60    inference(subsumption_resolution,[],[f177,f38])).
% 1.70/0.60  fof(f177,plain,(
% 1.70/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK3,X0),sK3,X1) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.60    inference(subsumption_resolution,[],[f176,f39])).
% 1.70/0.60  fof(f176,plain,(
% 1.70/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK3,X0),sK3,X1) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.60    inference(subsumption_resolution,[],[f175,f40])).
% 1.70/0.60  fof(f175,plain,(
% 1.70/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK3,X0),sK3,X1) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.60    inference(subsumption_resolution,[],[f174,f42])).
% 1.70/0.60  fof(f42,plain,(
% 1.70/0.60    r4_tsep_1(sK0,sK3,sK4)),
% 1.70/0.60    inference(cnf_transformation,[],[f25])).
% 1.70/0.60  fof(f174,plain,(
% 1.70/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK3,X0),sK3,X1) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~r4_tsep_1(sK0,sK3,sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.60    inference(superposition,[],[f94,f41])).
% 1.70/0.60  fof(f94,plain,(
% 1.70/0.60    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.60    inference(duplicate_literal_removal,[],[f79])).
% 1.70/0.60  fof(f79,plain,(
% 1.70/0.60    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.60    inference(cnf_transformation,[],[f27])).
% 1.70/0.60  fof(f27,plain,(
% 1.70/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.70/0.60    inference(flattening,[],[f26])).
% 1.70/0.61  fof(f26,plain,(
% 1.70/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | (~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.70/0.61    inference(nnf_transformation,[],[f13])).
% 1.70/0.61  fof(f13,plain,(
% 1.70/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.70/0.61    inference(flattening,[],[f12])).
% 1.70/0.61  fof(f12,plain,(
% 1.70/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.70/0.61    inference(ennf_transformation,[],[f4])).
% 1.70/0.61  fof(f4,axiom,(
% 1.70/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r4_tsep_1(X0,X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))))))))),
% 1.70/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_tmap_1)).
% 1.70/0.61  fof(f339,plain,(
% 1.70/0.61    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v5_pre_topc(sK2,sK0,sK1)),
% 1.70/0.61    inference(subsumption_resolution,[],[f338,f34])).
% 1.70/0.61  fof(f338,plain,(
% 1.70/0.61    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.70/0.61    inference(subsumption_resolution,[],[f337,f35])).
% 1.70/0.61  fof(f337,plain,(
% 1.70/0.61    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.61    inference(subsumption_resolution,[],[f336,f36])).
% 1.70/0.61  fof(f336,plain,(
% 1.70/0.61    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.61    inference(duplicate_literal_removal,[],[f335])).
% 1.70/0.61  fof(f335,plain,(
% 1.70/0.61    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.61    inference(resolution,[],[f331,f211])).
% 1.70/0.61  fof(f211,plain,(
% 1.70/0.61    ( ! [X0] : (v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f210,f28])).
% 1.70/0.61  fof(f210,plain,(
% 1.70/0.61    ( ! [X0] : (v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f209,f29])).
% 1.70/0.61  fof(f209,plain,(
% 1.70/0.61    ( ! [X0] : (v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f208,f30])).
% 1.70/0.61  fof(f208,plain,(
% 1.70/0.61    ( ! [X0] : (v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f207,f110])).
% 1.70/0.61  fof(f207,plain,(
% 1.70/0.61    ( ! [X0] : (v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f206,f40])).
% 1.70/0.61  fof(f206,plain,(
% 1.70/0.61    ( ! [X0] : (v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f205,f31])).
% 1.70/0.61  fof(f205,plain,(
% 1.70/0.61    ( ! [X0] : (v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | v2_struct_0(sK1) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f204,f32])).
% 1.70/0.61  fof(f204,plain,(
% 1.70/0.61    ( ! [X0] : (v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f203,f33])).
% 1.70/0.61  fof(f203,plain,(
% 1.70/0.61    ( ! [X0] : (v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(duplicate_literal_removal,[],[f202])).
% 1.70/0.61  fof(f202,plain,(
% 1.70/0.61    ( ! [X0] : (v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(sK4,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(superposition,[],[f201,f129])).
% 1.70/0.61  fof(f201,plain,(
% 1.70/0.61    ( ! [X0,X1] : (v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK4,X0),sK4,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f200,f28])).
% 1.70/0.61  fof(f200,plain,(
% 1.70/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK4,X0),sK4,X1) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f199,f29])).
% 1.70/0.61  fof(f199,plain,(
% 1.70/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK4,X0),sK4,X1) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f198,f30])).
% 1.70/0.61  fof(f198,plain,(
% 1.70/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK4,X0),sK4,X1) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f197,f37])).
% 1.70/0.61  fof(f197,plain,(
% 1.70/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK4,X0),sK4,X1) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f196,f38])).
% 1.70/0.61  fof(f196,plain,(
% 1.70/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK4,X0),sK4,X1) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f195,f39])).
% 1.70/0.61  fof(f195,plain,(
% 1.70/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK4,X0),sK4,X1) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f194,f40])).
% 1.70/0.61  fof(f194,plain,(
% 1.70/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK4,X0),sK4,X1) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f193,f42])).
% 1.70/0.61  fof(f193,plain,(
% 1.70/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK4,X0),sK4,X1) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~r4_tsep_1(sK0,sK3,sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(superposition,[],[f98,f41])).
% 1.70/0.61  fof(f98,plain,(
% 1.70/0.61    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.61    inference(duplicate_literal_removal,[],[f83])).
% 1.70/0.61  fof(f83,plain,(
% 1.70/0.61    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f27])).
% 1.70/0.61  fof(f331,plain,(
% 1.70/0.61    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v5_pre_topc(sK2,sK0,sK1)),
% 1.70/0.61    inference(subsumption_resolution,[],[f330,f34])).
% 1.70/0.61  fof(f330,plain,(
% 1.70/0.61    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.70/0.61    inference(subsumption_resolution,[],[f329,f35])).
% 1.70/0.61  fof(f329,plain,(
% 1.70/0.61    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.61    inference(subsumption_resolution,[],[f328,f36])).
% 1.70/0.61  fof(f328,plain,(
% 1.70/0.61    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.61    inference(duplicate_literal_removal,[],[f327])).
% 1.70/0.61  fof(f327,plain,(
% 1.70/0.61    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.61    inference(resolution,[],[f324,f272])).
% 1.70/0.61  fof(f272,plain,(
% 1.70/0.61    ( ! [X0] : (m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f271,f28])).
% 1.70/0.61  fof(f271,plain,(
% 1.70/0.61    ( ! [X0] : (m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f270,f29])).
% 1.70/0.61  fof(f270,plain,(
% 1.70/0.61    ( ! [X0] : (m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f269,f30])).
% 1.70/0.61  fof(f269,plain,(
% 1.70/0.61    ( ! [X0] : (m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f268,f110])).
% 1.70/0.61  fof(f268,plain,(
% 1.70/0.61    ( ! [X0] : (m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f267,f38])).
% 1.70/0.61  fof(f267,plain,(
% 1.70/0.61    ( ! [X0] : (m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f266,f31])).
% 1.70/0.61  fof(f266,plain,(
% 1.70/0.61    ( ! [X0] : (m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f265,f32])).
% 1.70/0.61  fof(f265,plain,(
% 1.70/0.61    ( ! [X0] : (m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f261,f33])).
% 1.70/0.61  fof(f261,plain,(
% 1.70/0.61    ( ! [X0] : (m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(duplicate_literal_removal,[],[f260])).
% 1.70/0.61  fof(f260,plain,(
% 1.70/0.61    ( ! [X0] : (m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(superposition,[],[f258,f129])).
% 1.70/0.61  fof(f258,plain,(
% 1.70/0.61    ( ! [X0,X1] : (m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f257,f28])).
% 1.70/0.61  fof(f257,plain,(
% 1.70/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f256,f29])).
% 1.70/0.61  fof(f256,plain,(
% 1.70/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f255,f30])).
% 1.70/0.61  fof(f255,plain,(
% 1.70/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f254,f37])).
% 1.70/0.61  fof(f254,plain,(
% 1.70/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f253,f38])).
% 1.70/0.61  fof(f253,plain,(
% 1.70/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f252,f39])).
% 1.70/0.61  fof(f252,plain,(
% 1.70/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f251,f40])).
% 1.70/0.61  fof(f251,plain,(
% 1.70/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f250,f42])).
% 1.70/0.61  fof(f250,plain,(
% 1.70/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~r4_tsep_1(sK0,sK3,sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(superposition,[],[f95,f41])).
% 1.70/0.61  fof(f95,plain,(
% 1.70/0.61    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.61    inference(duplicate_literal_removal,[],[f80])).
% 1.70/0.61  fof(f80,plain,(
% 1.70/0.61    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f27])).
% 1.70/0.61  fof(f324,plain,(
% 1.70/0.61    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v5_pre_topc(sK2,sK0,sK1)),
% 1.70/0.61    inference(subsumption_resolution,[],[f323,f34])).
% 1.70/0.61  fof(f323,plain,(
% 1.70/0.61    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.70/0.61    inference(subsumption_resolution,[],[f322,f35])).
% 1.70/0.61  fof(f322,plain,(
% 1.70/0.61    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.61    inference(subsumption_resolution,[],[f321,f36])).
% 1.70/0.61  fof(f321,plain,(
% 1.70/0.61    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.61    inference(duplicate_literal_removal,[],[f320])).
% 1.70/0.61  fof(f320,plain,(
% 1.70/0.61    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.61    inference(resolution,[],[f317,f295])).
% 1.70/0.61  fof(f295,plain,(
% 1.70/0.61    ( ! [X0] : (m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f294,f28])).
% 1.70/0.61  fof(f294,plain,(
% 1.70/0.61    ( ! [X0] : (m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f293,f29])).
% 1.70/0.61  fof(f293,plain,(
% 1.70/0.61    ( ! [X0] : (m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f292,f30])).
% 1.70/0.61  fof(f292,plain,(
% 1.70/0.61    ( ! [X0] : (m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f291,f110])).
% 1.70/0.61  fof(f291,plain,(
% 1.70/0.61    ( ! [X0] : (m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f290,f40])).
% 1.70/0.61  fof(f290,plain,(
% 1.70/0.61    ( ! [X0] : (m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f289,f31])).
% 1.70/0.61  fof(f289,plain,(
% 1.70/0.61    ( ! [X0] : (m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | v2_struct_0(sK1) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f288,f32])).
% 1.70/0.61  fof(f288,plain,(
% 1.70/0.61    ( ! [X0] : (m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f284,f33])).
% 1.70/0.61  fof(f284,plain,(
% 1.70/0.61    ( ! [X0] : (m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(duplicate_literal_removal,[],[f283])).
% 1.70/0.61  fof(f283,plain,(
% 1.70/0.61    ( ! [X0] : (m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(sK4,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(superposition,[],[f281,f129])).
% 1.70/0.61  fof(f281,plain,(
% 1.70/0.61    ( ! [X0,X1] : (m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f280,f28])).
% 1.70/0.61  fof(f280,plain,(
% 1.70/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f279,f29])).
% 1.70/0.61  fof(f279,plain,(
% 1.70/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f278,f30])).
% 1.70/0.61  fof(f278,plain,(
% 1.70/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f277,f37])).
% 1.70/0.61  fof(f277,plain,(
% 1.70/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f276,f38])).
% 1.70/0.61  fof(f276,plain,(
% 1.70/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f275,f39])).
% 1.70/0.61  fof(f275,plain,(
% 1.70/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f274,f40])).
% 1.70/0.61  fof(f274,plain,(
% 1.70/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f273,f42])).
% 1.70/0.61  fof(f273,plain,(
% 1.70/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~r4_tsep_1(sK0,sK3,sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(superposition,[],[f99,f41])).
% 1.70/0.61  fof(f99,plain,(
% 1.70/0.61    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.61    inference(duplicate_literal_removal,[],[f84])).
% 1.70/0.61  fof(f84,plain,(
% 1.70/0.61    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.61    inference(cnf_transformation,[],[f27])).
% 1.70/0.61  fof(f317,plain,(
% 1.70/0.61    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v5_pre_topc(sK2,sK0,sK1)),
% 1.70/0.61    inference(subsumption_resolution,[],[f316,f34])).
% 1.70/0.61  fof(f316,plain,(
% 1.70/0.61    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.70/0.61    inference(subsumption_resolution,[],[f315,f35])).
% 1.70/0.61  fof(f315,plain,(
% 1.70/0.61    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.61    inference(subsumption_resolution,[],[f314,f36])).
% 1.70/0.61  fof(f314,plain,(
% 1.70/0.61    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.61    inference(duplicate_literal_removal,[],[f313])).
% 1.70/0.61  fof(f313,plain,(
% 1.70/0.61    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.61    inference(resolution,[],[f311,f230])).
% 1.70/0.61  fof(f230,plain,(
% 1.70/0.61    ( ! [X0] : (v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f229,f28])).
% 1.70/0.61  fof(f229,plain,(
% 1.70/0.61    ( ! [X0] : (v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f228,f29])).
% 1.70/0.61  fof(f228,plain,(
% 1.70/0.61    ( ! [X0] : (v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f227,f30])).
% 1.70/0.61  fof(f227,plain,(
% 1.70/0.61    ( ! [X0] : (v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.61    inference(subsumption_resolution,[],[f226,f110])).
% 1.70/0.62  % (19973)Refutation not found, incomplete strategy% (19973)------------------------------
% 1.70/0.62  % (19973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.62  fof(f226,plain,(
% 1.70/0.62    ( ! [X0] : (v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f225,f38])).
% 1.70/0.62  fof(f225,plain,(
% 1.70/0.62    ( ! [X0] : (v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f224,f31])).
% 1.70/0.62  fof(f224,plain,(
% 1.70/0.62    ( ! [X0] : (v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f223,f32])).
% 1.70/0.62  fof(f223,plain,(
% 1.70/0.62    ( ! [X0] : (v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f222,f33])).
% 1.70/0.62  fof(f222,plain,(
% 1.70/0.62    ( ! [X0] : (v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(duplicate_literal_removal,[],[f221])).
% 1.70/0.62  fof(f221,plain,(
% 1.70/0.62    ( ! [X0] : (v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(superposition,[],[f220,f129])).
% 1.70/0.62  fof(f220,plain,(
% 1.70/0.62    ( ! [X0,X1] : (v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f219,f28])).
% 1.70/0.62  fof(f219,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(X1)) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f218,f29])).
% 1.70/0.62  fof(f218,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(X1)) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f217,f30])).
% 1.70/0.62  fof(f217,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(X1)) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f216,f37])).
% 1.70/0.62  fof(f216,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(X1)) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f215,f38])).
% 1.70/0.62  fof(f215,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(X1)) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f214,f39])).
% 1.70/0.62  fof(f214,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(X1)) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f213,f40])).
% 1.70/0.62  fof(f213,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(X1)) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f212,f42])).
% 1.70/0.62  fof(f212,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(X1)) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~r4_tsep_1(sK0,sK3,sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(superposition,[],[f93,f41])).
% 1.70/0.62  fof(f93,plain,(
% 1.70/0.62    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.62    inference(duplicate_literal_removal,[],[f78])).
% 1.70/0.62  fof(f78,plain,(
% 1.70/0.62    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.62    inference(cnf_transformation,[],[f27])).
% 1.70/0.62  fof(f311,plain,(
% 1.70/0.62    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v5_pre_topc(sK2,sK0,sK1)),
% 1.70/0.62    inference(subsumption_resolution,[],[f310,f34])).
% 1.70/0.62  fof(f310,plain,(
% 1.70/0.62    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.70/0.62    inference(subsumption_resolution,[],[f309,f35])).
% 1.70/0.62  fof(f309,plain,(
% 1.70/0.62    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.62    inference(subsumption_resolution,[],[f308,f36])).
% 1.70/0.62  fof(f308,plain,(
% 1.70/0.62    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.62    inference(duplicate_literal_removal,[],[f307])).
% 1.70/0.62  fof(f307,plain,(
% 1.70/0.62    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.62    inference(resolution,[],[f305,f249])).
% 1.70/0.62  fof(f249,plain,(
% 1.70/0.62    ( ! [X0] : (v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f248,f28])).
% 1.70/0.62  fof(f248,plain,(
% 1.70/0.62    ( ! [X0] : (v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f247,f29])).
% 1.70/0.62  fof(f247,plain,(
% 1.70/0.62    ( ! [X0] : (v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f246,f30])).
% 1.70/0.62  fof(f246,plain,(
% 1.70/0.62    ( ! [X0] : (v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f245,f110])).
% 1.70/0.62  fof(f245,plain,(
% 1.70/0.62    ( ! [X0] : (v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f244,f40])).
% 1.70/0.62  fof(f244,plain,(
% 1.70/0.62    ( ! [X0] : (v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f243,f31])).
% 1.70/0.62  fof(f243,plain,(
% 1.70/0.62    ( ! [X0] : (v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | v2_struct_0(sK1) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f242,f32])).
% 1.70/0.62  fof(f242,plain,(
% 1.70/0.62    ( ! [X0] : (v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f241,f33])).
% 1.70/0.62  fof(f241,plain,(
% 1.70/0.62    ( ! [X0] : (v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(duplicate_literal_removal,[],[f240])).
% 1.70/0.62  fof(f240,plain,(
% 1.70/0.62    ( ! [X0] : (v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(sK4,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(superposition,[],[f239,f129])).
% 1.70/0.62  fof(f239,plain,(
% 1.70/0.62    ( ! [X0,X1] : (v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK4,X0),u1_struct_0(sK4),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f238,f28])).
% 1.70/0.62  fof(f238,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK4,X0),u1_struct_0(sK4),u1_struct_0(X1)) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f237,f29])).
% 1.70/0.62  fof(f237,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK4,X0),u1_struct_0(sK4),u1_struct_0(X1)) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f236,f30])).
% 1.70/0.62  fof(f236,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK4,X0),u1_struct_0(sK4),u1_struct_0(X1)) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f235,f37])).
% 1.70/0.62  fof(f235,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK4,X0),u1_struct_0(sK4),u1_struct_0(X1)) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f234,f38])).
% 1.70/0.62  fof(f234,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK4,X0),u1_struct_0(sK4),u1_struct_0(X1)) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f233,f39])).
% 1.70/0.62  fof(f233,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK4,X0),u1_struct_0(sK4),u1_struct_0(X1)) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f232,f40])).
% 1.70/0.62  fof(f232,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK4,X0),u1_struct_0(sK4),u1_struct_0(X1)) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f231,f42])).
% 1.70/0.62  fof(f231,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK4,X0),u1_struct_0(sK4),u1_struct_0(X1)) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~r4_tsep_1(sK0,sK3,sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(superposition,[],[f97,f41])).
% 1.70/0.62  fof(f97,plain,(
% 1.70/0.62    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.62    inference(duplicate_literal_removal,[],[f82])).
% 1.70/0.62  fof(f82,plain,(
% 1.70/0.62    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.62    inference(cnf_transformation,[],[f27])).
% 1.70/0.62  fof(f305,plain,(
% 1.70/0.62    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v5_pre_topc(sK2,sK0,sK1)),
% 1.70/0.62    inference(subsumption_resolution,[],[f304,f34])).
% 1.70/0.62  fof(f304,plain,(
% 1.70/0.62    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.70/0.62    inference(subsumption_resolution,[],[f303,f35])).
% 1.70/0.62  fof(f303,plain,(
% 1.70/0.62    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.62    inference(subsumption_resolution,[],[f302,f36])).
% 1.70/0.62  fof(f302,plain,(
% 1.70/0.62    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.62    inference(duplicate_literal_removal,[],[f301])).
% 1.70/0.62  fof(f301,plain,(
% 1.70/0.62    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.62    inference(resolution,[],[f300,f154])).
% 1.70/0.62  fof(f154,plain,(
% 1.70/0.62    ( ! [X0] : (v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f153,f28])).
% 1.70/0.62  fof(f153,plain,(
% 1.70/0.62    ( ! [X0] : (v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f152,f29])).
% 1.70/0.62  fof(f152,plain,(
% 1.70/0.62    ( ! [X0] : (v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f151,f30])).
% 1.70/0.62  fof(f151,plain,(
% 1.70/0.62    ( ! [X0] : (v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f150,f110])).
% 1.70/0.62  fof(f150,plain,(
% 1.70/0.62    ( ! [X0] : (v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f149,f38])).
% 1.70/0.62  fof(f149,plain,(
% 1.70/0.62    ( ! [X0] : (v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f148,f31])).
% 1.70/0.62  fof(f148,plain,(
% 1.70/0.62    ( ! [X0] : (v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f147,f32])).
% 1.70/0.62  fof(f147,plain,(
% 1.70/0.62    ( ! [X0] : (v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f146,f33])).
% 1.70/0.62  fof(f146,plain,(
% 1.70/0.62    ( ! [X0] : (v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(duplicate_literal_removal,[],[f145])).
% 1.70/0.62  fof(f145,plain,(
% 1.70/0.62    ( ! [X0] : (v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(superposition,[],[f144,f129])).
% 1.70/0.62  fof(f144,plain,(
% 1.70/0.62    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f143,f28])).
% 1.70/0.62  fof(f143,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0)) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f142,f29])).
% 1.70/0.62  fof(f142,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0)) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f141,f30])).
% 1.70/0.62  fof(f141,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0)) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f140,f37])).
% 1.70/0.62  fof(f140,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0)) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f139,f38])).
% 1.70/0.62  fof(f139,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0)) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f138,f39])).
% 1.70/0.62  fof(f138,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0)) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f137,f40])).
% 1.70/0.62  fof(f137,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0)) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f136,f42])).
% 1.70/0.62  fof(f136,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0)) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~r4_tsep_1(sK0,sK3,sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(superposition,[],[f92,f41])).
% 1.70/0.62  fof(f92,plain,(
% 1.70/0.62    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.62    inference(duplicate_literal_removal,[],[f77])).
% 1.70/0.62  % (19973)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.62  fof(f77,plain,(
% 1.70/0.62    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.62    inference(cnf_transformation,[],[f27])).
% 1.70/0.62  
% 1.70/0.62  % (19973)Memory used [KB]: 2430
% 1.70/0.62  % (19973)Time elapsed: 0.204 s
% 1.70/0.62  % (19973)------------------------------
% 1.70/0.62  % (19973)------------------------------
% 1.70/0.62  fof(f300,plain,(
% 1.70/0.62    ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v5_pre_topc(sK2,sK0,sK1)),
% 1.70/0.62    inference(subsumption_resolution,[],[f299,f34])).
% 1.70/0.62  fof(f299,plain,(
% 1.70/0.62    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.70/0.62    inference(subsumption_resolution,[],[f298,f35])).
% 1.70/0.62  fof(f298,plain,(
% 1.70/0.62    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.62    inference(subsumption_resolution,[],[f297,f36])).
% 1.70/0.62  fof(f297,plain,(
% 1.70/0.62    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.62    inference(duplicate_literal_removal,[],[f296])).
% 1.70/0.62  fof(f296,plain,(
% 1.70/0.62    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.62    inference(resolution,[],[f102,f173])).
% 1.70/0.62  fof(f173,plain,(
% 1.70/0.62    ( ! [X0] : (v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f172,f28])).
% 1.70/0.62  fof(f172,plain,(
% 1.70/0.62    ( ! [X0] : (v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f171,f29])).
% 1.70/0.62  fof(f171,plain,(
% 1.70/0.62    ( ! [X0] : (v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f170,f30])).
% 1.70/0.62  fof(f170,plain,(
% 1.70/0.62    ( ! [X0] : (v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f169,f110])).
% 1.70/0.62  fof(f169,plain,(
% 1.70/0.62    ( ! [X0] : (v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f168,f40])).
% 1.70/0.62  fof(f168,plain,(
% 1.70/0.62    ( ! [X0] : (v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f167,f31])).
% 1.70/0.62  fof(f167,plain,(
% 1.70/0.62    ( ! [X0] : (v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | v2_struct_0(sK1) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f166,f32])).
% 1.70/0.62  fof(f166,plain,(
% 1.70/0.62    ( ! [X0] : (v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f165,f33])).
% 1.70/0.62  fof(f165,plain,(
% 1.70/0.62    ( ! [X0] : (v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(duplicate_literal_removal,[],[f164])).
% 1.70/0.62  fof(f164,plain,(
% 1.70/0.62    ( ! [X0] : (v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(sK4,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(superposition,[],[f163,f129])).
% 1.70/0.62  fof(f163,plain,(
% 1.70/0.62    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f162,f28])).
% 1.70/0.62  fof(f162,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0)) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f161,f29])).
% 1.70/0.62  fof(f161,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0)) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f160,f30])).
% 1.70/0.62  fof(f160,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0)) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f159,f37])).
% 1.70/0.62  fof(f159,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0)) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f158,f38])).
% 1.70/0.62  fof(f158,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0)) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f157,f39])).
% 1.70/0.62  fof(f157,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0)) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f156,f40])).
% 1.70/0.62  fof(f156,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0)) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f155,f42])).
% 1.70/0.62  fof(f155,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0)) | ~v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~r4_tsep_1(sK0,sK3,sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(superposition,[],[f96,f41])).
% 1.70/0.62  fof(f96,plain,(
% 1.70/0.62    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.62    inference(duplicate_literal_removal,[],[f81])).
% 1.70/0.62  fof(f81,plain,(
% 1.70/0.62    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.62    inference(cnf_transformation,[],[f27])).
% 1.70/0.62  fof(f102,plain,(
% 1.70/0.62    ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v5_pre_topc(sK2,sK0,sK1)),
% 1.70/0.62    inference(subsumption_resolution,[],[f101,f34])).
% 1.70/0.62  fof(f101,plain,(
% 1.70/0.62    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.70/0.62    inference(subsumption_resolution,[],[f100,f35])).
% 1.70/0.62  fof(f100,plain,(
% 1.70/0.62    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.62    inference(subsumption_resolution,[],[f75,f36])).
% 1.70/0.62  fof(f75,plain,(
% 1.70/0.62    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.62    inference(cnf_transformation,[],[f25])).
% 1.70/0.62  fof(f45,plain,(
% 1.70/0.62    v5_pre_topc(sK2,sK0,sK1) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))),
% 1.70/0.62    inference(cnf_transformation,[],[f25])).
% 1.70/0.62  fof(f398,plain,(
% 1.70/0.62    ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.70/0.62    inference(subsumption_resolution,[],[f397,f349])).
% 1.70/0.62  fof(f349,plain,(
% 1.70/0.62    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.70/0.62    inference(subsumption_resolution,[],[f49,f347])).
% 1.70/0.62  fof(f49,plain,(
% 1.70/0.62    v5_pre_topc(sK2,sK0,sK1) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.70/0.62    inference(cnf_transformation,[],[f25])).
% 1.70/0.62  fof(f397,plain,(
% 1.70/0.62    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.70/0.62    inference(subsumption_resolution,[],[f396,f351])).
% 1.70/0.62  fof(f351,plain,(
% 1.70/0.62    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.70/0.62    inference(subsumption_resolution,[],[f57,f347])).
% 1.70/0.62  fof(f57,plain,(
% 1.70/0.62    v5_pre_topc(sK2,sK0,sK1) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.70/0.62    inference(cnf_transformation,[],[f25])).
% 1.70/0.62  fof(f396,plain,(
% 1.70/0.62    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.70/0.62    inference(subsumption_resolution,[],[f395,f350])).
% 1.70/0.62  fof(f350,plain,(
% 1.70/0.62    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)),
% 1.70/0.62    inference(subsumption_resolution,[],[f53,f347])).
% 1.70/0.62  fof(f53,plain,(
% 1.70/0.62    v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)),
% 1.70/0.62    inference(cnf_transformation,[],[f25])).
% 1.70/0.62  fof(f395,plain,(
% 1.70/0.62    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.70/0.62    inference(duplicate_literal_removal,[],[f394])).
% 1.70/0.62  fof(f394,plain,(
% 1.70/0.62    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.70/0.62    inference(superposition,[],[f392,f129])).
% 1.70/0.62  fof(f392,plain,(
% 1.70/0.62    ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2))),
% 1.70/0.62    inference(subsumption_resolution,[],[f391,f34])).
% 1.70/0.62  fof(f391,plain,(
% 1.70/0.62    ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~v1_funct_1(sK2)),
% 1.70/0.62    inference(subsumption_resolution,[],[f390,f35])).
% 1.70/0.62  fof(f390,plain,(
% 1.70/0.62    ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.62    inference(subsumption_resolution,[],[f389,f355])).
% 1.70/0.62  fof(f355,plain,(
% 1.70/0.62    m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))),
% 1.70/0.62    inference(subsumption_resolution,[],[f73,f347])).
% 1.70/0.62  fof(f73,plain,(
% 1.70/0.62    v5_pre_topc(sK2,sK0,sK1) | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))),
% 1.70/0.62    inference(cnf_transformation,[],[f25])).
% 1.70/0.62  fof(f389,plain,(
% 1.70/0.62    ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.62    inference(subsumption_resolution,[],[f388,f352])).
% 1.70/0.62  fof(f352,plain,(
% 1.70/0.62    v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))),
% 1.70/0.62    inference(subsumption_resolution,[],[f61,f347])).
% 1.70/0.62  fof(f61,plain,(
% 1.70/0.62    v5_pre_topc(sK2,sK0,sK1) | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))),
% 1.70/0.62    inference(cnf_transformation,[],[f25])).
% 1.70/0.62  fof(f388,plain,(
% 1.70/0.62    ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.62    inference(subsumption_resolution,[],[f387,f353])).
% 1.70/0.62  fof(f353,plain,(
% 1.70/0.62    v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))),
% 1.70/0.62    inference(subsumption_resolution,[],[f65,f347])).
% 1.70/0.62  fof(f65,plain,(
% 1.70/0.62    v5_pre_topc(sK2,sK0,sK1) | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))),
% 1.70/0.62    inference(cnf_transformation,[],[f25])).
% 1.70/0.62  fof(f387,plain,(
% 1.70/0.62    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.62    inference(subsumption_resolution,[],[f386,f354])).
% 1.70/0.62  fof(f354,plain,(
% 1.70/0.62    v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)),
% 1.70/0.62    inference(subsumption_resolution,[],[f69,f347])).
% 1.70/0.62  fof(f69,plain,(
% 1.70/0.62    v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)),
% 1.70/0.62    inference(cnf_transformation,[],[f25])).
% 1.70/0.62  fof(f386,plain,(
% 1.70/0.62    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.62    inference(subsumption_resolution,[],[f385,f36])).
% 1.70/0.62  fof(f385,plain,(
% 1.70/0.62    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),sK3,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK2),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK2)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.70/0.62    inference(resolution,[],[f384,f347])).
% 1.70/0.62  fof(f384,plain,(
% 1.70/0.62    ( ! [X0] : (v5_pre_topc(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,X0),sK3,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f383,f28])).
% 1.70/0.62  fof(f383,plain,(
% 1.70/0.62    ( ! [X0] : (~m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,X0),sK3,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0)) | v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f382,f29])).
% 1.70/0.62  fof(f382,plain,(
% 1.70/0.62    ( ! [X0] : (~m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,X0),sK3,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0)) | v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f381,f30])).
% 1.70/0.62  fof(f381,plain,(
% 1.70/0.62    ( ! [X0] : (~m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,X0),sK3,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0)) | v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f380,f110])).
% 1.70/0.62  fof(f380,plain,(
% 1.70/0.62    ( ! [X0] : (~m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,X0),sK3,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0)) | v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f379,f40])).
% 1.70/0.62  fof(f379,plain,(
% 1.70/0.62    ( ! [X0] : (~m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,X0),sK3,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0)) | v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f378,f31])).
% 1.70/0.62  fof(f378,plain,(
% 1.70/0.62    ( ! [X0] : (~m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,X0),sK3,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0)) | v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | v2_struct_0(sK1) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f377,f32])).
% 1.70/0.62  fof(f377,plain,(
% 1.70/0.62    ( ! [X0] : (~m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,X0),sK3,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0)) | v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f375,f33])).
% 1.70/0.62  fof(f375,plain,(
% 1.70/0.62    ( ! [X0] : (~m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,X0),sK3,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0)) | v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(duplicate_literal_removal,[],[f374])).
% 1.70/0.62  fof(f374,plain,(
% 1.70/0.62    ( ! [X0] : (~m1_subset_1(k2_tmap_1(sK0,sK1,X0,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,X0,sK4),sK4,sK1) | ~v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK4)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k3_tmap_1(sK0,sK1,sK0,sK3,X0),sK3,sK1) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,X0)) | v5_pre_topc(X0,sK0,sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(sK4,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(superposition,[],[f372,f129])).
% 1.70/0.62  fof(f372,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK4,X0),sK4,X1) | ~v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK4,X0),u1_struct_0(sK4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0)) | ~m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK3,X0),sK3,X1) | ~v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0)) | v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f371,f28])).
% 1.70/0.62  fof(f371,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK4,X0),sK4,X1) | ~v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK4,X0),u1_struct_0(sK4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0)) | ~m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK3,X0),sK3,X1) | ~v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0)) | v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f370,f29])).
% 1.70/0.62  fof(f370,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK4,X0),sK4,X1) | ~v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK4,X0),u1_struct_0(sK4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0)) | ~m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK3,X0),sK3,X1) | ~v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0)) | v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f369,f30])).
% 1.70/0.62  fof(f369,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK4,X0),sK4,X1) | ~v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK4,X0),u1_struct_0(sK4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0)) | ~m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK3,X0),sK3,X1) | ~v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0)) | v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f368,f37])).
% 1.70/0.62  fof(f368,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK4,X0),sK4,X1) | ~v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK4,X0),u1_struct_0(sK4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0)) | ~m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK3,X0),sK3,X1) | ~v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0)) | v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f367,f38])).
% 1.70/0.62  fof(f367,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK4,X0),sK4,X1) | ~v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK4,X0),u1_struct_0(sK4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0)) | ~m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK3,X0),sK3,X1) | ~v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0)) | v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f366,f39])).
% 1.70/0.62  fof(f366,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK4,X0),sK4,X1) | ~v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK4,X0),u1_struct_0(sK4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0)) | ~m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK3,X0),sK3,X1) | ~v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0)) | v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f365,f40])).
% 1.70/0.62  fof(f365,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK4,X0),sK4,X1) | ~v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK4,X0),u1_struct_0(sK4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0)) | ~m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK3,X0),sK3,X1) | ~v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0)) | v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(subsumption_resolution,[],[f364,f42])).
% 1.70/0.62  fof(f364,plain,(
% 1.70/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK4,X0),sK4,X1) | ~v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK4,X0),u1_struct_0(sK4),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK4,X0)) | ~m1_subset_1(k3_tmap_1(sK0,X1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(sK0,X1,sK0,sK3,X0),sK3,X1) | ~v1_funct_2(k3_tmap_1(sK0,X1,sK0,sK3,X0),u1_struct_0(sK3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK0,X1,sK0,sK3,X0)) | v5_pre_topc(X0,sK0,X1) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X0) | ~r4_tsep_1(sK0,sK3,sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.70/0.62    inference(superposition,[],[f87,f41])).
% 1.70/0.62  fof(f87,plain,(
% 1.70/0.62    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) | v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.62    inference(cnf_transformation,[],[f27])).
% 1.70/0.62  % SZS output end Proof for theBenchmark
% 1.70/0.62  % (19976)------------------------------
% 1.70/0.62  % (19976)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.62  % (19976)Termination reason: Refutation
% 1.70/0.62  
% 1.70/0.62  % (19976)Memory used [KB]: 6780
% 1.70/0.62  % (19976)Time elapsed: 0.186 s
% 1.70/0.62  % (19976)------------------------------
% 1.70/0.62  % (19976)------------------------------
% 1.70/0.62  % (19954)Success in time 0.258 s
%------------------------------------------------------------------------------
