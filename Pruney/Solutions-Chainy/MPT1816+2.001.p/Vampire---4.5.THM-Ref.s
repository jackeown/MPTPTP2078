%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:44 EST 2020

% Result     : Theorem 1.72s
% Output     : Refutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :  286 (5510 expanded)
%              Number of leaves         :   34 (2298 expanded)
%              Depth                    :   34
%              Number of atoms          : 1890 (205512 expanded)
%              Number of equality atoms :   49 (6621 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3697,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f209,f211,f215,f219,f223,f227,f231,f235,f239,f1341,f1353,f1365,f1377,f1395,f1429,f1436,f1440,f3110,f3118,f3121,f3124,f3173,f3175,f3177,f3596,f3681])).

fof(f3681,plain,
    ( spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(avatar_contradiction_clause,[],[f3680])).

fof(f3680,plain,
    ( $false
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f3679,f172])).

fof(f172,plain,
    ( ~ v5_pre_topc(sK4,sK2,sK3)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl7_3
  <=> v5_pre_topc(sK4,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f3679,plain,
    ( v5_pre_topc(sK4,sK2,sK3)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f3678,f520])).

fof(f520,plain,(
    sK4 = k2_tmap_1(sK2,sK3,sK4,sK2) ),
    inference(forward_demodulation,[],[f519,f300])).

fof(f300,plain,(
    sK4 = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f299,f298])).

fof(f298,plain,(
    v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f280,f145])).

fof(f145,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f280,plain,
    ( v1_relat_1(sK4)
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) ),
    inference(resolution,[],[f80,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f80,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,
    ( ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK4) )
    & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
        & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
        & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
        & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
        & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
        & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
        & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) )
      | ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        & v5_pre_topc(sK4,sK2,sK3)
        & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
        & v1_funct_1(sK4) ) )
    & r4_tsep_1(sK2,sK5,sK6)
    & sK2 = k1_tsep_1(sK2,sK5,sK6)
    & m1_pre_topc(sK6,sK2)
    & ~ v2_struct_0(sK6)
    & m1_pre_topc(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f56,f61,f60,f59,f58,f57])).

fof(f57,plain,
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
                      ( ( ~ m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1)
                        | ~ v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(sK2,X1,X2,X4))
                        | ~ m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1)
                        | ~ v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(sK2,X1,X2,X3))
                        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                        | ~ v5_pre_topc(X2,sK2,X1)
                        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
                        | ~ v1_funct_1(X2) )
                      & ( ( m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(sK2,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(sK2,X1,X2,X3)) )
                        | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                          & v5_pre_topc(X2,sK2,X1)
                          & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
                          & v1_funct_1(X2) ) )
                      & r4_tsep_1(sK2,X3,X4)
                      & sK2 = k1_tsep_1(sK2,X3,X4)
                      & m1_pre_topc(X4,sK2)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,sK2)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ( ~ m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                      | ~ v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1)
                      | ~ v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                      | ~ v1_funct_1(k2_tmap_1(sK2,X1,X2,X4))
                      | ~ m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1)
                      | ~ v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(k2_tmap_1(sK2,X1,X2,X3))
                      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X2,sK2,X1)
                      | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
                      | ~ v1_funct_1(X2) )
                    & ( ( m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                        & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1)
                        & v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                        & v1_funct_1(k2_tmap_1(sK2,X1,X2,X4))
                        & m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1)
                        & v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(k2_tmap_1(sK2,X1,X2,X3)) )
                      | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                        & v5_pre_topc(X2,sK2,X1)
                        & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
                        & v1_funct_1(X2) ) )
                    & r4_tsep_1(sK2,X3,X4)
                    & sK2 = k1_tsep_1(sK2,X3,X4)
                    & m1_pre_topc(X4,sK2)
                    & ~ v2_struct_0(X4) )
                & m1_pre_topc(X3,sK2)
                & ~ v2_struct_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
                    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X4),X4,sK3)
                    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3))
                    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,X2,X4))
                    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X3),X3,sK3)
                    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3))
                    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,X2,X3))
                    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                    | ~ v5_pre_topc(X2,sK2,sK3)
                    | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
                    | ~ v1_funct_1(X2) )
                  & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
                      & v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X4),X4,sK3)
                      & v1_funct_2(k2_tmap_1(sK2,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3))
                      & v1_funct_1(k2_tmap_1(sK2,sK3,X2,X4))
                      & m1_subset_1(k2_tmap_1(sK2,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                      & v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X3),X3,sK3)
                      & v1_funct_2(k2_tmap_1(sK2,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3))
                      & v1_funct_1(k2_tmap_1(sK2,sK3,X2,X3)) )
                    | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                      & v5_pre_topc(X2,sK2,sK3)
                      & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
                      & v1_funct_1(X2) ) )
                  & r4_tsep_1(sK2,X3,X4)
                  & sK2 = k1_tsep_1(sK2,X3,X4)
                  & m1_pre_topc(X4,sK2)
                  & ~ v2_struct_0(X4) )
              & m1_pre_topc(X3,sK2)
              & ~ v2_struct_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
          & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
                  | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X4),X4,sK3)
                  | ~ v1_funct_2(k2_tmap_1(sK2,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3))
                  | ~ v1_funct_1(k2_tmap_1(sK2,sK3,X2,X4))
                  | ~ m1_subset_1(k2_tmap_1(sK2,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                  | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X3),X3,sK3)
                  | ~ v1_funct_2(k2_tmap_1(sK2,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3))
                  | ~ v1_funct_1(k2_tmap_1(sK2,sK3,X2,X3))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                  | ~ v5_pre_topc(X2,sK2,sK3)
                  | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
                  | ~ v1_funct_1(X2) )
                & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
                    & v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X4),X4,sK3)
                    & v1_funct_2(k2_tmap_1(sK2,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3))
                    & v1_funct_1(k2_tmap_1(sK2,sK3,X2,X4))
                    & m1_subset_1(k2_tmap_1(sK2,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                    & v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X3),X3,sK3)
                    & v1_funct_2(k2_tmap_1(sK2,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3))
                    & v1_funct_1(k2_tmap_1(sK2,sK3,X2,X3)) )
                  | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                    & v5_pre_topc(X2,sK2,sK3)
                    & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
                    & v1_funct_1(X2) ) )
                & r4_tsep_1(sK2,X3,X4)
                & sK2 = k1_tsep_1(sK2,X3,X4)
                & m1_pre_topc(X4,sK2)
                & ~ v2_struct_0(X4) )
            & m1_pre_topc(X3,sK2)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
                | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3)
                | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3))
                | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4))
                | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X3),X3,sK3)
                | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X3),u1_struct_0(X3),u1_struct_0(sK3))
                | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X3))
                | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                | ~ v5_pre_topc(sK4,sK2,sK3)
                | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
                | ~ v1_funct_1(sK4) )
              & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
                  & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3)
                  & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3))
                  & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4))
                  & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                  & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X3),X3,sK3)
                  & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X3),u1_struct_0(X3),u1_struct_0(sK3))
                  & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X3)) )
                | ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                  & v5_pre_topc(sK4,sK2,sK3)
                  & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
                  & v1_funct_1(sK4) ) )
              & r4_tsep_1(sK2,X3,X4)
              & sK2 = k1_tsep_1(sK2,X3,X4)
              & m1_pre_topc(X4,sK2)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,sK2)
          & ~ v2_struct_0(X3) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
              | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3)
              | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3))
              | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4))
              | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
              | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X3),X3,sK3)
              | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X3),u1_struct_0(X3),u1_struct_0(sK3))
              | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X3))
              | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
              | ~ v5_pre_topc(sK4,sK2,sK3)
              | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
              | ~ v1_funct_1(sK4) )
            & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
                & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3)
                & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3))
                & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4))
                & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X3),X3,sK3)
                & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X3),u1_struct_0(X3),u1_struct_0(sK3))
                & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X3)) )
              | ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                & v5_pre_topc(sK4,sK2,sK3)
                & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
                & v1_funct_1(sK4) ) )
            & r4_tsep_1(sK2,X3,X4)
            & sK2 = k1_tsep_1(sK2,X3,X4)
            & m1_pre_topc(X4,sK2)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(X3,sK2)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
            | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3)
            | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3))
            | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4))
            | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
            | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
            | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
            | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
            | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
            | ~ v5_pre_topc(sK4,sK2,sK3)
            | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
            | ~ v1_funct_1(sK4) )
          & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
              & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3)
              & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3))
              & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4))
              & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
              & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
              & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
              & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) )
            | ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
              & v5_pre_topc(sK4,sK2,sK3)
              & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
              & v1_funct_1(sK4) ) )
          & r4_tsep_1(sK2,sK5,X4)
          & sK2 = k1_tsep_1(sK2,sK5,X4)
          & m1_pre_topc(X4,sK2)
          & ~ v2_struct_0(X4) )
      & m1_pre_topc(sK5,sK2)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ? [X4] :
        ( ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
          | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3)
          | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3))
          | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4))
          | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
          | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
          | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
          | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
          | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
          | ~ v5_pre_topc(sK4,sK2,sK3)
          | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
          | ~ v1_funct_1(sK4) )
        & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
            & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3)
            & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3))
            & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4))
            & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
            & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
            & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
            & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) )
          | ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
            & v5_pre_topc(sK4,sK2,sK3)
            & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
            & v1_funct_1(sK4) ) )
        & r4_tsep_1(sK2,sK5,X4)
        & sK2 = k1_tsep_1(sK2,sK5,X4)
        & m1_pre_topc(X4,sK2)
        & ~ v2_struct_0(X4) )
   => ( ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
        | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        | ~ v5_pre_topc(sK4,sK2,sK3)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
        | ~ v1_funct_1(sK4) )
      & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
          & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
          & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
          & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
          & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
          & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
          & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
          & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) )
        | ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
          & v5_pre_topc(sK4,sK2,sK3)
          & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
          & v1_funct_1(sK4) ) )
      & r4_tsep_1(sK2,sK5,sK6)
      & sK2 = k1_tsep_1(sK2,sK5,sK6)
      & m1_pre_topc(sK6,sK2)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
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
    inference(flattening,[],[f55])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_tmap_1)).

fof(f299,plain,
    ( sK4 = k7_relat_1(sK4,u1_struct_0(sK2))
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f278,f146])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f278,plain,(
    v4_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f80,f152])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f519,plain,(
    k7_relat_1(sK4,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK3,sK4,sK2) ),
    inference(subsumption_resolution,[],[f515,f74])).

fof(f74,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f515,plain,
    ( k7_relat_1(sK4,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK3,sK4,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f514,f121])).

fof(f121,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f514,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,sK2)
      | k2_tmap_1(sK2,sK3,sK4,X3) = k7_relat_1(sK4,u1_struct_0(X3)) ) ),
    inference(forward_demodulation,[],[f288,f297])).

fof(f297,plain,(
    ! [X6] : k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X6) = k7_relat_1(sK4,X6) ),
    inference(subsumption_resolution,[],[f277,f78])).

fof(f78,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f277,plain,(
    ! [X6] :
      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X6) = k7_relat_1(sK4,X6)
      | ~ v1_funct_1(sK4) ) ),
    inference(resolution,[],[f80,f158])).

fof(f158,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f288,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,sK2)
      | k2_tmap_1(sK2,sK3,sK4,X3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f287,f72])).

fof(f72,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f287,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,sK2)
      | k2_tmap_1(sK2,sK3,sK4,X3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X3))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f286,f73])).

fof(f73,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f286,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,sK2)
      | k2_tmap_1(sK2,sK3,sK4,X3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X3))
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f285,f74])).

fof(f285,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,sK2)
      | k2_tmap_1(sK2,sK3,sK4,X3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X3))
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f284,f75])).

fof(f75,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f284,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,sK2)
      | k2_tmap_1(sK2,sK3,sK4,X3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X3))
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f283,f76])).

fof(f76,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f283,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,sK2)
      | k2_tmap_1(sK2,sK3,sK4,X3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X3))
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f282,f77])).

fof(f77,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f282,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,sK2)
      | k2_tmap_1(sK2,sK3,sK4,X3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X3))
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f281,f78])).

fof(f281,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,sK2)
      | k2_tmap_1(sK2,sK3,sK4,X3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X3))
      | ~ v1_funct_1(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f275,f79])).

fof(f79,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f62])).

fof(f275,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,sK2)
      | k2_tmap_1(sK2,sK3,sK4,X3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X3))
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f80,f140])).

fof(f140,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f3678,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f3677,f85])).

fof(f85,plain,(
    sK2 = k1_tsep_1(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f62])).

fof(f3677,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f3676,f86])).

fof(f86,plain,(
    r4_tsep_1(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f62])).

fof(f3676,plain,
    ( ~ r4_tsep_1(sK2,sK5,sK6)
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f3675,f81])).

fof(f81,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f62])).

fof(f3675,plain,
    ( v2_struct_0(sK5)
    | ~ r4_tsep_1(sK2,sK5,sK6)
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f3674,f82])).

fof(f82,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f3674,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ r4_tsep_1(sK2,sK5,sK6)
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f3673,f83])).

fof(f83,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f62])).

fof(f3673,plain,
    ( v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ r4_tsep_1(sK2,sK5,sK6)
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f3649,f84])).

fof(f84,plain,(
    m1_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f3649,plain,
    ( ~ m1_pre_topc(sK6,sK2)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ r4_tsep_1(sK2,sK5,sK6)
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(resolution,[],[f827,f750])).

fof(f750,plain,(
    ! [X4,X5] :
      ( ~ sP0(sK3,X5,sK4,sK2,X4)
      | ~ m1_pre_topc(X5,sK2)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,sK2)
      | v2_struct_0(X4)
      | ~ r4_tsep_1(sK2,X4,X5)
      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,X4,X5)),k1_tsep_1(sK2,X4,X5),sK3) ) ),
    inference(resolution,[],[f296,f128])).

fof(f128,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4)
      | ~ sP0(X4,X3,X2,X1,X0)
      | v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( ( ( m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
            & v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
            & v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
            & v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) )
          | ~ sP0(X4,X3,X2,X1,X0) )
        & ( sP0(X4,X3,X2,X1,X0)
          | ~ m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
          | ~ v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
          | ~ v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
          | ~ v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) ) )
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X4,X3,X1] :
      ( ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
            & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
          | ~ sP0(X1,X3,X4,X0,X2) )
        & ( sP0(X1,X3,X4,X0,X2)
          | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
          | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) ) )
      | ~ sP1(X2,X0,X4,X3,X1) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X4,X3,X1] :
      ( ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
            & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
          | ~ sP0(X1,X3,X4,X0,X2) )
        & ( sP0(X1,X3,X4,X0,X2)
          | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
          | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) ) )
      | ~ sP1(X2,X0,X4,X3,X1) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X4,X3,X1] :
      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
      <=> sP0(X1,X3,X4,X0,X2) )
      | ~ sP1(X2,X0,X4,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f296,plain,(
    ! [X4,X5] :
      ( sP1(X4,sK2,sK4,X5,sK3)
      | ~ r4_tsep_1(sK2,X4,X5)
      | ~ m1_pre_topc(X5,sK2)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,sK2)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f295,f72])).

fof(f295,plain,(
    ! [X4,X5] :
      ( sP1(X4,sK2,sK4,X5,sK3)
      | ~ r4_tsep_1(sK2,X4,X5)
      | ~ m1_pre_topc(X5,sK2)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,sK2)
      | v2_struct_0(X4)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f294,f73])).

fof(f294,plain,(
    ! [X4,X5] :
      ( sP1(X4,sK2,sK4,X5,sK3)
      | ~ r4_tsep_1(sK2,X4,X5)
      | ~ m1_pre_topc(X5,sK2)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,sK2)
      | v2_struct_0(X4)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f293,f74])).

fof(f293,plain,(
    ! [X4,X5] :
      ( sP1(X4,sK2,sK4,X5,sK3)
      | ~ r4_tsep_1(sK2,X4,X5)
      | ~ m1_pre_topc(X5,sK2)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,sK2)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f292,f75])).

fof(f292,plain,(
    ! [X4,X5] :
      ( sP1(X4,sK2,sK4,X5,sK3)
      | ~ r4_tsep_1(sK2,X4,X5)
      | ~ m1_pre_topc(X5,sK2)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,sK2)
      | v2_struct_0(X4)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f291,f76])).

fof(f291,plain,(
    ! [X4,X5] :
      ( sP1(X4,sK2,sK4,X5,sK3)
      | ~ r4_tsep_1(sK2,X4,X5)
      | ~ m1_pre_topc(X5,sK2)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,sK2)
      | v2_struct_0(X4)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f290,f77])).

fof(f290,plain,(
    ! [X4,X5] :
      ( sP1(X4,sK2,sK4,X5,sK3)
      | ~ r4_tsep_1(sK2,X4,X5)
      | ~ m1_pre_topc(X5,sK2)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,sK2)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f289,f78])).

fof(f289,plain,(
    ! [X4,X5] :
      ( sP1(X4,sK2,sK4,X5,sK3)
      | ~ v1_funct_1(sK4)
      | ~ r4_tsep_1(sK2,X4,X5)
      | ~ m1_pre_topc(X5,sK2)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,sK2)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f276,f79])).

fof(f276,plain,(
    ! [X4,X5] :
      ( sP1(X4,sK2,sK4,X5,sK3)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK4)
      | ~ r4_tsep_1(sK2,X4,X5)
      | ~ m1_pre_topc(X5,sK2)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,sK2)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f80,f139])).

fof(f139,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | sP1(X2,X0,X4,X3,X1)
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( sP1(X2,X0,X4,X3,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(definition_folding,[],[f32,f53,f52])).

fof(f52,plain,(
    ! [X1,X3,X4,X0,X2] :
      ( sP0(X1,X3,X4,X0,X2)
    <=> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
        & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                          & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                          & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                        <=> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                            & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_tmap_1)).

fof(f827,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f826,f627])).

fof(f627,plain,
    ( v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6)))
    | ~ spl7_9 ),
    inference(backward_demodulation,[],[f195,f518])).

fof(f518,plain,(
    k2_tmap_1(sK2,sK3,sK4,sK6) = k7_relat_1(sK4,u1_struct_0(sK6)) ),
    inference(resolution,[],[f514,f84])).

fof(f195,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl7_9
  <=> v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f826,plain,
    ( ~ v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6)))
    | sP0(sK3,sK6,sK4,sK2,sK5)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f825,f628])).

fof(f628,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ spl7_10 ),
    inference(backward_demodulation,[],[f199,f518])).

fof(f199,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl7_10
  <=> v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f825,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6)))
    | sP0(sK3,sK6,sK4,sK2,sK5)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f824,f629])).

fof(f629,plain,
    ( v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3)
    | ~ spl7_11 ),
    inference(backward_demodulation,[],[f203,f518])).

fof(f203,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl7_11
  <=> v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f824,plain,
    ( ~ v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3)
    | ~ v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6)))
    | sP0(sK3,sK6,sK4,sK2,sK5)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f819,f630])).

fof(f630,plain,
    ( m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ spl7_12 ),
    inference(backward_demodulation,[],[f207,f518])).

fof(f207,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl7_12
  <=> m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f819,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3)
    | ~ v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6)))
    | sP0(sK3,sK6,sK4,sK2,sK5)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(superposition,[],[f366,f518])).

fof(f366,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
        | sP0(sK3,X0,sK4,sK2,sK5) )
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f365,f179])).

fof(f179,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl7_5
  <=> v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f365,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
        | sP0(sK3,X0,sK4,sK2,sK5)
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) )
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f364,f183])).

fof(f183,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl7_6
  <=> v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f364,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
        | sP0(sK3,X0,sK4,sK2,sK5)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) )
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f354,f187])).

fof(f187,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl7_7
  <=> v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f354,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
        | sP0(sK3,X0,sK4,sK2,sK5)
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) )
    | ~ spl7_8 ),
    inference(resolution,[],[f191,f138])).

fof(f138,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
      | sP0(X0,X1,X2,X3,X4)
      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
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
    inference(rectify,[],[f67])).

fof(f67,plain,(
    ! [X1,X3,X4,X0,X2] :
      ( ( sP0(X1,X3,X4,X0,X2)
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) )
      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
          & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) )
        | ~ sP0(X1,X3,X4,X0,X2) ) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X1,X3,X4,X0,X2] :
      ( ( sP0(X1,X3,X4,X0,X2)
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) )
      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
          & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) )
        | ~ sP0(X1,X3,X4,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f191,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl7_8
  <=> m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f3596,plain,
    ( spl7_6
    | ~ spl7_110 ),
    inference(avatar_contradiction_clause,[],[f3595])).

fof(f3595,plain,
    ( $false
    | spl7_6
    | ~ spl7_110 ),
    inference(subsumption_resolution,[],[f3189,f3245])).

fof(f3245,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3))
    | spl7_6 ),
    inference(forward_demodulation,[],[f184,f517])).

fof(f517,plain,(
    k2_tmap_1(sK2,sK3,sK4,sK5) = k7_relat_1(sK4,u1_struct_0(sK5)) ),
    inference(resolution,[],[f514,f82])).

fof(f184,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | spl7_6 ),
    inference(avatar_component_clause,[],[f182])).

fof(f3189,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ spl7_110 ),
    inference(subsumption_resolution,[],[f3188,f81])).

fof(f3188,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3))
    | v2_struct_0(sK5)
    | ~ spl7_110 ),
    inference(subsumption_resolution,[],[f1615,f82])).

fof(f1615,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ spl7_110 ),
    inference(superposition,[],[f1352,f517])).

fof(f1352,plain,
    ( ! [X1] :
        ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X1),u1_struct_0(X1),u1_struct_0(sK3))
        | ~ m1_pre_topc(X1,sK2)
        | v2_struct_0(X1) )
    | ~ spl7_110 ),
    inference(avatar_component_clause,[],[f1351])).

fof(f1351,plain,
    ( spl7_110
  <=> ! [X1] :
        ( ~ m1_pre_topc(X1,sK2)
        | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X1),u1_struct_0(X1),u1_struct_0(sK3))
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_110])])).

fof(f3177,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f3176])).

fof(f3176,plain,
    ( $false
    | spl7_1 ),
    inference(subsumption_resolution,[],[f164,f78])).

fof(f164,plain,
    ( ~ v1_funct_1(sK4)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl7_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f3175,plain,(
    spl7_2 ),
    inference(avatar_contradiction_clause,[],[f3174])).

fof(f3174,plain,
    ( $false
    | spl7_2 ),
    inference(subsumption_resolution,[],[f168,f79])).

fof(f168,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | spl7_2 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl7_2
  <=> v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f3173,plain,(
    spl7_4 ),
    inference(avatar_contradiction_clause,[],[f3172])).

fof(f3172,plain,
    ( $false
    | spl7_4 ),
    inference(subsumption_resolution,[],[f176,f80])).

fof(f176,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | spl7_4 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl7_4
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f3124,plain,
    ( spl7_11
    | ~ spl7_109 ),
    inference(avatar_contradiction_clause,[],[f3123])).

fof(f3123,plain,
    ( $false
    | spl7_11
    | ~ spl7_109 ),
    inference(subsumption_resolution,[],[f3112,f3122])).

fof(f3122,plain,
    ( ~ v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3)
    | spl7_11 ),
    inference(forward_demodulation,[],[f204,f518])).

fof(f204,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | spl7_11 ),
    inference(avatar_component_clause,[],[f202])).

fof(f3112,plain,
    ( v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3)
    | ~ spl7_109 ),
    inference(subsumption_resolution,[],[f3111,f83])).

fof(f3111,plain,
    ( v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3)
    | v2_struct_0(sK6)
    | ~ spl7_109 ),
    inference(subsumption_resolution,[],[f1526,f84])).

fof(f1526,plain,
    ( v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3)
    | ~ m1_pre_topc(sK6,sK2)
    | v2_struct_0(sK6)
    | ~ spl7_109 ),
    inference(superposition,[],[f1340,f518])).

fof(f1340,plain,
    ( ! [X2] :
        ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X2),X2,sK3)
        | ~ m1_pre_topc(X2,sK2)
        | v2_struct_0(X2) )
    | ~ spl7_109 ),
    inference(avatar_component_clause,[],[f1339])).

fof(f1339,plain,
    ( spl7_109
  <=> ! [X2] :
        ( ~ m1_pre_topc(X2,sK2)
        | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X2),X2,sK3)
        | v2_struct_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_109])])).

fof(f3121,plain,
    ( spl7_10
    | ~ spl7_110 ),
    inference(avatar_contradiction_clause,[],[f3120])).

fof(f3120,plain,
    ( $false
    | spl7_10
    | ~ spl7_110 ),
    inference(subsumption_resolution,[],[f3119,f2820])).

fof(f2820,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ spl7_110 ),
    inference(subsumption_resolution,[],[f2819,f83])).

fof(f2819,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3))
    | v2_struct_0(sK6)
    | ~ spl7_110 ),
    inference(subsumption_resolution,[],[f1616,f84])).

fof(f1616,plain,
    ( v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK6,sK2)
    | v2_struct_0(sK6)
    | ~ spl7_110 ),
    inference(superposition,[],[f1352,f518])).

fof(f3119,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3))
    | spl7_10 ),
    inference(forward_demodulation,[],[f200,f518])).

fof(f200,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | spl7_10 ),
    inference(avatar_component_clause,[],[f198])).

fof(f3118,plain,
    ( spl7_9
    | ~ spl7_111 ),
    inference(avatar_contradiction_clause,[],[f3117])).

fof(f3117,plain,
    ( $false
    | spl7_9
    | ~ spl7_111 ),
    inference(subsumption_resolution,[],[f3116,f1461])).

fof(f1461,plain,
    ( v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6)))
    | ~ spl7_111 ),
    inference(forward_demodulation,[],[f1460,f518])).

fof(f1460,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ spl7_111 ),
    inference(subsumption_resolution,[],[f1452,f83])).

fof(f1452,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | v2_struct_0(sK6)
    | ~ spl7_111 ),
    inference(resolution,[],[f1364,f84])).

fof(f1364,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
        | v2_struct_0(X0) )
    | ~ spl7_111 ),
    inference(avatar_component_clause,[],[f1363])).

fof(f1363,plain,
    ( spl7_111
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_111])])).

fof(f3116,plain,
    ( ~ v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6)))
    | spl7_9 ),
    inference(forward_demodulation,[],[f196,f518])).

fof(f196,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | spl7_9 ),
    inference(avatar_component_clause,[],[f194])).

fof(f3110,plain,
    ( spl7_12
    | ~ spl7_113 ),
    inference(avatar_contradiction_clause,[],[f3109])).

fof(f3109,plain,
    ( $false
    | spl7_12
    | ~ spl7_113 ),
    inference(subsumption_resolution,[],[f1433,f1387])).

fof(f1387,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | spl7_12 ),
    inference(forward_demodulation,[],[f208,f518])).

fof(f208,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | spl7_12 ),
    inference(avatar_component_clause,[],[f206])).

fof(f1433,plain,
    ( m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f1416,f518])).

fof(f1416,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ spl7_113 ),
    inference(resolution,[],[f1376,f137])).

fof(f137,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4)
      | m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f1376,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5)
    | ~ spl7_113 ),
    inference(avatar_component_clause,[],[f1374])).

fof(f1374,plain,
    ( spl7_113
  <=> sP0(sK3,sK6,sK4,sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_113])])).

fof(f1440,plain,
    ( spl7_7
    | ~ spl7_113 ),
    inference(avatar_contradiction_clause,[],[f1439])).

fof(f1439,plain,
    ( $false
    | spl7_7
    | ~ spl7_113 ),
    inference(subsumption_resolution,[],[f1426,f1437])).

fof(f1437,plain,
    ( ~ v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK5)),sK5,sK3)
    | spl7_7 ),
    inference(forward_demodulation,[],[f188,f517])).

fof(f188,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f186])).

fof(f1426,plain,
    ( v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK5)),sK5,sK3)
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f1411,f517])).

fof(f1411,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ spl7_113 ),
    inference(resolution,[],[f1376,f132])).

fof(f132,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4)
      | v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f1436,plain,
    ( spl7_5
    | ~ spl7_113 ),
    inference(avatar_contradiction_clause,[],[f1435])).

fof(f1435,plain,
    ( $false
    | spl7_5
    | ~ spl7_113 ),
    inference(subsumption_resolution,[],[f1424,f1434])).

fof(f1434,plain,
    ( ~ v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK5)))
    | spl7_5 ),
    inference(forward_demodulation,[],[f180,f517])).

fof(f180,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | spl7_5 ),
    inference(avatar_component_clause,[],[f178])).

fof(f1424,plain,
    ( v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK5)))
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f1409,f517])).

fof(f1409,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ spl7_113 ),
    inference(resolution,[],[f1376,f130])).

fof(f130,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4)
      | v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f1429,plain,
    ( spl7_8
    | ~ spl7_113 ),
    inference(avatar_contradiction_clause,[],[f1428])).

fof(f1428,plain,
    ( $false
    | spl7_8
    | ~ spl7_113 ),
    inference(subsumption_resolution,[],[f1427,f1386])).

fof(f1386,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | spl7_8 ),
    inference(forward_demodulation,[],[f192,f517])).

fof(f192,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | spl7_8 ),
    inference(avatar_component_clause,[],[f190])).

fof(f1427,plain,
    ( m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f1412,f517])).

fof(f1412,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ spl7_113 ),
    inference(resolution,[],[f1376,f133])).

fof(f133,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4)
      | m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f1395,plain,(
    spl7_112 ),
    inference(avatar_contradiction_clause,[],[f1394])).

fof(f1394,plain,
    ( $false
    | spl7_112 ),
    inference(subsumption_resolution,[],[f1393,f81])).

fof(f1393,plain,
    ( v2_struct_0(sK5)
    | spl7_112 ),
    inference(subsumption_resolution,[],[f1392,f82])).

fof(f1392,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | spl7_112 ),
    inference(subsumption_resolution,[],[f1391,f83])).

fof(f1391,plain,
    ( v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | spl7_112 ),
    inference(subsumption_resolution,[],[f1390,f84])).

fof(f1390,plain,
    ( ~ m1_pre_topc(sK6,sK2)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | spl7_112 ),
    inference(subsumption_resolution,[],[f1389,f86])).

fof(f1389,plain,
    ( ~ r4_tsep_1(sK2,sK5,sK6)
    | ~ m1_pre_topc(sK6,sK2)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | spl7_112 ),
    inference(resolution,[],[f1372,f296])).

fof(f1372,plain,
    ( ~ sP1(sK5,sK2,sK4,sK6,sK3)
    | spl7_112 ),
    inference(avatar_component_clause,[],[f1370])).

fof(f1370,plain,
    ( spl7_112
  <=> sP1(sK5,sK2,sK4,sK6,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_112])])).

fof(f1377,plain,
    ( ~ spl7_112
    | ~ spl7_3
    | spl7_113 ),
    inference(avatar_split_clause,[],[f1368,f1374,f170,f1370])).

fof(f1368,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ sP1(sK5,sK2,sK4,sK6,sK3) ),
    inference(subsumption_resolution,[],[f1367,f78])).

fof(f1367,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ sP1(sK5,sK2,sK4,sK6,sK3) ),
    inference(subsumption_resolution,[],[f1366,f79])).

fof(f1366,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ sP1(sK5,sK2,sK4,sK6,sK3) ),
    inference(subsumption_resolution,[],[f948,f80])).

fof(f948,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | sP0(sK3,sK6,sK4,sK2,sK5)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ sP1(sK5,sK2,sK4,sK6,sK3) ),
    inference(superposition,[],[f271,f520])).

fof(f271,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_tmap_1(sK2,X0,X1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | sP0(X0,sK6,X1,sK2,sK5)
      | ~ v5_pre_topc(k2_tmap_1(sK2,X0,X1,sK2),sK2,X0)
      | ~ v1_funct_2(k2_tmap_1(sK2,X0,X1,sK2),u1_struct_0(sK2),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tmap_1(sK2,X0,X1,sK2))
      | ~ sP1(sK5,sK2,X1,sK6,X0) ) ),
    inference(superposition,[],[f125,f85])).

fof(f125,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
      | sP0(X4,X3,X2,X1,X0)
      | ~ v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
      | ~ v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
      | ~ v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)))
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f1365,plain,
    ( ~ spl7_3
    | spl7_111 ),
    inference(avatar_split_clause,[],[f1361,f1363,f170])).

fof(f1361,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
      | ~ v5_pre_topc(sK4,sK2,sK3) ) ),
    inference(subsumption_resolution,[],[f1360,f72])).

fof(f1360,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f1359,f73])).

fof(f1359,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f1358,f74])).

fof(f1358,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f1357,f75])).

fof(f1357,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f1356,f76])).

fof(f1356,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f1355,f77])).

fof(f1355,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f1354,f78])).

fof(f1354,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | ~ v1_funct_1(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f272,f79])).

fof(f272,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f80,f155])).

fof(f155,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_pre_topc(X3,X0)
        & ~ v2_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v5_pre_topc(X2,X0,X1)
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tmap_1)).

fof(f1353,plain,
    ( ~ spl7_3
    | spl7_110 ),
    inference(avatar_split_clause,[],[f1349,f1351,f170])).

fof(f1349,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X1),u1_struct_0(X1),u1_struct_0(sK3))
      | ~ v5_pre_topc(sK4,sK2,sK3) ) ),
    inference(subsumption_resolution,[],[f1348,f72])).

fof(f1348,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X1),u1_struct_0(X1),u1_struct_0(sK3))
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f1347,f73])).

fof(f1347,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X1),u1_struct_0(X1),u1_struct_0(sK3))
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f1346,f74])).

fof(f1346,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X1),u1_struct_0(X1),u1_struct_0(sK3))
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f1345,f75])).

fof(f1345,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X1),u1_struct_0(X1),u1_struct_0(sK3))
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f1344,f76])).

fof(f1344,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X1),u1_struct_0(X1),u1_struct_0(sK3))
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f1343,f77])).

fof(f1343,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X1),u1_struct_0(X1),u1_struct_0(sK3))
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f1342,f78])).

fof(f1342,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X1),u1_struct_0(X1),u1_struct_0(sK3))
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | ~ v1_funct_1(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f273,f79])).

fof(f273,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(X1)
      | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X1),u1_struct_0(X1),u1_struct_0(sK3))
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f80,f156])).

fof(f156,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f1341,plain,
    ( ~ spl7_3
    | spl7_109 ),
    inference(avatar_split_clause,[],[f1337,f1339,f170])).

fof(f1337,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X2),X2,sK3)
      | ~ v5_pre_topc(sK4,sK2,sK3) ) ),
    inference(subsumption_resolution,[],[f1336,f72])).

fof(f1336,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X2),X2,sK3)
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f1335,f73])).

fof(f1335,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X2),X2,sK3)
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f1334,f74])).

fof(f1334,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X2),X2,sK3)
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f1333,f75])).

fof(f1333,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X2),X2,sK3)
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f1332,f76])).

fof(f1332,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X2),X2,sK3)
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f1331,f77])).

fof(f1331,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X2),X2,sK3)
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f1330,f78])).

fof(f1330,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X2),X2,sK3)
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | ~ v1_funct_1(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f274,f79])).

fof(f274,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X2),X2,sK3)
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f80,f157])).

fof(f157,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f239,plain,
    ( spl7_3
    | spl7_5 ),
    inference(avatar_split_clause,[],[f89,f178,f170])).

fof(f89,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f235,plain,
    ( spl7_3
    | spl7_6 ),
    inference(avatar_split_clause,[],[f93,f182,f170])).

fof(f93,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f231,plain,
    ( spl7_3
    | spl7_7 ),
    inference(avatar_split_clause,[],[f97,f186,f170])).

fof(f97,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f227,plain,
    ( spl7_3
    | spl7_8 ),
    inference(avatar_split_clause,[],[f101,f190,f170])).

fof(f101,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f223,plain,
    ( spl7_3
    | spl7_9 ),
    inference(avatar_split_clause,[],[f105,f194,f170])).

fof(f105,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f219,plain,
    ( spl7_3
    | spl7_10 ),
    inference(avatar_split_clause,[],[f109,f198,f170])).

fof(f109,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f215,plain,
    ( spl7_3
    | spl7_11 ),
    inference(avatar_split_clause,[],[f113,f202,f170])).

fof(f113,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f211,plain,
    ( spl7_3
    | spl7_12 ),
    inference(avatar_split_clause,[],[f117,f206,f170])).

fof(f117,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f209,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f119,f206,f202,f198,f194,f190,f186,f182,f178,f174,f170,f166,f162])).

fof(f119,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f62])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:29:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (25610)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.49  % (25602)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.50  % (25599)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  % (25596)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (25597)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (25611)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.51  % (25600)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (25595)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (25598)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (25614)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.51  % (25608)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (25609)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (25607)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (25603)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.52  % (25613)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.52  % (25612)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.52  % (25616)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % (25606)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (25601)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (25604)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.52  % (25618)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.52  % (25619)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.53  % (25605)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.53  % (25615)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.53  % (25595)Refutation not found, incomplete strategy% (25595)------------------------------
% 0.22/0.53  % (25595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (25595)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (25595)Memory used [KB]: 11001
% 0.22/0.53  % (25595)Time elapsed: 0.086 s
% 0.22/0.53  % (25595)------------------------------
% 0.22/0.53  % (25595)------------------------------
% 0.22/0.53  % (25617)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.54  % (25620)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.72/0.61  % (25596)Refutation found. Thanks to Tanya!
% 1.72/0.61  % SZS status Theorem for theBenchmark
% 1.72/0.61  % SZS output start Proof for theBenchmark
% 1.72/0.61  fof(f3697,plain,(
% 1.72/0.61    $false),
% 1.72/0.61    inference(avatar_sat_refutation,[],[f209,f211,f215,f219,f223,f227,f231,f235,f239,f1341,f1353,f1365,f1377,f1395,f1429,f1436,f1440,f3110,f3118,f3121,f3124,f3173,f3175,f3177,f3596,f3681])).
% 1.72/0.61  fof(f3681,plain,(
% 1.72/0.61    spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12),
% 1.72/0.61    inference(avatar_contradiction_clause,[],[f3680])).
% 1.72/0.61  fof(f3680,plain,(
% 1.72/0.61    $false | (spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12)),
% 1.72/0.61    inference(subsumption_resolution,[],[f3679,f172])).
% 1.72/0.61  fof(f172,plain,(
% 1.72/0.61    ~v5_pre_topc(sK4,sK2,sK3) | spl7_3),
% 1.72/0.61    inference(avatar_component_clause,[],[f170])).
% 1.72/0.61  fof(f170,plain,(
% 1.72/0.61    spl7_3 <=> v5_pre_topc(sK4,sK2,sK3)),
% 1.72/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.72/0.61  fof(f3679,plain,(
% 1.72/0.61    v5_pre_topc(sK4,sK2,sK3) | (~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12)),
% 1.72/0.61    inference(forward_demodulation,[],[f3678,f520])).
% 1.72/0.61  fof(f520,plain,(
% 1.72/0.61    sK4 = k2_tmap_1(sK2,sK3,sK4,sK2)),
% 1.72/0.61    inference(forward_demodulation,[],[f519,f300])).
% 1.72/0.61  fof(f300,plain,(
% 1.72/0.61    sK4 = k7_relat_1(sK4,u1_struct_0(sK2))),
% 1.72/0.61    inference(subsumption_resolution,[],[f299,f298])).
% 1.72/0.61  fof(f298,plain,(
% 1.72/0.61    v1_relat_1(sK4)),
% 1.72/0.61    inference(subsumption_resolution,[],[f280,f145])).
% 1.72/0.61  fof(f145,plain,(
% 1.72/0.61    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.72/0.61    inference(cnf_transformation,[],[f4])).
% 1.72/0.61  fof(f4,axiom,(
% 1.72/0.61    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.72/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.72/0.61  fof(f280,plain,(
% 1.72/0.61    v1_relat_1(sK4) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))),
% 1.72/0.61    inference(resolution,[],[f80,f120])).
% 1.72/0.61  fof(f120,plain,(
% 1.72/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.72/0.61    inference(cnf_transformation,[],[f26])).
% 1.72/0.61  fof(f26,plain,(
% 1.72/0.61    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.72/0.61    inference(ennf_transformation,[],[f3])).
% 1.72/0.61  fof(f3,axiom,(
% 1.72/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.72/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.72/0.61  fof(f80,plain,(
% 1.72/0.61    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 1.72/0.61    inference(cnf_transformation,[],[f62])).
% 1.72/0.61  fof(f62,plain,(
% 1.72/0.61    (((((~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))) & r4_tsep_1(sK2,sK5,sK6) & sK2 = k1_tsep_1(sK2,sK5,sK6) & m1_pre_topc(sK6,sK2) & ~v2_struct_0(sK6)) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 1.72/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f56,f61,f60,f59,f58,f57])).
% 1.72/0.61  fof(f57,plain,(
% 1.72/0.61    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v5_pre_topc(X2,sK2,X1) | ~v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) & m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v5_pre_topc(X2,sK2,X1) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(sK2,X3,X4) & sK2 = k1_tsep_1(sK2,X3,X4) & m1_pre_topc(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 1.72/0.61    introduced(choice_axiom,[])).
% 1.72/0.61  fof(f58,plain,(
% 1.72/0.61    ? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v5_pre_topc(X2,sK2,X1) | ~v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) & m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v5_pre_topc(X2,sK2,X1) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(sK2,X3,X4) & sK2 = k1_tsep_1(sK2,X3,X4) & m1_pre_topc(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X4),X4,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,X2,X4)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X3),X3,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(X2,sK2,sK3) | ~v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X4),X4,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,X2,X4)) & m1_subset_1(k2_tmap_1(sK2,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X3),X3,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(X2,sK2,sK3) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X2))) & r4_tsep_1(sK2,X3,X4) & sK2 = k1_tsep_1(sK2,X3,X4) & m1_pre_topc(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 1.72/0.61    introduced(choice_axiom,[])).
% 1.72/0.61  fof(f59,plain,(
% 1.72/0.61    ? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X4),X4,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,X2,X4)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X3),X3,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(X2,sK2,sK3) | ~v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X4),X4,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,X2,X4)) & m1_subset_1(k2_tmap_1(sK2,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X3),X3,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(X2,sK2,sK3) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X2))) & r4_tsep_1(sK2,X3,X4) & sK2 = k1_tsep_1(sK2,X3,X4) & m1_pre_topc(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X3),X3,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X3),u1_struct_0(X3),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4)) & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X3),X3,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X3),u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X3))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))) & r4_tsep_1(sK2,X3,X4) & sK2 = k1_tsep_1(sK2,X3,X4) & m1_pre_topc(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))),
% 1.72/0.61    introduced(choice_axiom,[])).
% 1.72/0.61  fof(f60,plain,(
% 1.72/0.61    ? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X3),X3,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X3),u1_struct_0(X3),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4)) & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X3),X3,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X3),u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X3))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))) & r4_tsep_1(sK2,X3,X4) & sK2 = k1_tsep_1(sK2,X3,X4) & m1_pre_topc(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) => (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4)) & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))) & r4_tsep_1(sK2,sK5,X4) & sK2 = k1_tsep_1(sK2,sK5,X4) & m1_pre_topc(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5))),
% 1.72/0.61    introduced(choice_axiom,[])).
% 1.72/0.61  fof(f61,plain,(
% 1.72/0.61    ? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4)) & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))) & r4_tsep_1(sK2,sK5,X4) & sK2 = k1_tsep_1(sK2,sK5,X4) & m1_pre_topc(X4,sK2) & ~v2_struct_0(X4)) => ((~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))) & r4_tsep_1(sK2,sK5,sK6) & sK2 = k1_tsep_1(sK2,sK5,sK6) & m1_pre_topc(sK6,sK2) & ~v2_struct_0(sK6))),
% 1.72/0.61    introduced(choice_axiom,[])).
% 1.72/0.61  fof(f56,plain,(
% 1.72/0.61    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.72/0.61    inference(flattening,[],[f55])).
% 1.72/0.61  fof(f55,plain,(
% 1.72/0.61    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.72/0.61    inference(nnf_transformation,[],[f25])).
% 1.72/0.61  fof(f25,plain,(
% 1.72/0.61    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.72/0.61    inference(flattening,[],[f24])).
% 1.72/0.61  fof(f24,plain,(
% 1.72/0.61    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & (r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0)) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.72/0.61    inference(ennf_transformation,[],[f21])).
% 1.72/0.61  fof(f21,negated_conjecture,(
% 1.72/0.61    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 1.72/0.61    inference(negated_conjecture,[],[f20])).
% 1.72/0.61  fof(f20,conjecture,(
% 1.72/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 1.72/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_tmap_1)).
% 1.72/0.61  fof(f299,plain,(
% 1.72/0.61    sK4 = k7_relat_1(sK4,u1_struct_0(sK2)) | ~v1_relat_1(sK4)),
% 1.72/0.61    inference(resolution,[],[f278,f146])).
% 1.72/0.61  fof(f146,plain,(
% 1.72/0.61    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 1.72/0.61    inference(cnf_transformation,[],[f44])).
% 1.72/0.61  fof(f44,plain,(
% 1.72/0.61    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.72/0.61    inference(flattening,[],[f43])).
% 1.72/0.61  fof(f43,plain,(
% 1.72/0.61    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.72/0.61    inference(ennf_transformation,[],[f5])).
% 1.72/0.61  fof(f5,axiom,(
% 1.72/0.61    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.72/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 1.72/0.61  fof(f278,plain,(
% 1.72/0.61    v4_relat_1(sK4,u1_struct_0(sK2))),
% 1.72/0.61    inference(resolution,[],[f80,f152])).
% 1.72/0.61  fof(f152,plain,(
% 1.72/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.72/0.61    inference(cnf_transformation,[],[f45])).
% 1.72/0.61  fof(f45,plain,(
% 1.72/0.61    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.72/0.61    inference(ennf_transformation,[],[f23])).
% 1.72/0.61  fof(f23,plain,(
% 1.72/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.72/0.61    inference(pure_predicate_removal,[],[f6])).
% 1.72/0.61  fof(f6,axiom,(
% 1.72/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.72/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.72/0.61  fof(f519,plain,(
% 1.72/0.61    k7_relat_1(sK4,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK3,sK4,sK2)),
% 1.72/0.61    inference(subsumption_resolution,[],[f515,f74])).
% 1.72/0.61  fof(f74,plain,(
% 1.72/0.61    l1_pre_topc(sK2)),
% 1.72/0.61    inference(cnf_transformation,[],[f62])).
% 1.72/0.61  fof(f515,plain,(
% 1.72/0.61    k7_relat_1(sK4,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK3,sK4,sK2) | ~l1_pre_topc(sK2)),
% 1.72/0.61    inference(resolution,[],[f514,f121])).
% 1.72/0.61  fof(f121,plain,(
% 1.72/0.61    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 1.72/0.61    inference(cnf_transformation,[],[f27])).
% 1.72/0.61  fof(f27,plain,(
% 1.72/0.61    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 1.72/0.61    inference(ennf_transformation,[],[f18])).
% 1.72/0.61  fof(f18,axiom,(
% 1.72/0.61    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 1.72/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 1.72/0.61  fof(f514,plain,(
% 1.72/0.61    ( ! [X3] : (~m1_pre_topc(X3,sK2) | k2_tmap_1(sK2,sK3,sK4,X3) = k7_relat_1(sK4,u1_struct_0(X3))) )),
% 1.72/0.61    inference(forward_demodulation,[],[f288,f297])).
% 1.72/0.61  fof(f297,plain,(
% 1.72/0.61    ( ! [X6] : (k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X6) = k7_relat_1(sK4,X6)) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f277,f78])).
% 1.72/0.61  fof(f78,plain,(
% 1.72/0.61    v1_funct_1(sK4)),
% 1.72/0.61    inference(cnf_transformation,[],[f62])).
% 1.72/0.61  fof(f277,plain,(
% 1.72/0.61    ( ! [X6] : (k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X6) = k7_relat_1(sK4,X6) | ~v1_funct_1(sK4)) )),
% 1.72/0.61    inference(resolution,[],[f80,f158])).
% 1.72/0.61  fof(f158,plain,(
% 1.72/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~v1_funct_1(X2)) )),
% 1.72/0.61    inference(cnf_transformation,[],[f51])).
% 1.72/0.61  fof(f51,plain,(
% 1.72/0.61    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.72/0.61    inference(flattening,[],[f50])).
% 1.72/0.61  fof(f50,plain,(
% 1.72/0.61    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.72/0.61    inference(ennf_transformation,[],[f7])).
% 1.72/0.61  fof(f7,axiom,(
% 1.72/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.72/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.72/0.61  fof(f288,plain,(
% 1.72/0.61    ( ! [X3] : (~m1_pre_topc(X3,sK2) | k2_tmap_1(sK2,sK3,sK4,X3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X3))) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f287,f72])).
% 1.72/0.61  fof(f72,plain,(
% 1.72/0.61    ~v2_struct_0(sK2)),
% 1.72/0.61    inference(cnf_transformation,[],[f62])).
% 1.72/0.61  fof(f287,plain,(
% 1.72/0.61    ( ! [X3] : (~m1_pre_topc(X3,sK2) | k2_tmap_1(sK2,sK3,sK4,X3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X3)) | v2_struct_0(sK2)) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f286,f73])).
% 1.72/0.61  fof(f73,plain,(
% 1.72/0.61    v2_pre_topc(sK2)),
% 1.72/0.61    inference(cnf_transformation,[],[f62])).
% 1.72/0.61  fof(f286,plain,(
% 1.72/0.61    ( ! [X3] : (~m1_pre_topc(X3,sK2) | k2_tmap_1(sK2,sK3,sK4,X3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X3)) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f285,f74])).
% 1.72/0.61  fof(f285,plain,(
% 1.72/0.61    ( ! [X3] : (~m1_pre_topc(X3,sK2) | k2_tmap_1(sK2,sK3,sK4,X3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X3)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f284,f75])).
% 1.72/0.61  fof(f75,plain,(
% 1.72/0.61    ~v2_struct_0(sK3)),
% 1.72/0.61    inference(cnf_transformation,[],[f62])).
% 1.72/0.61  fof(f284,plain,(
% 1.72/0.61    ( ! [X3] : (~m1_pre_topc(X3,sK2) | k2_tmap_1(sK2,sK3,sK4,X3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X3)) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f283,f76])).
% 1.72/0.61  fof(f76,plain,(
% 1.72/0.61    v2_pre_topc(sK3)),
% 1.72/0.61    inference(cnf_transformation,[],[f62])).
% 1.72/0.61  fof(f283,plain,(
% 1.72/0.61    ( ! [X3] : (~m1_pre_topc(X3,sK2) | k2_tmap_1(sK2,sK3,sK4,X3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X3)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f282,f77])).
% 1.72/0.61  fof(f77,plain,(
% 1.72/0.61    l1_pre_topc(sK3)),
% 1.72/0.61    inference(cnf_transformation,[],[f62])).
% 1.72/0.61  fof(f282,plain,(
% 1.72/0.61    ( ! [X3] : (~m1_pre_topc(X3,sK2) | k2_tmap_1(sK2,sK3,sK4,X3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X3)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f281,f78])).
% 1.72/0.61  fof(f281,plain,(
% 1.72/0.61    ( ! [X3] : (~m1_pre_topc(X3,sK2) | k2_tmap_1(sK2,sK3,sK4,X3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X3)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f275,f79])).
% 1.72/0.61  fof(f79,plain,(
% 1.72/0.61    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 1.72/0.61    inference(cnf_transformation,[],[f62])).
% 1.72/0.61  fof(f275,plain,(
% 1.72/0.61    ( ! [X3] : (~m1_pre_topc(X3,sK2) | k2_tmap_1(sK2,sK3,sK4,X3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X3)) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.72/0.61    inference(resolution,[],[f80,f140])).
% 1.72/0.61  fof(f140,plain,(
% 1.72/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.72/0.61    inference(cnf_transformation,[],[f34])).
% 1.72/0.61  fof(f34,plain,(
% 1.72/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.72/0.61    inference(flattening,[],[f33])).
% 1.72/0.61  fof(f33,plain,(
% 1.72/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.72/0.61    inference(ennf_transformation,[],[f11])).
% 1.72/0.61  fof(f11,axiom,(
% 1.72/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 1.72/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 1.72/0.61  fof(f3678,plain,(
% 1.72/0.61    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) | (~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12)),
% 1.72/0.61    inference(forward_demodulation,[],[f3677,f85])).
% 1.72/0.61  fof(f85,plain,(
% 1.72/0.61    sK2 = k1_tsep_1(sK2,sK5,sK6)),
% 1.72/0.61    inference(cnf_transformation,[],[f62])).
% 1.72/0.61  fof(f3677,plain,(
% 1.72/0.61    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) | (~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12)),
% 1.72/0.61    inference(subsumption_resolution,[],[f3676,f86])).
% 1.72/0.61  fof(f86,plain,(
% 1.72/0.61    r4_tsep_1(sK2,sK5,sK6)),
% 1.72/0.61    inference(cnf_transformation,[],[f62])).
% 1.72/0.61  fof(f3676,plain,(
% 1.72/0.61    ~r4_tsep_1(sK2,sK5,sK6) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) | (~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12)),
% 1.72/0.61    inference(subsumption_resolution,[],[f3675,f81])).
% 1.72/0.61  fof(f81,plain,(
% 1.72/0.61    ~v2_struct_0(sK5)),
% 1.72/0.61    inference(cnf_transformation,[],[f62])).
% 1.72/0.61  fof(f3675,plain,(
% 1.72/0.61    v2_struct_0(sK5) | ~r4_tsep_1(sK2,sK5,sK6) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) | (~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12)),
% 1.72/0.61    inference(subsumption_resolution,[],[f3674,f82])).
% 1.72/0.61  fof(f82,plain,(
% 1.72/0.61    m1_pre_topc(sK5,sK2)),
% 1.72/0.61    inference(cnf_transformation,[],[f62])).
% 1.72/0.61  fof(f3674,plain,(
% 1.72/0.61    ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~r4_tsep_1(sK2,sK5,sK6) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) | (~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12)),
% 1.72/0.61    inference(subsumption_resolution,[],[f3673,f83])).
% 1.72/0.61  fof(f83,plain,(
% 1.72/0.61    ~v2_struct_0(sK6)),
% 1.72/0.61    inference(cnf_transformation,[],[f62])).
% 1.72/0.61  fof(f3673,plain,(
% 1.72/0.61    v2_struct_0(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~r4_tsep_1(sK2,sK5,sK6) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) | (~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12)),
% 1.72/0.61    inference(subsumption_resolution,[],[f3649,f84])).
% 1.72/0.61  fof(f84,plain,(
% 1.72/0.61    m1_pre_topc(sK6,sK2)),
% 1.72/0.61    inference(cnf_transformation,[],[f62])).
% 1.72/0.61  fof(f3649,plain,(
% 1.72/0.61    ~m1_pre_topc(sK6,sK2) | v2_struct_0(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~r4_tsep_1(sK2,sK5,sK6) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) | (~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12)),
% 1.72/0.61    inference(resolution,[],[f827,f750])).
% 1.72/0.61  fof(f750,plain,(
% 1.72/0.61    ( ! [X4,X5] : (~sP0(sK3,X5,sK4,sK2,X4) | ~m1_pre_topc(X5,sK2) | v2_struct_0(X5) | ~m1_pre_topc(X4,sK2) | v2_struct_0(X4) | ~r4_tsep_1(sK2,X4,X5) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,X4,X5)),k1_tsep_1(sK2,X4,X5),sK3)) )),
% 1.72/0.61    inference(resolution,[],[f296,f128])).
% 1.72/0.61  fof(f128,plain,(
% 1.72/0.61    ( ! [X4,X2,X0,X3,X1] : (~sP1(X0,X1,X2,X3,X4) | ~sP0(X4,X3,X2,X1,X0) | v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)) )),
% 1.72/0.61    inference(cnf_transformation,[],[f65])).
% 1.72/0.61  fof(f65,plain,(
% 1.72/0.61    ! [X0,X1,X2,X3,X4] : ((((m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) & v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) & v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) & v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)))) | ~sP0(X4,X3,X2,X1,X0)) & (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) | ~v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) | ~v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) | ~v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))))) | ~sP1(X0,X1,X2,X3,X4))),
% 1.72/0.61    inference(rectify,[],[f64])).
% 1.72/0.61  fof(f64,plain,(
% 1.72/0.61    ! [X2,X0,X4,X3,X1] : ((((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) | ~sP0(X1,X3,X4,X0,X2)) & (sP0(X1,X3,X4,X0,X2) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))))) | ~sP1(X2,X0,X4,X3,X1))),
% 1.72/0.61    inference(flattening,[],[f63])).
% 1.72/0.61  fof(f63,plain,(
% 1.72/0.61    ! [X2,X0,X4,X3,X1] : ((((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) | ~sP0(X1,X3,X4,X0,X2)) & (sP0(X1,X3,X4,X0,X2) | (~m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))))) | ~sP1(X2,X0,X4,X3,X1))),
% 1.72/0.61    inference(nnf_transformation,[],[f53])).
% 1.72/0.61  fof(f53,plain,(
% 1.72/0.61    ! [X2,X0,X4,X3,X1] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> sP0(X1,X3,X4,X0,X2)) | ~sP1(X2,X0,X4,X3,X1))),
% 1.72/0.61    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.72/0.61  fof(f296,plain,(
% 1.72/0.61    ( ! [X4,X5] : (sP1(X4,sK2,sK4,X5,sK3) | ~r4_tsep_1(sK2,X4,X5) | ~m1_pre_topc(X5,sK2) | v2_struct_0(X5) | ~m1_pre_topc(X4,sK2) | v2_struct_0(X4)) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f295,f72])).
% 1.72/0.61  fof(f295,plain,(
% 1.72/0.61    ( ! [X4,X5] : (sP1(X4,sK2,sK4,X5,sK3) | ~r4_tsep_1(sK2,X4,X5) | ~m1_pre_topc(X5,sK2) | v2_struct_0(X5) | ~m1_pre_topc(X4,sK2) | v2_struct_0(X4) | v2_struct_0(sK2)) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f294,f73])).
% 1.72/0.61  fof(f294,plain,(
% 1.72/0.61    ( ! [X4,X5] : (sP1(X4,sK2,sK4,X5,sK3) | ~r4_tsep_1(sK2,X4,X5) | ~m1_pre_topc(X5,sK2) | v2_struct_0(X5) | ~m1_pre_topc(X4,sK2) | v2_struct_0(X4) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f293,f74])).
% 1.72/0.61  fof(f293,plain,(
% 1.72/0.61    ( ! [X4,X5] : (sP1(X4,sK2,sK4,X5,sK3) | ~r4_tsep_1(sK2,X4,X5) | ~m1_pre_topc(X5,sK2) | v2_struct_0(X5) | ~m1_pre_topc(X4,sK2) | v2_struct_0(X4) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f292,f75])).
% 1.72/0.61  fof(f292,plain,(
% 1.72/0.61    ( ! [X4,X5] : (sP1(X4,sK2,sK4,X5,sK3) | ~r4_tsep_1(sK2,X4,X5) | ~m1_pre_topc(X5,sK2) | v2_struct_0(X5) | ~m1_pre_topc(X4,sK2) | v2_struct_0(X4) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f291,f76])).
% 1.72/0.61  fof(f291,plain,(
% 1.72/0.61    ( ! [X4,X5] : (sP1(X4,sK2,sK4,X5,sK3) | ~r4_tsep_1(sK2,X4,X5) | ~m1_pre_topc(X5,sK2) | v2_struct_0(X5) | ~m1_pre_topc(X4,sK2) | v2_struct_0(X4) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f290,f77])).
% 1.72/0.61  fof(f290,plain,(
% 1.72/0.61    ( ! [X4,X5] : (sP1(X4,sK2,sK4,X5,sK3) | ~r4_tsep_1(sK2,X4,X5) | ~m1_pre_topc(X5,sK2) | v2_struct_0(X5) | ~m1_pre_topc(X4,sK2) | v2_struct_0(X4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f289,f78])).
% 1.72/0.61  fof(f289,plain,(
% 1.72/0.61    ( ! [X4,X5] : (sP1(X4,sK2,sK4,X5,sK3) | ~v1_funct_1(sK4) | ~r4_tsep_1(sK2,X4,X5) | ~m1_pre_topc(X5,sK2) | v2_struct_0(X5) | ~m1_pre_topc(X4,sK2) | v2_struct_0(X4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.72/0.61    inference(subsumption_resolution,[],[f276,f79])).
% 1.72/0.61  fof(f276,plain,(
% 1.72/0.61    ( ! [X4,X5] : (sP1(X4,sK2,sK4,X5,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~r4_tsep_1(sK2,X4,X5) | ~m1_pre_topc(X5,sK2) | v2_struct_0(X5) | ~m1_pre_topc(X4,sK2) | v2_struct_0(X4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.72/0.61    inference(resolution,[],[f80,f139])).
% 1.72/0.61  fof(f139,plain,(
% 1.72/0.61    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | sP1(X2,X0,X4,X3,X1) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.72/0.61    inference(cnf_transformation,[],[f54])).
% 1.72/0.61  fof(f54,plain,(
% 1.72/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (sP1(X2,X0,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.72/0.61    inference(definition_folding,[],[f32,f53,f52])).
% 1.72/0.61  fof(f52,plain,(
% 1.72/0.61    ! [X1,X3,X4,X0,X2] : (sP0(X1,X3,X4,X0,X2) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))))),
% 1.72/0.61    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.72/0.61  fof(f32,plain,(
% 1.72/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.72/0.61    inference(flattening,[],[f31])).
% 1.72/0.61  fof(f31,plain,(
% 1.72/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.72/0.61    inference(ennf_transformation,[],[f14])).
% 1.72/0.61  fof(f14,axiom,(
% 1.72/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r4_tsep_1(X0,X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))))))))))),
% 1.72/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_tmap_1)).
% 1.72/0.61  fof(f827,plain,(
% 1.72/0.61    sP0(sK3,sK6,sK4,sK2,sK5) | (~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12)),
% 1.72/0.61    inference(subsumption_resolution,[],[f826,f627])).
% 1.72/0.61  fof(f627,plain,(
% 1.72/0.61    v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6))) | ~spl7_9),
% 1.72/0.61    inference(backward_demodulation,[],[f195,f518])).
% 1.72/0.61  fof(f518,plain,(
% 1.72/0.61    k2_tmap_1(sK2,sK3,sK4,sK6) = k7_relat_1(sK4,u1_struct_0(sK6))),
% 1.72/0.61    inference(resolution,[],[f514,f84])).
% 1.72/0.61  fof(f195,plain,(
% 1.72/0.61    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~spl7_9),
% 1.72/0.61    inference(avatar_component_clause,[],[f194])).
% 1.72/0.61  fof(f194,plain,(
% 1.72/0.61    spl7_9 <=> v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))),
% 1.72/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.72/0.61  fof(f826,plain,(
% 1.72/0.61    ~v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6))) | sP0(sK3,sK6,sK4,sK2,sK5) | (~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_10 | ~spl7_11 | ~spl7_12)),
% 1.72/0.61    inference(subsumption_resolution,[],[f825,f628])).
% 1.72/0.61  fof(f628,plain,(
% 1.72/0.61    v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) | ~spl7_10),
% 1.72/0.61    inference(backward_demodulation,[],[f199,f518])).
% 1.72/0.61  fof(f199,plain,(
% 1.72/0.61    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~spl7_10),
% 1.72/0.61    inference(avatar_component_clause,[],[f198])).
% 1.72/0.61  fof(f198,plain,(
% 1.72/0.61    spl7_10 <=> v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))),
% 1.72/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.72/0.61  fof(f825,plain,(
% 1.72/0.61    ~v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6))) | sP0(sK3,sK6,sK4,sK2,sK5) | (~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_11 | ~spl7_12)),
% 1.72/0.61    inference(subsumption_resolution,[],[f824,f629])).
% 1.72/0.61  fof(f629,plain,(
% 1.72/0.61    v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) | ~spl7_11),
% 1.72/0.61    inference(backward_demodulation,[],[f203,f518])).
% 1.72/0.61  fof(f203,plain,(
% 1.72/0.61    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~spl7_11),
% 1.72/0.61    inference(avatar_component_clause,[],[f202])).
% 1.72/0.61  fof(f202,plain,(
% 1.72/0.61    spl7_11 <=> v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)),
% 1.72/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 1.72/0.61  fof(f824,plain,(
% 1.72/0.61    ~v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) | ~v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6))) | sP0(sK3,sK6,sK4,sK2,sK5) | (~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_12)),
% 1.72/0.61    inference(subsumption_resolution,[],[f819,f630])).
% 1.72/0.61  fof(f630,plain,(
% 1.72/0.61    m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~spl7_12),
% 1.72/0.61    inference(backward_demodulation,[],[f207,f518])).
% 1.72/0.61  fof(f207,plain,(
% 1.72/0.61    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~spl7_12),
% 1.72/0.61    inference(avatar_component_clause,[],[f206])).
% 1.72/0.61  fof(f206,plain,(
% 1.72/0.61    spl7_12 <=> m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))),
% 1.72/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 1.72/0.61  fof(f819,plain,(
% 1.72/0.61    ~m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) | ~v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6))) | sP0(sK3,sK6,sK4,sK2,sK5) | (~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8)),
% 1.72/0.61    inference(superposition,[],[f366,f518])).
% 1.72/0.61  fof(f366,plain,(
% 1.72/0.61    ( ! [X0] : (~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) | sP0(sK3,X0,sK4,sK2,sK5)) ) | (~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8)),
% 1.72/0.61    inference(subsumption_resolution,[],[f365,f179])).
% 1.72/0.61  fof(f179,plain,(
% 1.72/0.61    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~spl7_5),
% 1.72/0.61    inference(avatar_component_clause,[],[f178])).
% 1.72/0.61  fof(f178,plain,(
% 1.72/0.61    spl7_5 <=> v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))),
% 1.72/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.72/0.61  fof(f365,plain,(
% 1.72/0.61    ( ! [X0] : (~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) | sP0(sK3,X0,sK4,sK2,sK5) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))) ) | (~spl7_6 | ~spl7_7 | ~spl7_8)),
% 1.72/0.61    inference(subsumption_resolution,[],[f364,f183])).
% 1.72/0.61  fof(f183,plain,(
% 1.72/0.61    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~spl7_6),
% 1.72/0.61    inference(avatar_component_clause,[],[f182])).
% 1.72/0.61  fof(f182,plain,(
% 1.72/0.61    spl7_6 <=> v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))),
% 1.72/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.72/0.61  fof(f364,plain,(
% 1.72/0.61    ( ! [X0] : (~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) | sP0(sK3,X0,sK4,sK2,sK5) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))) ) | (~spl7_7 | ~spl7_8)),
% 1.72/0.61    inference(subsumption_resolution,[],[f354,f187])).
% 1.72/0.61  fof(f187,plain,(
% 1.72/0.61    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~spl7_7),
% 1.72/0.61    inference(avatar_component_clause,[],[f186])).
% 1.72/0.61  fof(f186,plain,(
% 1.72/0.61    spl7_7 <=> v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)),
% 1.72/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.72/0.61  fof(f354,plain,(
% 1.72/0.61    ( ! [X0] : (~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) | sP0(sK3,X0,sK4,sK2,sK5) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))) ) | ~spl7_8),
% 1.72/0.61    inference(resolution,[],[f191,f138])).
% 1.72/0.61  fof(f138,plain,(
% 1.72/0.61    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) | sP0(X0,X1,X2,X3,X4) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) )),
% 1.72/0.61    inference(cnf_transformation,[],[f68])).
% 1.72/0.61  fof(f68,plain,(
% 1.72/0.61    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) & ((m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) & v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) & m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) & v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) & v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) | ~sP0(X0,X1,X2,X3,X4)))),
% 1.72/0.61    inference(rectify,[],[f67])).
% 1.72/0.61  fof(f67,plain,(
% 1.72/0.61    ! [X1,X3,X4,X0,X2] : ((sP0(X1,X3,X4,X0,X2) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X2))) & ((m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))) | ~sP0(X1,X3,X4,X0,X2)))),
% 1.72/0.61    inference(flattening,[],[f66])).
% 1.72/0.61  fof(f66,plain,(
% 1.72/0.61    ! [X1,X3,X4,X0,X2] : ((sP0(X1,X3,X4,X0,X2) | (~m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) & ((m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))) | ~sP0(X1,X3,X4,X0,X2)))),
% 1.72/0.61    inference(nnf_transformation,[],[f52])).
% 1.72/0.61  fof(f191,plain,(
% 1.72/0.61    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~spl7_8),
% 1.72/0.61    inference(avatar_component_clause,[],[f190])).
% 1.72/0.61  fof(f190,plain,(
% 1.72/0.61    spl7_8 <=> m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))),
% 1.72/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.72/0.61  fof(f3596,plain,(
% 1.72/0.61    spl7_6 | ~spl7_110),
% 1.72/0.61    inference(avatar_contradiction_clause,[],[f3595])).
% 1.72/0.61  fof(f3595,plain,(
% 1.72/0.61    $false | (spl7_6 | ~spl7_110)),
% 1.72/0.61    inference(subsumption_resolution,[],[f3189,f3245])).
% 1.72/0.61  fof(f3245,plain,(
% 1.72/0.61    ~v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3)) | spl7_6),
% 1.72/0.61    inference(forward_demodulation,[],[f184,f517])).
% 1.72/0.61  fof(f517,plain,(
% 1.72/0.61    k2_tmap_1(sK2,sK3,sK4,sK5) = k7_relat_1(sK4,u1_struct_0(sK5))),
% 1.72/0.61    inference(resolution,[],[f514,f82])).
% 1.72/0.61  fof(f184,plain,(
% 1.72/0.61    ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | spl7_6),
% 1.72/0.61    inference(avatar_component_clause,[],[f182])).
% 1.72/0.61  fof(f3189,plain,(
% 1.72/0.61    v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~spl7_110),
% 1.72/0.61    inference(subsumption_resolution,[],[f3188,f81])).
% 1.72/0.61  fof(f3188,plain,(
% 1.72/0.61    v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3)) | v2_struct_0(sK5) | ~spl7_110),
% 1.72/0.61    inference(subsumption_resolution,[],[f1615,f82])).
% 1.72/0.61  fof(f1615,plain,(
% 1.72/0.61    v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3)) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~spl7_110),
% 1.72/0.61    inference(superposition,[],[f1352,f517])).
% 1.72/0.61  fof(f1352,plain,(
% 1.72/0.61    ( ! [X1] : (v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X1),u1_struct_0(X1),u1_struct_0(sK3)) | ~m1_pre_topc(X1,sK2) | v2_struct_0(X1)) ) | ~spl7_110),
% 1.72/0.61    inference(avatar_component_clause,[],[f1351])).
% 1.72/0.61  fof(f1351,plain,(
% 1.72/0.61    spl7_110 <=> ! [X1] : (~m1_pre_topc(X1,sK2) | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X1),u1_struct_0(X1),u1_struct_0(sK3)) | v2_struct_0(X1))),
% 1.72/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_110])])).
% 1.72/0.61  fof(f3177,plain,(
% 1.72/0.61    spl7_1),
% 1.72/0.61    inference(avatar_contradiction_clause,[],[f3176])).
% 1.72/0.61  fof(f3176,plain,(
% 1.72/0.61    $false | spl7_1),
% 1.72/0.61    inference(subsumption_resolution,[],[f164,f78])).
% 1.72/0.61  fof(f164,plain,(
% 1.72/0.61    ~v1_funct_1(sK4) | spl7_1),
% 1.72/0.61    inference(avatar_component_clause,[],[f162])).
% 1.72/0.61  fof(f162,plain,(
% 1.72/0.61    spl7_1 <=> v1_funct_1(sK4)),
% 1.72/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.72/0.61  fof(f3175,plain,(
% 1.72/0.61    spl7_2),
% 1.72/0.61    inference(avatar_contradiction_clause,[],[f3174])).
% 1.72/0.61  fof(f3174,plain,(
% 1.72/0.61    $false | spl7_2),
% 1.72/0.61    inference(subsumption_resolution,[],[f168,f79])).
% 1.72/0.61  fof(f168,plain,(
% 1.72/0.61    ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | spl7_2),
% 1.72/0.61    inference(avatar_component_clause,[],[f166])).
% 1.72/0.61  fof(f166,plain,(
% 1.72/0.61    spl7_2 <=> v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 1.72/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.72/0.61  fof(f3173,plain,(
% 1.72/0.61    spl7_4),
% 1.72/0.61    inference(avatar_contradiction_clause,[],[f3172])).
% 1.72/0.61  fof(f3172,plain,(
% 1.72/0.61    $false | spl7_4),
% 1.72/0.61    inference(subsumption_resolution,[],[f176,f80])).
% 1.72/0.61  fof(f176,plain,(
% 1.72/0.61    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | spl7_4),
% 1.72/0.61    inference(avatar_component_clause,[],[f174])).
% 1.72/0.61  fof(f174,plain,(
% 1.72/0.61    spl7_4 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 1.72/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.72/0.61  fof(f3124,plain,(
% 1.72/0.61    spl7_11 | ~spl7_109),
% 1.72/0.61    inference(avatar_contradiction_clause,[],[f3123])).
% 1.72/0.61  fof(f3123,plain,(
% 1.72/0.61    $false | (spl7_11 | ~spl7_109)),
% 1.72/0.61    inference(subsumption_resolution,[],[f3112,f3122])).
% 1.72/0.61  fof(f3122,plain,(
% 1.72/0.61    ~v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) | spl7_11),
% 1.72/0.61    inference(forward_demodulation,[],[f204,f518])).
% 1.72/0.61  fof(f204,plain,(
% 1.72/0.61    ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | spl7_11),
% 1.72/0.61    inference(avatar_component_clause,[],[f202])).
% 1.72/0.61  fof(f3112,plain,(
% 1.72/0.61    v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) | ~spl7_109),
% 1.72/0.61    inference(subsumption_resolution,[],[f3111,f83])).
% 1.72/0.61  fof(f3111,plain,(
% 1.72/0.61    v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) | v2_struct_0(sK6) | ~spl7_109),
% 1.72/0.61    inference(subsumption_resolution,[],[f1526,f84])).
% 1.72/0.61  fof(f1526,plain,(
% 1.72/0.61    v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK6)),sK6,sK3) | ~m1_pre_topc(sK6,sK2) | v2_struct_0(sK6) | ~spl7_109),
% 1.72/0.61    inference(superposition,[],[f1340,f518])).
% 1.72/0.61  fof(f1340,plain,(
% 1.72/0.61    ( ! [X2] : (v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X2),X2,sK3) | ~m1_pre_topc(X2,sK2) | v2_struct_0(X2)) ) | ~spl7_109),
% 1.72/0.61    inference(avatar_component_clause,[],[f1339])).
% 1.72/0.61  fof(f1339,plain,(
% 1.72/0.61    spl7_109 <=> ! [X2] : (~m1_pre_topc(X2,sK2) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X2),X2,sK3) | v2_struct_0(X2))),
% 1.72/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_109])])).
% 1.72/0.61  fof(f3121,plain,(
% 1.72/0.61    spl7_10 | ~spl7_110),
% 1.72/0.61    inference(avatar_contradiction_clause,[],[f3120])).
% 1.72/0.61  fof(f3120,plain,(
% 1.72/0.61    $false | (spl7_10 | ~spl7_110)),
% 1.72/0.61    inference(subsumption_resolution,[],[f3119,f2820])).
% 1.72/0.61  fof(f2820,plain,(
% 1.72/0.61    v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) | ~spl7_110),
% 1.72/0.61    inference(subsumption_resolution,[],[f2819,f83])).
% 1.72/0.61  fof(f2819,plain,(
% 1.72/0.61    v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) | v2_struct_0(sK6) | ~spl7_110),
% 1.72/0.61    inference(subsumption_resolution,[],[f1616,f84])).
% 1.72/0.61  fof(f1616,plain,(
% 1.72/0.61    v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) | ~m1_pre_topc(sK6,sK2) | v2_struct_0(sK6) | ~spl7_110),
% 1.72/0.61    inference(superposition,[],[f1352,f518])).
% 1.72/0.61  fof(f3119,plain,(
% 1.72/0.61    ~v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK6)),u1_struct_0(sK6),u1_struct_0(sK3)) | spl7_10),
% 1.72/0.61    inference(forward_demodulation,[],[f200,f518])).
% 1.72/0.61  fof(f200,plain,(
% 1.72/0.61    ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | spl7_10),
% 1.72/0.61    inference(avatar_component_clause,[],[f198])).
% 1.72/0.61  fof(f3118,plain,(
% 1.72/0.61    spl7_9 | ~spl7_111),
% 1.72/0.61    inference(avatar_contradiction_clause,[],[f3117])).
% 1.72/0.61  fof(f3117,plain,(
% 1.72/0.61    $false | (spl7_9 | ~spl7_111)),
% 1.72/0.61    inference(subsumption_resolution,[],[f3116,f1461])).
% 1.72/0.61  fof(f1461,plain,(
% 1.72/0.61    v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6))) | ~spl7_111),
% 1.72/0.61    inference(forward_demodulation,[],[f1460,f518])).
% 1.72/0.61  fof(f1460,plain,(
% 1.72/0.61    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~spl7_111),
% 1.72/0.61    inference(subsumption_resolution,[],[f1452,f83])).
% 1.72/0.61  fof(f1452,plain,(
% 1.72/0.61    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | v2_struct_0(sK6) | ~spl7_111),
% 1.72/0.61    inference(resolution,[],[f1364,f84])).
% 1.72/0.61  fof(f1364,plain,(
% 1.72/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) | v2_struct_0(X0)) ) | ~spl7_111),
% 1.72/0.61    inference(avatar_component_clause,[],[f1363])).
% 1.72/0.61  fof(f1363,plain,(
% 1.72/0.61    spl7_111 <=> ! [X0] : (~m1_pre_topc(X0,sK2) | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) | v2_struct_0(X0))),
% 1.72/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_111])])).
% 1.72/0.61  fof(f3116,plain,(
% 1.72/0.61    ~v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK6))) | spl7_9),
% 1.72/0.61    inference(forward_demodulation,[],[f196,f518])).
% 1.72/0.61  fof(f196,plain,(
% 1.72/0.61    ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | spl7_9),
% 1.72/0.61    inference(avatar_component_clause,[],[f194])).
% 1.72/0.61  fof(f3110,plain,(
% 1.72/0.61    spl7_12 | ~spl7_113),
% 1.72/0.61    inference(avatar_contradiction_clause,[],[f3109])).
% 1.72/0.61  fof(f3109,plain,(
% 1.72/0.61    $false | (spl7_12 | ~spl7_113)),
% 1.72/0.61    inference(subsumption_resolution,[],[f1433,f1387])).
% 1.72/0.62  fof(f1387,plain,(
% 1.72/0.62    ~m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | spl7_12),
% 1.72/0.62    inference(forward_demodulation,[],[f208,f518])).
% 1.72/0.62  fof(f208,plain,(
% 1.72/0.62    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | spl7_12),
% 1.72/0.62    inference(avatar_component_clause,[],[f206])).
% 1.72/0.62  fof(f1433,plain,(
% 1.72/0.62    m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~spl7_113),
% 1.72/0.62    inference(forward_demodulation,[],[f1416,f518])).
% 1.72/0.62  fof(f1416,plain,(
% 1.72/0.62    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~spl7_113),
% 1.72/0.62    inference(resolution,[],[f1376,f137])).
% 1.72/0.62  fof(f137,plain,(
% 1.72/0.62    ( ! [X4,X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3,X4) | m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))) )),
% 1.72/0.62    inference(cnf_transformation,[],[f68])).
% 1.72/0.62  fof(f1376,plain,(
% 1.72/0.62    sP0(sK3,sK6,sK4,sK2,sK5) | ~spl7_113),
% 1.72/0.62    inference(avatar_component_clause,[],[f1374])).
% 1.72/0.62  fof(f1374,plain,(
% 1.72/0.62    spl7_113 <=> sP0(sK3,sK6,sK4,sK2,sK5)),
% 1.72/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_113])])).
% 1.72/0.62  fof(f1440,plain,(
% 1.72/0.62    spl7_7 | ~spl7_113),
% 1.72/0.62    inference(avatar_contradiction_clause,[],[f1439])).
% 1.72/0.62  fof(f1439,plain,(
% 1.72/0.62    $false | (spl7_7 | ~spl7_113)),
% 1.72/0.62    inference(subsumption_resolution,[],[f1426,f1437])).
% 1.72/0.62  fof(f1437,plain,(
% 1.72/0.62    ~v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK5)),sK5,sK3) | spl7_7),
% 1.72/0.62    inference(forward_demodulation,[],[f188,f517])).
% 1.72/0.62  fof(f188,plain,(
% 1.72/0.62    ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | spl7_7),
% 1.72/0.62    inference(avatar_component_clause,[],[f186])).
% 1.72/0.62  fof(f1426,plain,(
% 1.72/0.62    v5_pre_topc(k7_relat_1(sK4,u1_struct_0(sK5)),sK5,sK3) | ~spl7_113),
% 1.72/0.62    inference(forward_demodulation,[],[f1411,f517])).
% 1.72/0.62  fof(f1411,plain,(
% 1.72/0.62    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~spl7_113),
% 1.72/0.62    inference(resolution,[],[f1376,f132])).
% 1.72/0.62  fof(f132,plain,(
% 1.72/0.62    ( ! [X4,X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3,X4) | v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)) )),
% 1.72/0.62    inference(cnf_transformation,[],[f68])).
% 1.72/0.62  fof(f1436,plain,(
% 1.72/0.62    spl7_5 | ~spl7_113),
% 1.72/0.62    inference(avatar_contradiction_clause,[],[f1435])).
% 1.72/0.62  fof(f1435,plain,(
% 1.72/0.62    $false | (spl7_5 | ~spl7_113)),
% 1.72/0.62    inference(subsumption_resolution,[],[f1424,f1434])).
% 1.72/0.62  fof(f1434,plain,(
% 1.72/0.62    ~v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK5))) | spl7_5),
% 1.72/0.62    inference(forward_demodulation,[],[f180,f517])).
% 1.72/0.62  fof(f180,plain,(
% 1.72/0.62    ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | spl7_5),
% 1.72/0.62    inference(avatar_component_clause,[],[f178])).
% 1.72/0.62  fof(f1424,plain,(
% 1.72/0.62    v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK5))) | ~spl7_113),
% 1.72/0.62    inference(forward_demodulation,[],[f1409,f517])).
% 1.72/0.62  fof(f1409,plain,(
% 1.72/0.62    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~spl7_113),
% 1.72/0.62    inference(resolution,[],[f1376,f130])).
% 1.72/0.62  fof(f130,plain,(
% 1.72/0.62    ( ! [X4,X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3,X4) | v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) )),
% 1.72/0.62    inference(cnf_transformation,[],[f68])).
% 1.72/0.62  fof(f1429,plain,(
% 1.72/0.62    spl7_8 | ~spl7_113),
% 1.72/0.62    inference(avatar_contradiction_clause,[],[f1428])).
% 1.72/0.62  fof(f1428,plain,(
% 1.72/0.62    $false | (spl7_8 | ~spl7_113)),
% 1.72/0.62    inference(subsumption_resolution,[],[f1427,f1386])).
% 1.72/0.62  fof(f1386,plain,(
% 1.72/0.62    ~m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | spl7_8),
% 1.72/0.62    inference(forward_demodulation,[],[f192,f517])).
% 1.72/0.62  fof(f192,plain,(
% 1.72/0.62    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | spl7_8),
% 1.72/0.62    inference(avatar_component_clause,[],[f190])).
% 1.72/0.62  fof(f1427,plain,(
% 1.72/0.62    m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~spl7_113),
% 1.72/0.62    inference(forward_demodulation,[],[f1412,f517])).
% 1.72/0.62  fof(f1412,plain,(
% 1.72/0.62    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~spl7_113),
% 1.72/0.62    inference(resolution,[],[f1376,f133])).
% 1.72/0.62  fof(f133,plain,(
% 1.72/0.62    ( ! [X4,X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3,X4) | m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))) )),
% 1.72/0.62    inference(cnf_transformation,[],[f68])).
% 1.72/0.62  fof(f1395,plain,(
% 1.72/0.62    spl7_112),
% 1.72/0.62    inference(avatar_contradiction_clause,[],[f1394])).
% 1.72/0.62  fof(f1394,plain,(
% 1.72/0.62    $false | spl7_112),
% 1.72/0.62    inference(subsumption_resolution,[],[f1393,f81])).
% 1.72/0.62  fof(f1393,plain,(
% 1.72/0.62    v2_struct_0(sK5) | spl7_112),
% 1.72/0.62    inference(subsumption_resolution,[],[f1392,f82])).
% 1.72/0.62  fof(f1392,plain,(
% 1.72/0.62    ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | spl7_112),
% 1.72/0.62    inference(subsumption_resolution,[],[f1391,f83])).
% 1.72/0.62  fof(f1391,plain,(
% 1.72/0.62    v2_struct_0(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | spl7_112),
% 1.72/0.62    inference(subsumption_resolution,[],[f1390,f84])).
% 1.72/0.62  fof(f1390,plain,(
% 1.72/0.62    ~m1_pre_topc(sK6,sK2) | v2_struct_0(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | spl7_112),
% 1.72/0.62    inference(subsumption_resolution,[],[f1389,f86])).
% 1.72/0.62  fof(f1389,plain,(
% 1.72/0.62    ~r4_tsep_1(sK2,sK5,sK6) | ~m1_pre_topc(sK6,sK2) | v2_struct_0(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | spl7_112),
% 1.72/0.62    inference(resolution,[],[f1372,f296])).
% 1.72/0.62  fof(f1372,plain,(
% 1.72/0.62    ~sP1(sK5,sK2,sK4,sK6,sK3) | spl7_112),
% 1.72/0.62    inference(avatar_component_clause,[],[f1370])).
% 1.72/0.62  fof(f1370,plain,(
% 1.72/0.62    spl7_112 <=> sP1(sK5,sK2,sK4,sK6,sK3)),
% 1.72/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_112])])).
% 1.72/0.62  fof(f1377,plain,(
% 1.72/0.62    ~spl7_112 | ~spl7_3 | spl7_113),
% 1.72/0.62    inference(avatar_split_clause,[],[f1368,f1374,f170,f1370])).
% 1.72/0.62  fof(f1368,plain,(
% 1.72/0.62    sP0(sK3,sK6,sK4,sK2,sK5) | ~v5_pre_topc(sK4,sK2,sK3) | ~sP1(sK5,sK2,sK4,sK6,sK3)),
% 1.72/0.62    inference(subsumption_resolution,[],[f1367,f78])).
% 1.72/0.62  fof(f1367,plain,(
% 1.72/0.62    sP0(sK3,sK6,sK4,sK2,sK5) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_1(sK4) | ~sP1(sK5,sK2,sK4,sK6,sK3)),
% 1.72/0.62    inference(subsumption_resolution,[],[f1366,f79])).
% 1.72/0.62  fof(f1366,plain,(
% 1.72/0.62    sP0(sK3,sK6,sK4,sK2,sK5) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~sP1(sK5,sK2,sK4,sK6,sK3)),
% 1.72/0.62    inference(subsumption_resolution,[],[f948,f80])).
% 1.72/0.62  fof(f948,plain,(
% 1.72/0.62    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | sP0(sK3,sK6,sK4,sK2,sK5) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~sP1(sK5,sK2,sK4,sK6,sK3)),
% 1.72/0.62    inference(superposition,[],[f271,f520])).
% 1.72/0.62  fof(f271,plain,(
% 1.72/0.62    ( ! [X0,X1] : (~m1_subset_1(k2_tmap_1(sK2,X0,X1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | sP0(X0,sK6,X1,sK2,sK5) | ~v5_pre_topc(k2_tmap_1(sK2,X0,X1,sK2),sK2,X0) | ~v1_funct_2(k2_tmap_1(sK2,X0,X1,sK2),u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(sK2,X0,X1,sK2)) | ~sP1(sK5,sK2,X1,sK6,X0)) )),
% 1.72/0.62    inference(superposition,[],[f125,f85])).
% 1.72/0.62  fof(f125,plain,(
% 1.72/0.62    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) | sP0(X4,X3,X2,X1,X0) | ~v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) | ~v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) | ~v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) | ~sP1(X0,X1,X2,X3,X4)) )),
% 1.72/0.62    inference(cnf_transformation,[],[f65])).
% 1.72/0.62  fof(f1365,plain,(
% 1.72/0.62    ~spl7_3 | spl7_111),
% 1.72/0.62    inference(avatar_split_clause,[],[f1361,f1363,f170])).
% 1.72/0.62  fof(f1361,plain,(
% 1.72/0.62    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) | ~v5_pre_topc(sK4,sK2,sK3)) )),
% 1.72/0.62    inference(subsumption_resolution,[],[f1360,f72])).
% 1.72/0.62  fof(f1360,plain,(
% 1.72/0.62    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) | ~v5_pre_topc(sK4,sK2,sK3) | v2_struct_0(sK2)) )),
% 1.72/0.62    inference(subsumption_resolution,[],[f1359,f73])).
% 1.72/0.62  fof(f1359,plain,(
% 1.72/0.62    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) | ~v5_pre_topc(sK4,sK2,sK3) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.72/0.62    inference(subsumption_resolution,[],[f1358,f74])).
% 1.72/0.62  fof(f1358,plain,(
% 1.72/0.62    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) | ~v5_pre_topc(sK4,sK2,sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.72/0.62    inference(subsumption_resolution,[],[f1357,f75])).
% 1.72/0.62  fof(f1357,plain,(
% 1.72/0.62    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) | ~v5_pre_topc(sK4,sK2,sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.72/0.62    inference(subsumption_resolution,[],[f1356,f76])).
% 1.72/0.62  fof(f1356,plain,(
% 1.72/0.62    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) | ~v5_pre_topc(sK4,sK2,sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.72/0.62    inference(subsumption_resolution,[],[f1355,f77])).
% 1.72/0.62  fof(f1355,plain,(
% 1.72/0.62    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) | ~v5_pre_topc(sK4,sK2,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.72/0.62    inference(subsumption_resolution,[],[f1354,f78])).
% 1.72/0.62  fof(f1354,plain,(
% 1.72/0.62    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.72/0.62    inference(subsumption_resolution,[],[f272,f79])).
% 1.72/0.62  fof(f272,plain,(
% 1.72/0.62    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.72/0.62    inference(resolution,[],[f80,f155])).
% 1.72/0.62  fof(f155,plain,(
% 1.72/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.72/0.62    inference(cnf_transformation,[],[f49])).
% 1.72/0.62  fof(f49,plain,(
% 1.72/0.62    ! [X0,X1,X2,X3] : ((v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.72/0.62    inference(flattening,[],[f48])).
% 1.72/0.62  fof(f48,plain,(
% 1.72/0.62    ! [X0,X1,X2,X3] : ((v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.72/0.62    inference(ennf_transformation,[],[f13])).
% 1.72/0.62  fof(f13,axiom,(
% 1.72/0.62    ! [X0,X1,X2,X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 1.72/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tmap_1)).
% 1.72/0.62  fof(f1353,plain,(
% 1.72/0.62    ~spl7_3 | spl7_110),
% 1.72/0.62    inference(avatar_split_clause,[],[f1349,f1351,f170])).
% 1.72/0.62  fof(f1349,plain,(
% 1.72/0.62    ( ! [X1] : (~m1_pre_topc(X1,sK2) | v2_struct_0(X1) | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X1),u1_struct_0(X1),u1_struct_0(sK3)) | ~v5_pre_topc(sK4,sK2,sK3)) )),
% 1.72/0.62    inference(subsumption_resolution,[],[f1348,f72])).
% 1.72/0.62  fof(f1348,plain,(
% 1.72/0.62    ( ! [X1] : (~m1_pre_topc(X1,sK2) | v2_struct_0(X1) | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X1),u1_struct_0(X1),u1_struct_0(sK3)) | ~v5_pre_topc(sK4,sK2,sK3) | v2_struct_0(sK2)) )),
% 1.72/0.62    inference(subsumption_resolution,[],[f1347,f73])).
% 1.72/0.62  fof(f1347,plain,(
% 1.72/0.62    ( ! [X1] : (~m1_pre_topc(X1,sK2) | v2_struct_0(X1) | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X1),u1_struct_0(X1),u1_struct_0(sK3)) | ~v5_pre_topc(sK4,sK2,sK3) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.72/0.62    inference(subsumption_resolution,[],[f1346,f74])).
% 1.72/0.62  fof(f1346,plain,(
% 1.72/0.62    ( ! [X1] : (~m1_pre_topc(X1,sK2) | v2_struct_0(X1) | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X1),u1_struct_0(X1),u1_struct_0(sK3)) | ~v5_pre_topc(sK4,sK2,sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.72/0.62    inference(subsumption_resolution,[],[f1345,f75])).
% 1.72/0.62  fof(f1345,plain,(
% 1.72/0.62    ( ! [X1] : (~m1_pre_topc(X1,sK2) | v2_struct_0(X1) | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X1),u1_struct_0(X1),u1_struct_0(sK3)) | ~v5_pre_topc(sK4,sK2,sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.72/0.62    inference(subsumption_resolution,[],[f1344,f76])).
% 1.72/0.62  fof(f1344,plain,(
% 1.72/0.62    ( ! [X1] : (~m1_pre_topc(X1,sK2) | v2_struct_0(X1) | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X1),u1_struct_0(X1),u1_struct_0(sK3)) | ~v5_pre_topc(sK4,sK2,sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.72/0.62    inference(subsumption_resolution,[],[f1343,f77])).
% 1.72/0.62  fof(f1343,plain,(
% 1.72/0.62    ( ! [X1] : (~m1_pre_topc(X1,sK2) | v2_struct_0(X1) | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X1),u1_struct_0(X1),u1_struct_0(sK3)) | ~v5_pre_topc(sK4,sK2,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.72/0.62    inference(subsumption_resolution,[],[f1342,f78])).
% 1.72/0.62  fof(f1342,plain,(
% 1.72/0.62    ( ! [X1] : (~m1_pre_topc(X1,sK2) | v2_struct_0(X1) | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X1),u1_struct_0(X1),u1_struct_0(sK3)) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.72/0.62    inference(subsumption_resolution,[],[f273,f79])).
% 1.72/0.62  fof(f273,plain,(
% 1.72/0.62    ( ! [X1] : (~m1_pre_topc(X1,sK2) | v2_struct_0(X1) | v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X1),u1_struct_0(X1),u1_struct_0(sK3)) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.72/0.62    inference(resolution,[],[f80,f156])).
% 1.72/0.62  fof(f156,plain,(
% 1.72/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.72/0.62    inference(cnf_transformation,[],[f49])).
% 1.72/0.62  fof(f1341,plain,(
% 1.72/0.62    ~spl7_3 | spl7_109),
% 1.72/0.62    inference(avatar_split_clause,[],[f1337,f1339,f170])).
% 1.72/0.62  fof(f1337,plain,(
% 1.72/0.62    ( ! [X2] : (~m1_pre_topc(X2,sK2) | v2_struct_0(X2) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X2),X2,sK3) | ~v5_pre_topc(sK4,sK2,sK3)) )),
% 1.72/0.62    inference(subsumption_resolution,[],[f1336,f72])).
% 1.72/0.62  fof(f1336,plain,(
% 1.72/0.62    ( ! [X2] : (~m1_pre_topc(X2,sK2) | v2_struct_0(X2) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X2),X2,sK3) | ~v5_pre_topc(sK4,sK2,sK3) | v2_struct_0(sK2)) )),
% 1.72/0.62    inference(subsumption_resolution,[],[f1335,f73])).
% 1.72/0.62  fof(f1335,plain,(
% 1.72/0.62    ( ! [X2] : (~m1_pre_topc(X2,sK2) | v2_struct_0(X2) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X2),X2,sK3) | ~v5_pre_topc(sK4,sK2,sK3) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.72/0.62    inference(subsumption_resolution,[],[f1334,f74])).
% 1.72/0.62  fof(f1334,plain,(
% 1.72/0.62    ( ! [X2] : (~m1_pre_topc(X2,sK2) | v2_struct_0(X2) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X2),X2,sK3) | ~v5_pre_topc(sK4,sK2,sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.72/0.62    inference(subsumption_resolution,[],[f1333,f75])).
% 1.72/0.62  fof(f1333,plain,(
% 1.72/0.62    ( ! [X2] : (~m1_pre_topc(X2,sK2) | v2_struct_0(X2) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X2),X2,sK3) | ~v5_pre_topc(sK4,sK2,sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.72/0.62    inference(subsumption_resolution,[],[f1332,f76])).
% 1.72/0.62  fof(f1332,plain,(
% 1.72/0.62    ( ! [X2] : (~m1_pre_topc(X2,sK2) | v2_struct_0(X2) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X2),X2,sK3) | ~v5_pre_topc(sK4,sK2,sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.72/0.62    inference(subsumption_resolution,[],[f1331,f77])).
% 1.72/0.62  fof(f1331,plain,(
% 1.72/0.62    ( ! [X2] : (~m1_pre_topc(X2,sK2) | v2_struct_0(X2) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X2),X2,sK3) | ~v5_pre_topc(sK4,sK2,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.72/0.62    inference(subsumption_resolution,[],[f1330,f78])).
% 1.72/0.62  fof(f1330,plain,(
% 1.72/0.62    ( ! [X2] : (~m1_pre_topc(X2,sK2) | v2_struct_0(X2) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X2),X2,sK3) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.72/0.62    inference(subsumption_resolution,[],[f274,f79])).
% 1.72/0.62  fof(f274,plain,(
% 1.72/0.62    ( ! [X2] : (~m1_pre_topc(X2,sK2) | v2_struct_0(X2) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X2),X2,sK3) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.72/0.62    inference(resolution,[],[f80,f157])).
% 1.72/0.62  fof(f157,plain,(
% 1.72/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.72/0.62    inference(cnf_transformation,[],[f49])).
% 1.72/0.62  fof(f239,plain,(
% 1.72/0.62    spl7_3 | spl7_5),
% 1.72/0.62    inference(avatar_split_clause,[],[f89,f178,f170])).
% 1.72/0.62  fof(f89,plain,(
% 1.72/0.62    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | v5_pre_topc(sK4,sK2,sK3)),
% 1.72/0.62    inference(cnf_transformation,[],[f62])).
% 1.72/0.62  fof(f235,plain,(
% 1.72/0.62    spl7_3 | spl7_6),
% 1.72/0.62    inference(avatar_split_clause,[],[f93,f182,f170])).
% 1.72/0.62  fof(f93,plain,(
% 1.72/0.62    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | v5_pre_topc(sK4,sK2,sK3)),
% 1.72/0.62    inference(cnf_transformation,[],[f62])).
% 1.72/0.62  fof(f231,plain,(
% 1.72/0.62    spl7_3 | spl7_7),
% 1.72/0.62    inference(avatar_split_clause,[],[f97,f186,f170])).
% 1.72/0.62  fof(f97,plain,(
% 1.72/0.62    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | v5_pre_topc(sK4,sK2,sK3)),
% 1.72/0.62    inference(cnf_transformation,[],[f62])).
% 1.72/0.62  fof(f227,plain,(
% 1.72/0.62    spl7_3 | spl7_8),
% 1.72/0.62    inference(avatar_split_clause,[],[f101,f190,f170])).
% 1.72/0.62  fof(f101,plain,(
% 1.72/0.62    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | v5_pre_topc(sK4,sK2,sK3)),
% 1.72/0.62    inference(cnf_transformation,[],[f62])).
% 1.72/0.62  fof(f223,plain,(
% 1.72/0.62    spl7_3 | spl7_9),
% 1.72/0.62    inference(avatar_split_clause,[],[f105,f194,f170])).
% 1.72/0.62  fof(f105,plain,(
% 1.72/0.62    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | v5_pre_topc(sK4,sK2,sK3)),
% 1.72/0.62    inference(cnf_transformation,[],[f62])).
% 1.72/0.62  fof(f219,plain,(
% 1.72/0.62    spl7_3 | spl7_10),
% 1.72/0.62    inference(avatar_split_clause,[],[f109,f198,f170])).
% 1.72/0.62  fof(f109,plain,(
% 1.72/0.62    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | v5_pre_topc(sK4,sK2,sK3)),
% 1.72/0.62    inference(cnf_transformation,[],[f62])).
% 1.72/0.62  fof(f215,plain,(
% 1.72/0.62    spl7_3 | spl7_11),
% 1.72/0.62    inference(avatar_split_clause,[],[f113,f202,f170])).
% 1.72/0.62  fof(f113,plain,(
% 1.72/0.62    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | v5_pre_topc(sK4,sK2,sK3)),
% 1.72/0.62    inference(cnf_transformation,[],[f62])).
% 1.72/0.62  fof(f211,plain,(
% 1.72/0.62    spl7_3 | spl7_12),
% 1.72/0.62    inference(avatar_split_clause,[],[f117,f206,f170])).
% 1.72/0.62  fof(f117,plain,(
% 1.72/0.62    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | v5_pre_topc(sK4,sK2,sK3)),
% 1.72/0.62    inference(cnf_transformation,[],[f62])).
% 1.72/0.62  fof(f209,plain,(
% 1.72/0.62    ~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12),
% 1.72/0.62    inference(avatar_split_clause,[],[f119,f206,f202,f198,f194,f190,f186,f182,f178,f174,f170,f166,f162])).
% 1.72/0.62  fof(f119,plain,(
% 1.72/0.62    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 1.72/0.62    inference(cnf_transformation,[],[f62])).
% 1.72/0.62  % SZS output end Proof for theBenchmark
% 1.72/0.62  % (25596)------------------------------
% 1.72/0.62  % (25596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.62  % (25596)Termination reason: Refutation
% 1.72/0.62  
% 1.72/0.62  % (25596)Memory used [KB]: 12537
% 1.72/0.62  % (25596)Time elapsed: 0.198 s
% 1.72/0.62  % (25596)------------------------------
% 1.72/0.62  % (25596)------------------------------
% 1.72/0.62  % (25594)Success in time 0.257 s
%------------------------------------------------------------------------------
