%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:48 EST 2020

% Result     : Theorem 2.23s
% Output     : Refutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :  240 (3053 expanded)
%              Number of leaves         :   32 (1455 expanded)
%              Depth                    :   32
%              Number of atoms          : 1541 (42051 expanded)
%              Number of equality atoms :   63 (3206 expanded)
%              Maximal formula depth    :   24 (   8 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1384,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f170,f174,f276,f365,f372,f392,f399,f443,f448,f475,f509,f1099,f1354,f1378])).

fof(f1378,plain,
    ( spl7_1
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_46 ),
    inference(avatar_contradiction_clause,[],[f1377])).

fof(f1377,plain,
    ( $false
    | spl7_1
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f1375,f271])).

fof(f271,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f270])).

fof(f270,plain,
    ( spl7_5
  <=> m1_pre_topc(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f1375,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | spl7_1
    | ~ spl7_3
    | ~ spl7_46 ),
    inference(resolution,[],[f1374,f217])).

fof(f217,plain,
    ( ! [X0] :
        ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(X0),u1_struct_0(sK3),sK6,sK6)
        | ~ m1_pre_topc(X0,sK2) )
    | spl7_1
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f216,f53])).

fof(f53,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5)))
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK6)
    & sK2 = k1_tsep_1(sK2,sK4,sK5)
    & m1_pre_topc(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f15,f44,f43,f42,f41,f40])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & k1_tsep_1(X0,X2,X3) = X0
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
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
                      ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(sK2,X1,X2,X3,k2_tmap_1(sK2,X1,X4,X2),k2_tmap_1(sK2,X1,X4,X3)))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & sK2 = k1_tsep_1(sK2,X2,X3)
                  & m1_pre_topc(X3,sK2)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(sK2,X1,X2,X3,k2_tmap_1(sK2,X1,X4,X2),k2_tmap_1(sK2,X1,X4,X3)))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & sK2 = k1_tsep_1(sK2,X2,X3)
                & m1_pre_topc(X3,sK2)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3),X4,k10_tmap_1(sK2,sK3,X2,X3,k2_tmap_1(sK2,sK3,X4,X2),k2_tmap_1(sK2,sK3,X4,X3)))
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                  & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3))
                  & v1_funct_1(X4) )
              & sK2 = k1_tsep_1(sK2,X2,X3)
              & m1_pre_topc(X3,sK2)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK2)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3),X4,k10_tmap_1(sK2,sK3,X2,X3,k2_tmap_1(sK2,sK3,X4,X2),k2_tmap_1(sK2,sK3,X4,X3)))
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3))
                & v1_funct_1(X4) )
            & sK2 = k1_tsep_1(sK2,X2,X3)
            & m1_pre_topc(X3,sK2)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK2)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3),X4,k10_tmap_1(sK2,sK3,sK4,X3,k2_tmap_1(sK2,sK3,X4,sK4),k2_tmap_1(sK2,sK3,X4,X3)))
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
              & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3))
              & v1_funct_1(X4) )
          & sK2 = k1_tsep_1(sK2,sK4,X3)
          & m1_pre_topc(X3,sK2)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK4,sK2)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3),X4,k10_tmap_1(sK2,sK3,sK4,X3,k2_tmap_1(sK2,sK3,X4,sK4),k2_tmap_1(sK2,sK3,X4,X3)))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
            & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3))
            & v1_funct_1(X4) )
        & sK2 = k1_tsep_1(sK2,sK4,X3)
        & m1_pre_topc(X3,sK2)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),X4,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,X4,sK4),k2_tmap_1(sK2,sK3,X4,sK5)))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
          & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3))
          & v1_funct_1(X4) )
      & sK2 = k1_tsep_1(sK2,sK4,sK5)
      & m1_pre_topc(sK5,sK2)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X4] :
        ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),X4,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,X4,sK4),k2_tmap_1(sK2,sK3,X4,sK5)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3))
        & v1_funct_1(X4) )
   => ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5)))
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      & v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & k1_tsep_1(X0,X2,X3) = X0
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & k1_tsep_1(X0,X2,X3) = X0
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( k1_tsep_1(X0,X2,X3) = X0
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X4) )
                         => r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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
                 => ( k1_tsep_1(X0,X2,X3) = X0
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_tmap_1)).

fof(f216,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | ~ l1_pre_topc(sK2)
        | r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(X0),u1_struct_0(sK3),sK6,sK6) )
    | spl7_1
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f215,f52])).

fof(f52,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f215,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(X0),u1_struct_0(sK3),sK6,sK6) )
    | spl7_1
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f214,f51])).

fof(f51,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f214,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(X0),u1_struct_0(sK3),sK6,sK6) )
    | spl7_1
    | ~ spl7_3 ),
    inference(duplicate_literal_removal,[],[f213])).

fof(f213,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(X0),u1_struct_0(sK3),sK6,sK6)
        | ~ l1_pre_topc(sK2) )
    | spl7_1
    | ~ spl7_3 ),
    inference(resolution,[],[f206,f67])).

fof(f67,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f206,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK2,X1)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(X0),u1_struct_0(sK3),sK6,sK6) )
    | spl7_1
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f205,f63])).

fof(f63,plain,(
    v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f45])).

fof(f205,plain,
    ( ! [X0,X1] :
        ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(X0),u1_struct_0(sK3),sK6,sK6)
        | ~ m1_pre_topc(X0,X1)
        | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK2,X1) )
    | spl7_1
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f204,f62])).

fof(f62,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f204,plain,
    ( ! [X0,X1] :
        ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(X0),u1_struct_0(sK3),sK6,sK6)
        | ~ m1_pre_topc(X0,X1)
        | ~ v1_funct_1(sK6)
        | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK2,X1) )
    | spl7_1
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f200,f144])).

fof(f144,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl7_1
  <=> v1_xboole_0(u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f200,plain,
    ( ! [X0,X1] :
        ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(X0),u1_struct_0(sK3),sK6,sK6)
        | ~ m1_pre_topc(X0,X1)
        | v1_xboole_0(u1_struct_0(sK3))
        | ~ v1_funct_1(sK6)
        | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK2,X1) )
    | ~ spl7_3 ),
    inference(resolution,[],[f169,f64])).

fof(f64,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f45])).

fof(f169,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | r1_funct_2(X3,X4,u1_struct_0(X0),u1_struct_0(sK3),X2,X2)
        | ~ m1_pre_topc(X0,X1)
        | v1_xboole_0(X4)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X3,X4)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK2,X1) )
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl7_3
  <=> ! [X1,X3,X0,X2,X4] :
        ( ~ m1_pre_topc(X0,X1)
        | r1_funct_2(X3,X4,u1_struct_0(X0),u1_struct_0(sK3),X2,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | v1_xboole_0(X4)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X3,X4)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f1374,plain,
    ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(sK2),u1_struct_0(sK3),sK6,sK6)
    | ~ spl7_46 ),
    inference(backward_demodulation,[],[f86,f1098])).

fof(f1098,plain,
    ( sK6 = k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5))
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f1096])).

fof(f1096,plain,
    ( spl7_46
  <=> sK6 = k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f86,plain,(
    ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5))) ),
    inference(backward_demodulation,[],[f65,f61])).

fof(f61,plain,(
    sK2 = k1_tsep_1(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f65,plain,(
    ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5))) ),
    inference(cnf_transformation,[],[f45])).

fof(f1354,plain,
    ( ~ spl7_7
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_15
    | ~ spl7_16
    | spl7_45 ),
    inference(avatar_contradiction_clause,[],[f1353])).

fof(f1353,plain,
    ( $false
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_15
    | ~ spl7_16
    | spl7_45 ),
    inference(subsumption_resolution,[],[f1352,f51])).

fof(f1352,plain,
    ( v2_struct_0(sK2)
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_15
    | ~ spl7_16
    | spl7_45 ),
    inference(subsumption_resolution,[],[f1351,f52])).

fof(f1351,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_15
    | ~ spl7_16
    | spl7_45 ),
    inference(subsumption_resolution,[],[f1350,f53])).

fof(f1350,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_15
    | ~ spl7_16
    | spl7_45 ),
    inference(subsumption_resolution,[],[f1349,f57])).

fof(f57,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f1349,plain,
    ( v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_15
    | ~ spl7_16
    | spl7_45 ),
    inference(subsumption_resolution,[],[f1348,f58])).

fof(f58,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f1348,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_15
    | ~ spl7_16
    | spl7_45 ),
    inference(subsumption_resolution,[],[f1347,f60])).

fof(f60,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f1347,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_15
    | ~ spl7_16
    | spl7_45 ),
    inference(subsumption_resolution,[],[f1346,f364])).

fof(f364,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f362])).

fof(f362,plain,
    ( spl7_7
  <=> v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f1346,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_15
    | ~ spl7_16
    | spl7_45 ),
    inference(subsumption_resolution,[],[f1345,f442])).

fof(f442,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f440])).

fof(f440,plain,
    ( spl7_12
  <=> v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f1345,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_15
    | ~ spl7_16
    | spl7_45 ),
    inference(subsumption_resolution,[],[f1339,f474])).

fof(f474,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f472])).

fof(f472,plain,
    ( spl7_15
  <=> m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f1339,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_16
    | spl7_45 ),
    inference(resolution,[],[f523,f1094])).

fof(f1094,plain,
    ( ~ sP1(sK3,sK5,sK4,sK2,k2_tmap_1(sK2,sK3,sK6,sK5),k2_tmap_1(sK2,sK3,sK6,sK4))
    | spl7_45 ),
    inference(avatar_component_clause,[],[f1092])).

fof(f1092,plain,
    ( spl7_45
  <=> sP1(sK3,sK5,sK4,sK2,k2_tmap_1(sK2,sK3,sK6,sK5),k2_tmap_1(sK2,sK3,sK6,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f523,plain,
    ( ! [X2,X0,X1] :
        ( sP1(sK3,sK5,X0,X1,k2_tmap_1(sK2,sK3,sK6,sK5),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(sK5,X1)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f522,f54])).

fof(f54,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f522,plain,
    ( ! [X2,X0,X1] :
        ( sP1(sK3,sK5,X0,X1,k2_tmap_1(sK2,sK3,sK6,sK5),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(sK5,X1)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f521,f55])).

fof(f55,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f521,plain,
    ( ! [X2,X0,X1] :
        ( sP1(sK3,sK5,X0,X1,k2_tmap_1(sK2,sK3,sK6,sK5),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(sK5,X1)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f520,f56])).

fof(f56,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f520,plain,
    ( ! [X2,X0,X1] :
        ( sP1(sK3,sK5,X0,X1,k2_tmap_1(sK2,sK3,sK6,sK5),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(sK5,X1)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f519,f59])).

fof(f59,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f519,plain,
    ( ! [X2,X0,X1] :
        ( sP1(sK3,sK5,X0,X1,k2_tmap_1(sK2,sK3,sK6,sK5),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(sK5,X1)
        | v2_struct_0(sK5)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_9
    | ~ spl7_13
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f518,f391])).

fof(f391,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK5))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f389])).

fof(f389,plain,
    ( spl7_9
  <=> v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f518,plain,
    ( ! [X2,X0,X1] :
        ( sP1(sK3,sK5,X0,X1,k2_tmap_1(sK2,sK3,sK6,sK5),X2)
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK5))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(sK5,X1)
        | v2_struct_0(sK5)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_13
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f510,f447])).

fof(f447,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f445])).

fof(f445,plain,
    ( spl7_13
  <=> v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f510,plain,
    ( ! [X2,X0,X1] :
        ( sP1(sK3,sK5,X0,X1,k2_tmap_1(sK2,sK3,sK6,sK5),X2)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK5))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(sK5,X1)
        | v2_struct_0(sK5)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_16 ),
    inference(resolution,[],[f508,f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | sP1(X1,X3,X2,X0,X5,X4)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
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
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( sP1(X1,X3,X2,X0,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
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
    inference(definition_folding,[],[f35,f38])).

fof(f38,plain,(
    ! [X1,X3,X2,X0,X5,X4] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ sP1(X1,X3,X2,X0,X5,X4) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_tmap_1)).

fof(f508,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f506])).

fof(f506,plain,
    ( spl7_16
  <=> m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f1099,plain,
    ( ~ spl7_45
    | spl7_46
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f916,f270,f1096,f1092])).

fof(f916,plain,
    ( sK6 = k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5))
    | ~ sP1(sK3,sK5,sK4,sK2,k2_tmap_1(sK2,sK3,sK6,sK5),k2_tmap_1(sK2,sK3,sK6,sK4))
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f915,f62])).

fof(f915,plain,
    ( sK6 = k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5))
    | ~ v1_funct_1(sK6)
    | ~ sP1(sK3,sK5,sK4,sK2,k2_tmap_1(sK2,sK3,sK6,sK5),k2_tmap_1(sK2,sK3,sK6,sK4))
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f914,f63])).

fof(f914,plain,
    ( sK6 = k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5))
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ sP1(sK3,sK5,sK4,sK2,k2_tmap_1(sK2,sK3,sK6,sK5),k2_tmap_1(sK2,sK3,sK6,sK4))
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f913,f64])).

fof(f913,plain,
    ( sK6 = k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ sP1(sK3,sK5,sK4,sK2,k2_tmap_1(sK2,sK3,sK6,sK5),k2_tmap_1(sK2,sK3,sK6,sK4))
    | ~ spl7_5 ),
    inference(resolution,[],[f891,f122])).

fof(f122,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X14),X15,k10_tmap_1(sK2,X14,sK4,sK5,X16,X17))
      | k10_tmap_1(sK2,X14,sK4,sK5,X16,X17) = X15
      | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X14))))
      | ~ v1_funct_2(X15,u1_struct_0(sK2),u1_struct_0(X14))
      | ~ v1_funct_1(X15)
      | ~ sP1(X14,sK5,sK4,sK2,X17,X16) ) ),
    inference(subsumption_resolution,[],[f121,f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4))
      | ~ sP1(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
        & v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
        & v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4)) )
      | ~ sP1(X0,X1,X2,X3,X4,X5) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X1,X3,X2,X0,X5,X4] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ sP1(X1,X3,X2,X0,X5,X4) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f121,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X14),X15,k10_tmap_1(sK2,X14,sK4,sK5,X16,X17))
      | k10_tmap_1(sK2,X14,sK4,sK5,X16,X17) = X15
      | ~ v1_funct_1(k10_tmap_1(sK2,X14,sK4,sK5,X16,X17))
      | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X14))))
      | ~ v1_funct_2(X15,u1_struct_0(sK2),u1_struct_0(X14))
      | ~ v1_funct_1(X15)
      | ~ sP1(X14,sK5,sK4,sK2,X17,X16) ) ),
    inference(subsumption_resolution,[],[f114,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k10_tmap_1(sK2,X0,sK4,sK5,X1,X2),u1_struct_0(sK2),u1_struct_0(X0))
      | ~ sP1(X0,sK5,sK4,sK2,X2,X1) ) ),
    inference(superposition,[],[f81,f61])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
      | ~ sP1(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f114,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X14),X15,k10_tmap_1(sK2,X14,sK4,sK5,X16,X17))
      | k10_tmap_1(sK2,X14,sK4,sK5,X16,X17) = X15
      | ~ v1_funct_2(k10_tmap_1(sK2,X14,sK4,sK5,X16,X17),u1_struct_0(sK2),u1_struct_0(X14))
      | ~ v1_funct_1(k10_tmap_1(sK2,X14,sK4,sK5,X16,X17))
      | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X14))))
      | ~ v1_funct_2(X15,u1_struct_0(sK2),u1_struct_0(X14))
      | ~ v1_funct_1(X15)
      | ~ sP1(X14,sK5,sK4,sK2,X17,X16) ) ),
    inference(resolution,[],[f73,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_tmap_1(sK2,X0,sK4,sK5,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | ~ sP1(X0,sK5,sK4,sK2,X2,X1) ) ),
    inference(superposition,[],[f82,f61])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
      | ~ sP1(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f891,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5)))
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f890,f316])).

fof(f316,plain,
    ( k2_tmap_1(sK2,sK3,sK6,sK5) = k3_tmap_1(sK2,sK3,sK2,sK5,sK6)
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f312,f197])).

fof(f197,plain,(
    k2_tmap_1(sK2,sK3,sK6,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(sK5)) ),
    inference(resolution,[],[f186,f60])).

fof(f186,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f185,f51])).

fof(f185,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f184,f52])).

fof(f184,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0))
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f183,f53])).

fof(f183,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0))
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f182,f54])).

fof(f182,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0))
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f181,f55])).

fof(f181,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0))
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f180,f56])).

fof(f180,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0))
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f179,f62])).

fof(f179,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0))
      | ~ v1_funct_1(sK6)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f175,f63])).

fof(f175,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0))
      | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK6)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f71,f64])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f312,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(sK5)) = k3_tmap_1(sK2,sK3,sK2,sK5,sK6)
    | ~ spl7_5 ),
    inference(resolution,[],[f310,f60])).

fof(f310,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(sK2,sK3,sK2,X0,sK6) )
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f309,f51])).

fof(f309,plain,
    ( ! [X0] :
        ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(sK2,sK3,sK2,X0,sK6)
        | ~ m1_pre_topc(X0,sK2)
        | v2_struct_0(sK2) )
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f308,f52])).

fof(f308,plain,
    ( ! [X0] :
        ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(sK2,sK3,sK2,X0,sK6)
        | ~ m1_pre_topc(X0,sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f305,f53])).

fof(f305,plain,
    ( ! [X0] :
        ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(sK2,sK3,sK2,X0,sK6)
        | ~ m1_pre_topc(X0,sK2)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl7_5 ),
    inference(resolution,[],[f286,f271])).

fof(f286,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK2,X1)
      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK6)
      | ~ m1_pre_topc(X0,sK2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f285,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f285,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK6)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f284,f54])).

fof(f284,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK6)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f283,f55])).

fof(f283,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK6)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f282,f56])).

fof(f282,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK6)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f281,f62])).

fof(f281,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK6)
      | ~ v1_funct_1(sK6)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f277,f63])).

fof(f277,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK6)
      | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK6)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f69,f64])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X2)
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
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
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f890,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6)))
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f889,f54])).

fof(f889,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6)))
    | v2_struct_0(sK3)
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f888,f55])).

fof(f888,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6)))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f887,f56])).

fof(f887,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f886,f62])).

fof(f886,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6)))
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f885,f63])).

fof(f885,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6)))
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f880,f64])).

fof(f880,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl7_5 ),
    inference(superposition,[],[f619,f315])).

fof(f315,plain,
    ( k2_tmap_1(sK2,sK3,sK6,sK4) = k3_tmap_1(sK2,sK3,sK2,sK4,sK6)
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f311,f196])).

fof(f196,plain,(
    k2_tmap_1(sK2,sK3,sK6,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(sK4)) ),
    inference(resolution,[],[f186,f58])).

fof(f311,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(sK4)) = k3_tmap_1(sK2,sK3,sK2,sK4,sK6)
    | ~ spl7_5 ),
    inference(resolution,[],[f310,f58])).

fof(f619,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f618,f51])).

fof(f618,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f617,f52])).

fof(f617,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f616,f53])).

fof(f616,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f615,f57])).

fof(f615,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f614,f58])).

fof(f614,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ m1_pre_topc(sK4,sK2)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f613,f59])).

fof(f613,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | v2_struct_0(sK5)
      | ~ m1_pre_topc(sK4,sK2)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f612,f60])).

fof(f612,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ m1_pre_topc(sK5,sK2)
      | v2_struct_0(sK5)
      | ~ m1_pre_topc(sK4,sK2)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(superposition,[],[f70,f61])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
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
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_tmap_1)).

fof(f509,plain,
    ( ~ spl7_8
    | spl7_16
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f338,f270,f506,f385])).

fof(f385,plain,
    ( spl7_8
  <=> sP0(sK3,sK5,sK6,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f338,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ sP0(sK3,sK5,sK6,sK2,sK2)
    | ~ spl7_5 ),
    inference(superposition,[],[f77,f316])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2)) )
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ sP0(X1,X3,X4,X2,X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ sP0(X1,X3,X4,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f475,plain,
    ( ~ spl7_6
    | spl7_15
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f327,f270,f472,f358])).

fof(f358,plain,
    ( spl7_6
  <=> sP0(sK3,sK4,sK6,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f327,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ sP0(sK3,sK4,sK6,sK2,sK2)
    | ~ spl7_5 ),
    inference(superposition,[],[f77,f315])).

fof(f448,plain,
    ( ~ spl7_8
    | spl7_13
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f339,f270,f445,f385])).

fof(f339,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ sP0(sK3,sK5,sK6,sK2,sK2)
    | ~ spl7_5 ),
    inference(superposition,[],[f76,f316])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f443,plain,
    ( ~ spl7_6
    | spl7_12
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f328,f270,f440,f358])).

fof(f328,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ sP0(sK3,sK4,sK6,sK2,sK2)
    | ~ spl7_5 ),
    inference(superposition,[],[f76,f315])).

fof(f399,plain,
    ( ~ spl7_5
    | spl7_8 ),
    inference(avatar_contradiction_clause,[],[f398])).

fof(f398,plain,
    ( $false
    | ~ spl7_5
    | spl7_8 ),
    inference(subsumption_resolution,[],[f397,f51])).

fof(f397,plain,
    ( v2_struct_0(sK2)
    | ~ spl7_5
    | spl7_8 ),
    inference(subsumption_resolution,[],[f396,f52])).

fof(f396,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl7_5
    | spl7_8 ),
    inference(subsumption_resolution,[],[f395,f53])).

fof(f395,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl7_5
    | spl7_8 ),
    inference(subsumption_resolution,[],[f394,f271])).

fof(f394,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl7_8 ),
    inference(subsumption_resolution,[],[f393,f60])).

fof(f393,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl7_8 ),
    inference(resolution,[],[f387,f158])).

fof(f158,plain,(
    ! [X0,X1] :
      ( sP0(sK3,X0,sK6,sK2,X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f157,f54])).

fof(f157,plain,(
    ! [X0,X1] :
      ( sP0(sK3,X0,sK6,sK2,X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f156,f55])).

fof(f156,plain,(
    ! [X0,X1] :
      ( sP0(sK3,X0,sK6,sK2,X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f155,f56])).

fof(f155,plain,(
    ! [X0,X1] :
      ( sP0(sK3,X0,sK6,sK2,X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f154,f62])).

fof(f154,plain,(
    ! [X0,X1] :
      ( sP0(sK3,X0,sK6,sK2,X1)
      | ~ v1_funct_1(sK6)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f150,f63])).

fof(f150,plain,(
    ! [X0,X1] :
      ( sP0(sK3,X0,sK6,sK2,X1)
      | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK6)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f78,f64])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | sP0(X1,X3,X4,X2,X0)
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
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( sP0(X1,X3,X4,X2,X0)
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
    inference(definition_folding,[],[f31,f36])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).

fof(f387,plain,
    ( ~ sP0(sK3,sK5,sK6,sK2,sK2)
    | spl7_8 ),
    inference(avatar_component_clause,[],[f385])).

fof(f392,plain,
    ( ~ spl7_8
    | spl7_9
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f340,f270,f389,f385])).

fof(f340,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK5))
    | ~ sP0(sK3,sK5,sK6,sK2,sK2)
    | ~ spl7_5 ),
    inference(superposition,[],[f75,f316])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f372,plain,
    ( ~ spl7_5
    | spl7_6 ),
    inference(avatar_contradiction_clause,[],[f371])).

fof(f371,plain,
    ( $false
    | ~ spl7_5
    | spl7_6 ),
    inference(subsumption_resolution,[],[f370,f51])).

fof(f370,plain,
    ( v2_struct_0(sK2)
    | ~ spl7_5
    | spl7_6 ),
    inference(subsumption_resolution,[],[f369,f52])).

fof(f369,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl7_5
    | spl7_6 ),
    inference(subsumption_resolution,[],[f368,f53])).

fof(f368,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl7_5
    | spl7_6 ),
    inference(subsumption_resolution,[],[f367,f271])).

fof(f367,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl7_6 ),
    inference(subsumption_resolution,[],[f366,f58])).

fof(f366,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl7_6 ),
    inference(resolution,[],[f360,f158])).

fof(f360,plain,
    ( ~ sP0(sK3,sK4,sK6,sK2,sK2)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f358])).

fof(f365,plain,
    ( ~ spl7_6
    | spl7_7
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f329,f270,f362,f358])).

fof(f329,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4))
    | ~ sP0(sK3,sK4,sK6,sK2,sK2)
    | ~ spl7_5 ),
    inference(superposition,[],[f75,f315])).

fof(f276,plain,(
    spl7_5 ),
    inference(avatar_contradiction_clause,[],[f275])).

fof(f275,plain,
    ( $false
    | spl7_5 ),
    inference(subsumption_resolution,[],[f274,f53])).

fof(f274,plain,
    ( ~ l1_pre_topc(sK2)
    | spl7_5 ),
    inference(resolution,[],[f272,f67])).

fof(f272,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | spl7_5 ),
    inference(avatar_component_clause,[],[f270])).

fof(f174,plain,(
    ~ spl7_1 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f172,f54])).

fof(f172,plain,
    ( v2_struct_0(sK3)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f171,f88])).

fof(f88,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f66,f56])).

fof(f66,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f171,plain,
    ( ~ l1_struct_0(sK3)
    | v2_struct_0(sK3)
    | ~ spl7_1 ),
    inference(resolution,[],[f145,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f145,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f143])).

fof(f170,plain,
    ( spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f165,f168,f143])).

fof(f165,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X2,X3,X4)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(u1_struct_0(sK3))
      | v1_xboole_0(X4)
      | r1_funct_2(X3,X4,u1_struct_0(X0),u1_struct_0(sK3),X2,X2) ) ),
    inference(resolution,[],[f158,f137])).

fof(f137,plain,(
    ! [X6,X4,X10,X8,X7,X5,X3,X9] :
      ( ~ sP0(X6,X5,X10,X9,X8)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X7,X3,X4)
      | ~ v1_funct_1(X7)
      | v1_xboole_0(u1_struct_0(X6))
      | v1_xboole_0(X4)
      | r1_funct_2(X3,X4,u1_struct_0(X5),u1_struct_0(X6),X7,X7) ) ),
    inference(subsumption_resolution,[],[f136,f75])).

fof(f136,plain,(
    ! [X6,X4,X10,X8,X7,X5,X3,X9] :
      ( r1_funct_2(X3,X4,u1_struct_0(X5),u1_struct_0(X6),X7,X7)
      | ~ v1_funct_1(k3_tmap_1(X8,X6,X9,X5,X10))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X7,X3,X4)
      | ~ v1_funct_1(X7)
      | v1_xboole_0(u1_struct_0(X6))
      | v1_xboole_0(X4)
      | ~ sP0(X6,X5,X10,X9,X8) ) ),
    inference(subsumption_resolution,[],[f131,f76])).

fof(f131,plain,(
    ! [X6,X4,X10,X8,X7,X5,X3,X9] :
      ( r1_funct_2(X3,X4,u1_struct_0(X5),u1_struct_0(X6),X7,X7)
      | ~ v1_funct_2(k3_tmap_1(X8,X6,X9,X5,X10),u1_struct_0(X5),u1_struct_0(X6))
      | ~ v1_funct_1(k3_tmap_1(X8,X6,X9,X5,X10))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X7,X3,X4)
      | ~ v1_funct_1(X7)
      | v1_xboole_0(u1_struct_0(X6))
      | v1_xboole_0(X4)
      | ~ sP0(X6,X5,X10,X9,X8) ) ),
    inference(resolution,[],[f79,f77])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => r1_funct_2(X0,X1,X2,X3,X4,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r1_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:10:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (24256)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.48  % (24248)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.50  % (24257)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.50  % (24241)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  % (24246)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.51  % (24242)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (24258)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.51  % (24244)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.52  % (24245)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.52  % (24249)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (24238)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (24250)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (24237)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.53  % (24251)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.53  % (24239)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.53  % (24254)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.54  % (24243)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.54  % (24260)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.55  % (24253)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.55  % (24255)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.55  % (24252)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.55  % (24262)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.55  % (24240)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.56  % (24247)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.56  % (24259)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.53/0.56  % (24261)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 2.13/0.64  % (24246)Refutation not found, incomplete strategy% (24246)------------------------------
% 2.13/0.64  % (24246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.64  % (24246)Termination reason: Refutation not found, incomplete strategy
% 2.13/0.64  
% 2.13/0.64  % (24246)Memory used [KB]: 6396
% 2.13/0.64  % (24246)Time elapsed: 0.221 s
% 2.13/0.64  % (24246)------------------------------
% 2.13/0.64  % (24246)------------------------------
% 2.23/0.66  % (24262)Refutation found. Thanks to Tanya!
% 2.23/0.66  % SZS status Theorem for theBenchmark
% 2.23/0.66  % SZS output start Proof for theBenchmark
% 2.23/0.66  fof(f1384,plain,(
% 2.23/0.66    $false),
% 2.23/0.66    inference(avatar_sat_refutation,[],[f170,f174,f276,f365,f372,f392,f399,f443,f448,f475,f509,f1099,f1354,f1378])).
% 2.23/0.66  fof(f1378,plain,(
% 2.23/0.66    spl7_1 | ~spl7_3 | ~spl7_5 | ~spl7_46),
% 2.23/0.66    inference(avatar_contradiction_clause,[],[f1377])).
% 2.23/0.66  fof(f1377,plain,(
% 2.23/0.66    $false | (spl7_1 | ~spl7_3 | ~spl7_5 | ~spl7_46)),
% 2.23/0.66    inference(subsumption_resolution,[],[f1375,f271])).
% 2.23/0.66  fof(f271,plain,(
% 2.23/0.66    m1_pre_topc(sK2,sK2) | ~spl7_5),
% 2.23/0.66    inference(avatar_component_clause,[],[f270])).
% 2.23/0.66  fof(f270,plain,(
% 2.23/0.66    spl7_5 <=> m1_pre_topc(sK2,sK2)),
% 2.23/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 2.23/0.66  fof(f1375,plain,(
% 2.23/0.66    ~m1_pre_topc(sK2,sK2) | (spl7_1 | ~spl7_3 | ~spl7_46)),
% 2.23/0.66    inference(resolution,[],[f1374,f217])).
% 2.23/0.66  fof(f217,plain,(
% 2.23/0.66    ( ! [X0] : (r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(X0),u1_struct_0(sK3),sK6,sK6) | ~m1_pre_topc(X0,sK2)) ) | (spl7_1 | ~spl7_3)),
% 2.23/0.66    inference(subsumption_resolution,[],[f216,f53])).
% 2.23/0.66  fof(f53,plain,(
% 2.23/0.66    l1_pre_topc(sK2)),
% 2.23/0.66    inference(cnf_transformation,[],[f45])).
% 2.23/0.66  fof(f45,plain,(
% 2.23/0.66    ((((~r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK6)) & sK2 = k1_tsep_1(sK2,sK4,sK5) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.23/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f15,f44,f43,f42,f41,f40])).
% 2.23/0.66  fof(f40,plain,(
% 2.23/0.66    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK2),u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(sK2,X1,X2,X3,k2_tmap_1(sK2,X1,X4,X2),k2_tmap_1(sK2,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X4)) & sK2 = k1_tsep_1(sK2,X2,X3) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.23/0.66    introduced(choice_axiom,[])).
% 2.23/0.68  fof(f41,plain,(
% 2.23/0.68    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK2),u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(sK2,X1,X2,X3,k2_tmap_1(sK2,X1,X4,X2),k2_tmap_1(sK2,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X4)) & sK2 = k1_tsep_1(sK2,X2,X3) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3),X4,k10_tmap_1(sK2,sK3,X2,X3,k2_tmap_1(sK2,sK3,X4,X2),k2_tmap_1(sK2,sK3,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) & sK2 = k1_tsep_1(sK2,X2,X3) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 2.23/0.68    introduced(choice_axiom,[])).
% 2.23/0.68  fof(f42,plain,(
% 2.23/0.68    ? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3),X4,k10_tmap_1(sK2,sK3,X2,X3,k2_tmap_1(sK2,sK3,X4,X2),k2_tmap_1(sK2,sK3,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) & sK2 = k1_tsep_1(sK2,X2,X3) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3),X4,k10_tmap_1(sK2,sK3,sK4,X3,k2_tmap_1(sK2,sK3,X4,sK4),k2_tmap_1(sK2,sK3,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) & sK2 = k1_tsep_1(sK2,sK4,X3) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4))),
% 2.23/0.68    introduced(choice_axiom,[])).
% 2.23/0.68  fof(f43,plain,(
% 2.23/0.68    ? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3),X4,k10_tmap_1(sK2,sK3,sK4,X3,k2_tmap_1(sK2,sK3,X4,sK4),k2_tmap_1(sK2,sK3,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) & sK2 = k1_tsep_1(sK2,sK4,X3) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) => (? [X4] : (~r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),X4,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,X4,sK4),k2_tmap_1(sK2,sK3,X4,sK5))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) & sK2 = k1_tsep_1(sK2,sK4,sK5) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5))),
% 2.23/0.68    introduced(choice_axiom,[])).
% 2.23/0.68  fof(f44,plain,(
% 2.23/0.68    ? [X4] : (~r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),X4,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,X4,sK4),k2_tmap_1(sK2,sK3,X4,sK5))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) => (~r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK6))),
% 2.23/0.68    introduced(choice_axiom,[])).
% 2.23/0.68  fof(f15,plain,(
% 2.23/0.68    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.23/0.68    inference(flattening,[],[f14])).
% 2.23/0.68  fof(f14,plain,(
% 2.23/0.68    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & k1_tsep_1(X0,X2,X3) = X0) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.23/0.68    inference(ennf_transformation,[],[f13])).
% 2.23/0.68  fof(f13,negated_conjecture,(
% 2.23/0.68    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X2,X3) = X0 => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))))))))),
% 2.23/0.68    inference(negated_conjecture,[],[f12])).
% 2.23/0.68  fof(f12,conjecture,(
% 2.23/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X2,X3) = X0 => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))))))))),
% 2.23/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_tmap_1)).
% 2.23/0.68  fof(f216,plain,(
% 2.23/0.68    ( ! [X0] : (~m1_pre_topc(X0,sK2) | ~l1_pre_topc(sK2) | r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(X0),u1_struct_0(sK3),sK6,sK6)) ) | (spl7_1 | ~spl7_3)),
% 2.23/0.68    inference(subsumption_resolution,[],[f215,f52])).
% 2.23/0.68  fof(f52,plain,(
% 2.23/0.68    v2_pre_topc(sK2)),
% 2.23/0.68    inference(cnf_transformation,[],[f45])).
% 2.23/0.68  fof(f215,plain,(
% 2.23/0.68    ( ! [X0] : (~m1_pre_topc(X0,sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(X0),u1_struct_0(sK3),sK6,sK6)) ) | (spl7_1 | ~spl7_3)),
% 2.23/0.68    inference(subsumption_resolution,[],[f214,f51])).
% 2.23/0.68  fof(f51,plain,(
% 2.23/0.68    ~v2_struct_0(sK2)),
% 2.23/0.68    inference(cnf_transformation,[],[f45])).
% 2.23/0.68  fof(f214,plain,(
% 2.23/0.68    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v2_struct_0(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(X0),u1_struct_0(sK3),sK6,sK6)) ) | (spl7_1 | ~spl7_3)),
% 2.23/0.68    inference(duplicate_literal_removal,[],[f213])).
% 2.23/0.68  fof(f213,plain,(
% 2.23/0.68    ( ! [X0] : (~m1_pre_topc(X0,sK2) | v2_struct_0(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(X0),u1_struct_0(sK3),sK6,sK6) | ~l1_pre_topc(sK2)) ) | (spl7_1 | ~spl7_3)),
% 2.23/0.68    inference(resolution,[],[f206,f67])).
% 2.23/0.68  fof(f67,plain,(
% 2.23/0.68    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 2.23/0.68    inference(cnf_transformation,[],[f17])).
% 2.23/0.68  fof(f17,plain,(
% 2.23/0.68    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.23/0.68    inference(ennf_transformation,[],[f10])).
% 2.23/0.68  fof(f10,axiom,(
% 2.23/0.68    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.23/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 2.23/0.68  fof(f206,plain,(
% 2.23/0.68    ( ! [X0,X1] : (~m1_pre_topc(sK2,X1) | ~m1_pre_topc(X0,X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(X0),u1_struct_0(sK3),sK6,sK6)) ) | (spl7_1 | ~spl7_3)),
% 2.23/0.68    inference(subsumption_resolution,[],[f205,f63])).
% 2.23/0.68  fof(f63,plain,(
% 2.23/0.68    v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))),
% 2.23/0.68    inference(cnf_transformation,[],[f45])).
% 2.23/0.68  fof(f205,plain,(
% 2.23/0.68    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(X0),u1_struct_0(sK3),sK6,sK6) | ~m1_pre_topc(X0,X1) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(sK2,X1)) ) | (spl7_1 | ~spl7_3)),
% 2.23/0.68    inference(subsumption_resolution,[],[f204,f62])).
% 2.23/0.68  fof(f62,plain,(
% 2.23/0.68    v1_funct_1(sK6)),
% 2.23/0.68    inference(cnf_transformation,[],[f45])).
% 2.23/0.68  fof(f204,plain,(
% 2.23/0.68    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(X0),u1_struct_0(sK3),sK6,sK6) | ~m1_pre_topc(X0,X1) | ~v1_funct_1(sK6) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(sK2,X1)) ) | (spl7_1 | ~spl7_3)),
% 2.23/0.68    inference(subsumption_resolution,[],[f200,f144])).
% 2.23/0.68  fof(f144,plain,(
% 2.23/0.68    ~v1_xboole_0(u1_struct_0(sK3)) | spl7_1),
% 2.23/0.68    inference(avatar_component_clause,[],[f143])).
% 2.23/0.68  fof(f143,plain,(
% 2.23/0.68    spl7_1 <=> v1_xboole_0(u1_struct_0(sK3))),
% 2.23/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 2.23/0.68  fof(f200,plain,(
% 2.23/0.68    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(X0),u1_struct_0(sK3),sK6,sK6) | ~m1_pre_topc(X0,X1) | v1_xboole_0(u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(sK2,X1)) ) | ~spl7_3),
% 2.23/0.68    inference(resolution,[],[f169,f64])).
% 2.23/0.68  fof(f64,plain,(
% 2.23/0.68    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 2.23/0.68    inference(cnf_transformation,[],[f45])).
% 2.23/0.68  fof(f169,plain,(
% 2.23/0.68    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | r1_funct_2(X3,X4,u1_struct_0(X0),u1_struct_0(sK3),X2,X2) | ~m1_pre_topc(X0,X1) | v1_xboole_0(X4) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X3,X4) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(sK2,X1)) ) | ~spl7_3),
% 2.23/0.68    inference(avatar_component_clause,[],[f168])).
% 2.23/0.68  fof(f168,plain,(
% 2.23/0.68    spl7_3 <=> ! [X1,X3,X0,X2,X4] : (~m1_pre_topc(X0,X1) | r1_funct_2(X3,X4,u1_struct_0(X0),u1_struct_0(sK3),X2,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | v1_xboole_0(X4) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X3,X4) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(sK2,X1))),
% 2.23/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 2.23/0.68  fof(f1374,plain,(
% 2.23/0.68    ~r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(sK2),u1_struct_0(sK3),sK6,sK6) | ~spl7_46),
% 2.23/0.68    inference(backward_demodulation,[],[f86,f1098])).
% 2.23/0.68  fof(f1098,plain,(
% 2.23/0.68    sK6 = k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5)) | ~spl7_46),
% 2.23/0.68    inference(avatar_component_clause,[],[f1096])).
% 2.23/0.68  fof(f1096,plain,(
% 2.23/0.68    spl7_46 <=> sK6 = k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5))),
% 2.23/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).
% 2.23/0.68  fof(f86,plain,(
% 2.23/0.68    ~r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5)))),
% 2.23/0.68    inference(backward_demodulation,[],[f65,f61])).
% 2.23/0.68  fof(f61,plain,(
% 2.23/0.68    sK2 = k1_tsep_1(sK2,sK4,sK5)),
% 2.23/0.68    inference(cnf_transformation,[],[f45])).
% 2.23/0.68  fof(f65,plain,(
% 2.23/0.68    ~r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5)))),
% 2.23/0.68    inference(cnf_transformation,[],[f45])).
% 2.23/0.68  fof(f1354,plain,(
% 2.23/0.68    ~spl7_7 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_15 | ~spl7_16 | spl7_45),
% 2.23/0.68    inference(avatar_contradiction_clause,[],[f1353])).
% 2.23/0.68  fof(f1353,plain,(
% 2.23/0.68    $false | (~spl7_7 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_15 | ~spl7_16 | spl7_45)),
% 2.23/0.68    inference(subsumption_resolution,[],[f1352,f51])).
% 2.23/0.68  fof(f1352,plain,(
% 2.23/0.68    v2_struct_0(sK2) | (~spl7_7 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_15 | ~spl7_16 | spl7_45)),
% 2.23/0.68    inference(subsumption_resolution,[],[f1351,f52])).
% 2.23/0.68  fof(f1351,plain,(
% 2.23/0.68    ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl7_7 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_15 | ~spl7_16 | spl7_45)),
% 2.23/0.68    inference(subsumption_resolution,[],[f1350,f53])).
% 2.23/0.68  fof(f1350,plain,(
% 2.23/0.68    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl7_7 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_15 | ~spl7_16 | spl7_45)),
% 2.23/0.68    inference(subsumption_resolution,[],[f1349,f57])).
% 2.23/0.68  fof(f57,plain,(
% 2.23/0.68    ~v2_struct_0(sK4)),
% 2.23/0.68    inference(cnf_transformation,[],[f45])).
% 2.23/0.68  fof(f1349,plain,(
% 2.23/0.68    v2_struct_0(sK4) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl7_7 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_15 | ~spl7_16 | spl7_45)),
% 2.23/0.68    inference(subsumption_resolution,[],[f1348,f58])).
% 2.23/0.68  fof(f58,plain,(
% 2.23/0.68    m1_pre_topc(sK4,sK2)),
% 2.23/0.68    inference(cnf_transformation,[],[f45])).
% 2.23/0.68  fof(f1348,plain,(
% 2.23/0.68    ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl7_7 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_15 | ~spl7_16 | spl7_45)),
% 2.23/0.68    inference(subsumption_resolution,[],[f1347,f60])).
% 2.23/0.68  fof(f60,plain,(
% 2.23/0.68    m1_pre_topc(sK5,sK2)),
% 2.23/0.68    inference(cnf_transformation,[],[f45])).
% 2.23/0.68  fof(f1347,plain,(
% 2.23/0.68    ~m1_pre_topc(sK5,sK2) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl7_7 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_15 | ~spl7_16 | spl7_45)),
% 2.23/0.68    inference(subsumption_resolution,[],[f1346,f364])).
% 2.23/0.68  fof(f364,plain,(
% 2.23/0.68    v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4)) | ~spl7_7),
% 2.23/0.68    inference(avatar_component_clause,[],[f362])).
% 2.23/0.68  fof(f362,plain,(
% 2.23/0.68    spl7_7 <=> v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4))),
% 2.23/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 2.23/0.68  fof(f1346,plain,(
% 2.23/0.68    ~v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4)) | ~m1_pre_topc(sK5,sK2) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_15 | ~spl7_16 | spl7_45)),
% 2.23/0.68    inference(subsumption_resolution,[],[f1345,f442])).
% 2.23/0.68  fof(f442,plain,(
% 2.23/0.68    v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) | ~spl7_12),
% 2.23/0.68    inference(avatar_component_clause,[],[f440])).
% 2.23/0.68  fof(f440,plain,(
% 2.23/0.68    spl7_12 <=> v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3))),
% 2.23/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 2.23/0.68  fof(f1345,plain,(
% 2.23/0.68    ~v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4)) | ~m1_pre_topc(sK5,sK2) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl7_9 | ~spl7_13 | ~spl7_15 | ~spl7_16 | spl7_45)),
% 2.23/0.68    inference(subsumption_resolution,[],[f1339,f474])).
% 2.23/0.68  fof(f474,plain,(
% 2.23/0.68    m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~spl7_15),
% 2.23/0.68    inference(avatar_component_clause,[],[f472])).
% 2.23/0.68  fof(f472,plain,(
% 2.23/0.68    spl7_15 <=> m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))),
% 2.23/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 2.23/0.68  fof(f1339,plain,(
% 2.23/0.68    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4)) | ~m1_pre_topc(sK5,sK2) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl7_9 | ~spl7_13 | ~spl7_16 | spl7_45)),
% 2.23/0.68    inference(resolution,[],[f523,f1094])).
% 2.23/0.68  fof(f1094,plain,(
% 2.23/0.68    ~sP1(sK3,sK5,sK4,sK2,k2_tmap_1(sK2,sK3,sK6,sK5),k2_tmap_1(sK2,sK3,sK6,sK4)) | spl7_45),
% 2.23/0.68    inference(avatar_component_clause,[],[f1092])).
% 2.23/0.68  fof(f1092,plain,(
% 2.23/0.68    spl7_45 <=> sP1(sK3,sK5,sK4,sK2,k2_tmap_1(sK2,sK3,sK6,sK5),k2_tmap_1(sK2,sK3,sK6,sK4))),
% 2.23/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).
% 2.23/0.68  fof(f523,plain,(
% 2.23/0.68    ( ! [X2,X0,X1] : (sP1(sK3,sK5,X0,X1,k2_tmap_1(sK2,sK3,sK6,sK5),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(X2) | ~m1_pre_topc(sK5,X1) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | (~spl7_9 | ~spl7_13 | ~spl7_16)),
% 2.23/0.68    inference(subsumption_resolution,[],[f522,f54])).
% 2.23/0.68  fof(f54,plain,(
% 2.23/0.68    ~v2_struct_0(sK3)),
% 2.23/0.68    inference(cnf_transformation,[],[f45])).
% 2.23/0.68  fof(f522,plain,(
% 2.23/0.68    ( ! [X2,X0,X1] : (sP1(sK3,sK5,X0,X1,k2_tmap_1(sK2,sK3,sK6,sK5),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(X2) | ~m1_pre_topc(sK5,X1) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | (~spl7_9 | ~spl7_13 | ~spl7_16)),
% 2.23/0.68    inference(subsumption_resolution,[],[f521,f55])).
% 2.23/0.68  fof(f55,plain,(
% 2.23/0.68    v2_pre_topc(sK3)),
% 2.23/0.68    inference(cnf_transformation,[],[f45])).
% 2.23/0.68  fof(f521,plain,(
% 2.23/0.68    ( ! [X2,X0,X1] : (sP1(sK3,sK5,X0,X1,k2_tmap_1(sK2,sK3,sK6,sK5),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(X2) | ~m1_pre_topc(sK5,X1) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | (~spl7_9 | ~spl7_13 | ~spl7_16)),
% 2.23/0.68    inference(subsumption_resolution,[],[f520,f56])).
% 2.23/0.68  fof(f56,plain,(
% 2.23/0.68    l1_pre_topc(sK3)),
% 2.23/0.68    inference(cnf_transformation,[],[f45])).
% 2.23/0.68  fof(f520,plain,(
% 2.23/0.68    ( ! [X2,X0,X1] : (sP1(sK3,sK5,X0,X1,k2_tmap_1(sK2,sK3,sK6,sK5),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(X2) | ~m1_pre_topc(sK5,X1) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | (~spl7_9 | ~spl7_13 | ~spl7_16)),
% 2.23/0.68    inference(subsumption_resolution,[],[f519,f59])).
% 2.23/0.68  fof(f59,plain,(
% 2.23/0.68    ~v2_struct_0(sK5)),
% 2.23/0.68    inference(cnf_transformation,[],[f45])).
% 2.23/0.68  fof(f519,plain,(
% 2.23/0.68    ( ! [X2,X0,X1] : (sP1(sK3,sK5,X0,X1,k2_tmap_1(sK2,sK3,sK6,sK5),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(X2) | ~m1_pre_topc(sK5,X1) | v2_struct_0(sK5) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | (~spl7_9 | ~spl7_13 | ~spl7_16)),
% 2.23/0.68    inference(subsumption_resolution,[],[f518,f391])).
% 2.23/0.68  fof(f391,plain,(
% 2.23/0.68    v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK5)) | ~spl7_9),
% 2.23/0.68    inference(avatar_component_clause,[],[f389])).
% 2.23/0.68  fof(f389,plain,(
% 2.23/0.68    spl7_9 <=> v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK5))),
% 2.23/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 2.23/0.68  fof(f518,plain,(
% 2.23/0.68    ( ! [X2,X0,X1] : (sP1(sK3,sK5,X0,X1,k2_tmap_1(sK2,sK3,sK6,sK5),X2) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK5)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(X2) | ~m1_pre_topc(sK5,X1) | v2_struct_0(sK5) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | (~spl7_13 | ~spl7_16)),
% 2.23/0.68    inference(subsumption_resolution,[],[f510,f447])).
% 2.23/0.68  fof(f447,plain,(
% 2.23/0.68    v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~spl7_13),
% 2.23/0.68    inference(avatar_component_clause,[],[f445])).
% 2.23/0.68  fof(f445,plain,(
% 2.23/0.68    spl7_13 <=> v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3))),
% 2.23/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 2.23/0.68  fof(f510,plain,(
% 2.23/0.68    ( ! [X2,X0,X1] : (sP1(sK3,sK5,X0,X1,k2_tmap_1(sK2,sK3,sK6,sK5),X2) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK5)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(X2) | ~m1_pre_topc(sK5,X1) | v2_struct_0(sK5) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl7_16),
% 2.23/0.68    inference(resolution,[],[f508,f83])).
% 2.23/0.68  fof(f83,plain,(
% 2.23/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | sP1(X1,X3,X2,X0,X5,X4) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.23/0.68    inference(cnf_transformation,[],[f39])).
% 2.23/0.68  fof(f39,plain,(
% 2.23/0.68    ! [X0,X1,X2,X3,X4,X5] : (sP1(X1,X3,X2,X0,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.23/0.68    inference(definition_folding,[],[f35,f38])).
% 2.23/0.68  fof(f38,plain,(
% 2.23/0.68    ! [X1,X3,X2,X0,X5,X4] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~sP1(X1,X3,X2,X0,X5,X4))),
% 2.23/0.68    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.23/0.68  fof(f35,plain,(
% 2.23/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.23/0.68    inference(flattening,[],[f34])).
% 2.23/0.68  fof(f34,plain,(
% 2.23/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.23/0.68    inference(ennf_transformation,[],[f7])).
% 2.23/0.68  fof(f7,axiom,(
% 2.23/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 2.23/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_tmap_1)).
% 2.23/0.68  fof(f508,plain,(
% 2.23/0.68    m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~spl7_16),
% 2.23/0.68    inference(avatar_component_clause,[],[f506])).
% 2.23/0.68  fof(f506,plain,(
% 2.23/0.68    spl7_16 <=> m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))),
% 2.23/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 2.23/0.68  fof(f1099,plain,(
% 2.23/0.68    ~spl7_45 | spl7_46 | ~spl7_5),
% 2.23/0.68    inference(avatar_split_clause,[],[f916,f270,f1096,f1092])).
% 2.23/0.68  fof(f916,plain,(
% 2.23/0.68    sK6 = k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5)) | ~sP1(sK3,sK5,sK4,sK2,k2_tmap_1(sK2,sK3,sK6,sK5),k2_tmap_1(sK2,sK3,sK6,sK4)) | ~spl7_5),
% 2.23/0.68    inference(subsumption_resolution,[],[f915,f62])).
% 2.23/0.68  fof(f915,plain,(
% 2.23/0.68    sK6 = k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5)) | ~v1_funct_1(sK6) | ~sP1(sK3,sK5,sK4,sK2,k2_tmap_1(sK2,sK3,sK6,sK5),k2_tmap_1(sK2,sK3,sK6,sK4)) | ~spl7_5),
% 2.23/0.68    inference(subsumption_resolution,[],[f914,f63])).
% 2.23/0.68  fof(f914,plain,(
% 2.23/0.68    sK6 = k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5)) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~sP1(sK3,sK5,sK4,sK2,k2_tmap_1(sK2,sK3,sK6,sK5),k2_tmap_1(sK2,sK3,sK6,sK4)) | ~spl7_5),
% 2.23/0.68    inference(subsumption_resolution,[],[f913,f64])).
% 2.23/0.68  fof(f913,plain,(
% 2.23/0.68    sK6 = k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~sP1(sK3,sK5,sK4,sK2,k2_tmap_1(sK2,sK3,sK6,sK5),k2_tmap_1(sK2,sK3,sK6,sK4)) | ~spl7_5),
% 2.23/0.68    inference(resolution,[],[f891,f122])).
% 2.23/0.68  fof(f122,plain,(
% 2.23/0.68    ( ! [X14,X17,X15,X16] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X14),X15,k10_tmap_1(sK2,X14,sK4,sK5,X16,X17)) | k10_tmap_1(sK2,X14,sK4,sK5,X16,X17) = X15 | ~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X14)))) | ~v1_funct_2(X15,u1_struct_0(sK2),u1_struct_0(X14)) | ~v1_funct_1(X15) | ~sP1(X14,sK5,sK4,sK2,X17,X16)) )),
% 2.23/0.68    inference(subsumption_resolution,[],[f121,f80])).
% 2.23/0.68  fof(f80,plain,(
% 2.23/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4)) | ~sP1(X0,X1,X2,X3,X4,X5)) )),
% 2.23/0.68    inference(cnf_transformation,[],[f50])).
% 2.23/0.68  fof(f50,plain,(
% 2.23/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) & v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) & v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4))) | ~sP1(X0,X1,X2,X3,X4,X5))),
% 2.23/0.68    inference(rectify,[],[f49])).
% 2.23/0.68  fof(f49,plain,(
% 2.23/0.68    ! [X1,X3,X2,X0,X5,X4] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~sP1(X1,X3,X2,X0,X5,X4))),
% 2.23/0.68    inference(nnf_transformation,[],[f38])).
% 2.23/0.68  fof(f121,plain,(
% 2.23/0.68    ( ! [X14,X17,X15,X16] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X14),X15,k10_tmap_1(sK2,X14,sK4,sK5,X16,X17)) | k10_tmap_1(sK2,X14,sK4,sK5,X16,X17) = X15 | ~v1_funct_1(k10_tmap_1(sK2,X14,sK4,sK5,X16,X17)) | ~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X14)))) | ~v1_funct_2(X15,u1_struct_0(sK2),u1_struct_0(X14)) | ~v1_funct_1(X15) | ~sP1(X14,sK5,sK4,sK2,X17,X16)) )),
% 2.23/0.68    inference(subsumption_resolution,[],[f114,f102])).
% 2.23/0.68  fof(f102,plain,(
% 2.23/0.68    ( ! [X2,X0,X1] : (v1_funct_2(k10_tmap_1(sK2,X0,sK4,sK5,X1,X2),u1_struct_0(sK2),u1_struct_0(X0)) | ~sP1(X0,sK5,sK4,sK2,X2,X1)) )),
% 2.23/0.68    inference(superposition,[],[f81,f61])).
% 2.23/0.68  fof(f81,plain,(
% 2.23/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~sP1(X0,X1,X2,X3,X4,X5)) )),
% 2.23/0.68    inference(cnf_transformation,[],[f50])).
% 2.23/0.68  fof(f114,plain,(
% 2.23/0.68    ( ! [X14,X17,X15,X16] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X14),X15,k10_tmap_1(sK2,X14,sK4,sK5,X16,X17)) | k10_tmap_1(sK2,X14,sK4,sK5,X16,X17) = X15 | ~v1_funct_2(k10_tmap_1(sK2,X14,sK4,sK5,X16,X17),u1_struct_0(sK2),u1_struct_0(X14)) | ~v1_funct_1(k10_tmap_1(sK2,X14,sK4,sK5,X16,X17)) | ~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X14)))) | ~v1_funct_2(X15,u1_struct_0(sK2),u1_struct_0(X14)) | ~v1_funct_1(X15) | ~sP1(X14,sK5,sK4,sK2,X17,X16)) )),
% 2.23/0.68    inference(resolution,[],[f73,f104])).
% 2.23/0.68  fof(f104,plain,(
% 2.23/0.68    ( ! [X2,X0,X1] : (m1_subset_1(k10_tmap_1(sK2,X0,sK4,sK5,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~sP1(X0,sK5,sK4,sK2,X2,X1)) )),
% 2.23/0.68    inference(superposition,[],[f82,f61])).
% 2.23/0.68  fof(f82,plain,(
% 2.23/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~sP1(X0,X1,X2,X3,X4,X5)) )),
% 2.23/0.68    inference(cnf_transformation,[],[f50])).
% 2.23/0.68  fof(f73,plain,(
% 2.23/0.68    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_funct_2(X0,X1,X2,X3) | X2 = X3 | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.23/0.68    inference(cnf_transformation,[],[f46])).
% 2.23/0.68  fof(f46,plain,(
% 2.23/0.68    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.23/0.68    inference(nnf_transformation,[],[f29])).
% 2.23/0.68  fof(f29,plain,(
% 2.23/0.68    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.23/0.68    inference(flattening,[],[f28])).
% 2.23/0.68  fof(f28,plain,(
% 2.23/0.68    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.23/0.68    inference(ennf_transformation,[],[f1])).
% 2.23/0.68  fof(f1,axiom,(
% 2.23/0.68    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 2.23/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 2.23/0.68  fof(f891,plain,(
% 2.23/0.68    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5))) | ~spl7_5),
% 2.23/0.68    inference(forward_demodulation,[],[f890,f316])).
% 2.23/0.68  fof(f316,plain,(
% 2.23/0.68    k2_tmap_1(sK2,sK3,sK6,sK5) = k3_tmap_1(sK2,sK3,sK2,sK5,sK6) | ~spl7_5),
% 2.23/0.68    inference(forward_demodulation,[],[f312,f197])).
% 2.23/0.68  fof(f197,plain,(
% 2.23/0.68    k2_tmap_1(sK2,sK3,sK6,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(sK5))),
% 2.23/0.68    inference(resolution,[],[f186,f60])).
% 2.23/0.68  fof(f186,plain,(
% 2.23/0.68    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0))) )),
% 2.23/0.68    inference(subsumption_resolution,[],[f185,f51])).
% 2.23/0.68  fof(f185,plain,(
% 2.23/0.68    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) | v2_struct_0(sK2)) )),
% 2.23/0.68    inference(subsumption_resolution,[],[f184,f52])).
% 2.23/0.68  fof(f184,plain,(
% 2.23/0.68    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 2.23/0.68    inference(subsumption_resolution,[],[f183,f53])).
% 2.23/0.68  fof(f183,plain,(
% 2.23/0.68    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 2.23/0.68    inference(subsumption_resolution,[],[f182,f54])).
% 2.23/0.68  fof(f182,plain,(
% 2.23/0.68    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 2.23/0.68    inference(subsumption_resolution,[],[f181,f55])).
% 2.23/0.68  fof(f181,plain,(
% 2.23/0.68    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 2.23/0.68    inference(subsumption_resolution,[],[f180,f56])).
% 2.23/0.68  fof(f180,plain,(
% 2.23/0.68    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 2.23/0.68    inference(subsumption_resolution,[],[f179,f62])).
% 2.23/0.68  fof(f179,plain,(
% 2.23/0.68    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) | ~v1_funct_1(sK6) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 2.23/0.68    inference(subsumption_resolution,[],[f175,f63])).
% 2.23/0.68  fof(f175,plain,(
% 2.23/0.68    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 2.23/0.68    inference(resolution,[],[f71,f64])).
% 2.23/0.68  fof(f71,plain,(
% 2.23/0.68    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.23/0.68    inference(cnf_transformation,[],[f25])).
% 2.23/0.68  fof(f25,plain,(
% 2.23/0.68    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.23/0.68    inference(flattening,[],[f24])).
% 2.23/0.68  fof(f24,plain,(
% 2.23/0.68    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.23/0.68    inference(ennf_transformation,[],[f5])).
% 2.23/0.68  fof(f5,axiom,(
% 2.23/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 2.23/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 2.23/0.68  fof(f312,plain,(
% 2.23/0.68    k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(sK5)) = k3_tmap_1(sK2,sK3,sK2,sK5,sK6) | ~spl7_5),
% 2.23/0.68    inference(resolution,[],[f310,f60])).
% 2.23/0.68  fof(f310,plain,(
% 2.23/0.68    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(sK2,sK3,sK2,X0,sK6)) ) | ~spl7_5),
% 2.23/0.68    inference(subsumption_resolution,[],[f309,f51])).
% 2.23/0.68  fof(f309,plain,(
% 2.23/0.68    ( ! [X0] : (k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(sK2,sK3,sK2,X0,sK6) | ~m1_pre_topc(X0,sK2) | v2_struct_0(sK2)) ) | ~spl7_5),
% 2.23/0.68    inference(subsumption_resolution,[],[f308,f52])).
% 2.23/0.68  fof(f308,plain,(
% 2.23/0.68    ( ! [X0] : (k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(sK2,sK3,sK2,X0,sK6) | ~m1_pre_topc(X0,sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl7_5),
% 2.23/0.68    inference(subsumption_resolution,[],[f305,f53])).
% 2.23/0.68  fof(f305,plain,(
% 2.23/0.68    ( ! [X0] : (k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(sK2,sK3,sK2,X0,sK6) | ~m1_pre_topc(X0,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl7_5),
% 2.23/0.68    inference(resolution,[],[f286,f271])).
% 2.23/0.68  fof(f286,plain,(
% 2.23/0.68    ( ! [X0,X1] : (~m1_pre_topc(sK2,X1) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK6) | ~m1_pre_topc(X0,sK2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 2.23/0.68    inference(subsumption_resolution,[],[f285,f72])).
% 2.23/0.68  fof(f72,plain,(
% 2.23/0.68    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.23/0.68    inference(cnf_transformation,[],[f27])).
% 2.23/0.68  fof(f27,plain,(
% 2.23/0.68    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.23/0.68    inference(flattening,[],[f26])).
% 2.23/0.68  fof(f26,plain,(
% 2.23/0.68    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.23/0.68    inference(ennf_transformation,[],[f11])).
% 2.23/0.68  fof(f11,axiom,(
% 2.23/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.23/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).
% 2.23/0.68  fof(f285,plain,(
% 2.23/0.68    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK6) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 2.23/0.68    inference(subsumption_resolution,[],[f284,f54])).
% 2.23/0.68  fof(f284,plain,(
% 2.23/0.68    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK6) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 2.23/0.68    inference(subsumption_resolution,[],[f283,f55])).
% 2.23/0.68  fof(f283,plain,(
% 2.23/0.68    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK6) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 2.23/0.68    inference(subsumption_resolution,[],[f282,f56])).
% 2.23/0.68  fof(f282,plain,(
% 2.23/0.68    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK6) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 2.23/0.68    inference(subsumption_resolution,[],[f281,f62])).
% 2.23/0.68  fof(f281,plain,(
% 2.23/0.68    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK6) | ~v1_funct_1(sK6) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 2.23/0.68    inference(subsumption_resolution,[],[f277,f63])).
% 2.23/0.68  fof(f277,plain,(
% 2.23/0.68    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK6) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 2.23/0.68    inference(resolution,[],[f69,f64])).
% 2.23/0.68  fof(f69,plain,(
% 2.23/0.68    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.23/0.68    inference(cnf_transformation,[],[f21])).
% 2.23/0.68  fof(f21,plain,(
% 2.23/0.68    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.23/0.68    inference(flattening,[],[f20])).
% 2.23/0.68  fof(f20,plain,(
% 2.23/0.68    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.23/0.68    inference(ennf_transformation,[],[f6])).
% 2.23/0.68  fof(f6,axiom,(
% 2.23/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 2.23/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).
% 2.23/0.68  fof(f890,plain,(
% 2.23/0.68    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6))) | ~spl7_5),
% 2.23/0.68    inference(subsumption_resolution,[],[f889,f54])).
% 2.23/0.68  fof(f889,plain,(
% 2.23/0.68    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6))) | v2_struct_0(sK3) | ~spl7_5),
% 2.23/0.68    inference(subsumption_resolution,[],[f888,f55])).
% 2.23/0.68  fof(f888,plain,(
% 2.23/0.68    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6))) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~spl7_5),
% 2.23/0.68    inference(subsumption_resolution,[],[f887,f56])).
% 2.23/0.68  fof(f887,plain,(
% 2.23/0.68    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~spl7_5),
% 2.23/0.68    inference(subsumption_resolution,[],[f886,f62])).
% 2.23/0.68  fof(f886,plain,(
% 2.23/0.68    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6))) | ~v1_funct_1(sK6) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~spl7_5),
% 2.23/0.68    inference(subsumption_resolution,[],[f885,f63])).
% 2.23/0.68  fof(f885,plain,(
% 2.23/0.68    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6))) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~spl7_5),
% 2.23/0.68    inference(subsumption_resolution,[],[f880,f64])).
% 2.23/0.68  fof(f880,plain,(
% 2.23/0.68    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~spl7_5),
% 2.23/0.68    inference(superposition,[],[f619,f315])).
% 2.23/0.68  fof(f315,plain,(
% 2.23/0.68    k2_tmap_1(sK2,sK3,sK6,sK4) = k3_tmap_1(sK2,sK3,sK2,sK4,sK6) | ~spl7_5),
% 2.23/0.68    inference(forward_demodulation,[],[f311,f196])).
% 2.23/0.68  fof(f196,plain,(
% 2.23/0.68    k2_tmap_1(sK2,sK3,sK6,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(sK4))),
% 2.23/0.68    inference(resolution,[],[f186,f58])).
% 2.23/0.68  fof(f311,plain,(
% 2.23/0.68    k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(sK4)) = k3_tmap_1(sK2,sK3,sK2,sK4,sK6) | ~spl7_5),
% 2.23/0.68    inference(resolution,[],[f310,f58])).
% 2.23/0.68  fof(f619,plain,(
% 2.23/0.68    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.23/0.68    inference(subsumption_resolution,[],[f618,f51])).
% 2.23/0.68  fof(f618,plain,(
% 2.23/0.68    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(sK2)) )),
% 2.23/0.68    inference(subsumption_resolution,[],[f617,f52])).
% 2.23/0.68  fof(f617,plain,(
% 2.23/0.68    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 2.23/0.68    inference(subsumption_resolution,[],[f616,f53])).
% 2.23/0.68  fof(f616,plain,(
% 2.23/0.68    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 2.23/0.68    inference(subsumption_resolution,[],[f615,f57])).
% 2.23/0.68  fof(f615,plain,(
% 2.23/0.68    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | v2_struct_0(sK4) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 2.23/0.68    inference(subsumption_resolution,[],[f614,f58])).
% 2.23/0.68  fof(f614,plain,(
% 2.23/0.68    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 2.23/0.68    inference(subsumption_resolution,[],[f613,f59])).
% 2.23/0.68  fof(f613,plain,(
% 2.23/0.68    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 2.23/0.68    inference(subsumption_resolution,[],[f612,f60])).
% 2.23/0.68  fof(f612,plain,(
% 2.23/0.68    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 2.23/0.68    inference(superposition,[],[f70,f61])).
% 2.23/0.68  fof(f70,plain,(
% 2.23/0.68    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.23/0.68    inference(cnf_transformation,[],[f23])).
% 2.23/0.68  fof(f23,plain,(
% 2.23/0.68    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.23/0.68    inference(flattening,[],[f22])).
% 2.23/0.68  fof(f22,plain,(
% 2.23/0.68    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.23/0.68    inference(ennf_transformation,[],[f9])).
% 2.23/0.68  fof(f9,axiom,(
% 2.23/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))))))))),
% 2.23/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_tmap_1)).
% 2.23/0.68  fof(f509,plain,(
% 2.23/0.68    ~spl7_8 | spl7_16 | ~spl7_5),
% 2.23/0.68    inference(avatar_split_clause,[],[f338,f270,f506,f385])).
% 2.23/0.68  fof(f385,plain,(
% 2.23/0.68    spl7_8 <=> sP0(sK3,sK5,sK6,sK2,sK2)),
% 2.23/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 2.23/0.68  fof(f338,plain,(
% 2.23/0.68    m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~sP0(sK3,sK5,sK6,sK2,sK2) | ~spl7_5),
% 2.23/0.68    inference(superposition,[],[f77,f316])).
% 2.23/0.68  fof(f77,plain,(
% 2.23/0.68    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~sP0(X0,X1,X2,X3,X4)) )),
% 2.23/0.68    inference(cnf_transformation,[],[f48])).
% 2.23/0.68  fof(f48,plain,(
% 2.23/0.68    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2))) | ~sP0(X0,X1,X2,X3,X4))),
% 2.23/0.68    inference(rectify,[],[f47])).
% 2.23/0.68  fof(f47,plain,(
% 2.23/0.68    ! [X1,X3,X4,X2,X0] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~sP0(X1,X3,X4,X2,X0))),
% 2.23/0.68    inference(nnf_transformation,[],[f36])).
% 2.23/0.68  fof(f36,plain,(
% 2.23/0.68    ! [X1,X3,X4,X2,X0] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~sP0(X1,X3,X4,X2,X0))),
% 2.23/0.68    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.23/0.68  fof(f475,plain,(
% 2.23/0.68    ~spl7_6 | spl7_15 | ~spl7_5),
% 2.23/0.68    inference(avatar_split_clause,[],[f327,f270,f472,f358])).
% 2.23/0.68  fof(f358,plain,(
% 2.23/0.68    spl7_6 <=> sP0(sK3,sK4,sK6,sK2,sK2)),
% 2.23/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 2.23/0.68  fof(f327,plain,(
% 2.23/0.68    m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~sP0(sK3,sK4,sK6,sK2,sK2) | ~spl7_5),
% 2.23/0.68    inference(superposition,[],[f77,f315])).
% 2.23/0.68  fof(f448,plain,(
% 2.23/0.68    ~spl7_8 | spl7_13 | ~spl7_5),
% 2.23/0.68    inference(avatar_split_clause,[],[f339,f270,f445,f385])).
% 2.23/0.68  fof(f339,plain,(
% 2.23/0.68    v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~sP0(sK3,sK5,sK6,sK2,sK2) | ~spl7_5),
% 2.23/0.68    inference(superposition,[],[f76,f316])).
% 2.23/0.68  fof(f76,plain,(
% 2.23/0.68    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 2.23/0.68    inference(cnf_transformation,[],[f48])).
% 2.23/0.68  fof(f443,plain,(
% 2.23/0.68    ~spl7_6 | spl7_12 | ~spl7_5),
% 2.23/0.68    inference(avatar_split_clause,[],[f328,f270,f440,f358])).
% 2.23/0.68  fof(f328,plain,(
% 2.23/0.68    v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) | ~sP0(sK3,sK4,sK6,sK2,sK2) | ~spl7_5),
% 2.23/0.68    inference(superposition,[],[f76,f315])).
% 2.23/0.68  fof(f399,plain,(
% 2.23/0.68    ~spl7_5 | spl7_8),
% 2.23/0.68    inference(avatar_contradiction_clause,[],[f398])).
% 2.23/0.68  fof(f398,plain,(
% 2.23/0.68    $false | (~spl7_5 | spl7_8)),
% 2.23/0.68    inference(subsumption_resolution,[],[f397,f51])).
% 2.23/0.68  fof(f397,plain,(
% 2.23/0.68    v2_struct_0(sK2) | (~spl7_5 | spl7_8)),
% 2.23/0.68    inference(subsumption_resolution,[],[f396,f52])).
% 2.23/0.68  fof(f396,plain,(
% 2.23/0.68    ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl7_5 | spl7_8)),
% 2.23/0.68    inference(subsumption_resolution,[],[f395,f53])).
% 2.23/0.68  fof(f395,plain,(
% 2.23/0.68    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl7_5 | spl7_8)),
% 2.23/0.68    inference(subsumption_resolution,[],[f394,f271])).
% 2.23/0.68  fof(f394,plain,(
% 2.23/0.68    ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl7_8),
% 2.23/0.68    inference(subsumption_resolution,[],[f393,f60])).
% 2.23/0.68  fof(f393,plain,(
% 2.23/0.68    ~m1_pre_topc(sK5,sK2) | ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl7_8),
% 2.23/0.68    inference(resolution,[],[f387,f158])).
% 2.23/0.68  fof(f158,plain,(
% 2.23/0.68    ( ! [X0,X1] : (sP0(sK3,X0,sK6,sK2,X1) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 2.23/0.68    inference(subsumption_resolution,[],[f157,f54])).
% 2.23/0.68  fof(f157,plain,(
% 2.23/0.68    ( ! [X0,X1] : (sP0(sK3,X0,sK6,sK2,X1) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 2.23/0.68    inference(subsumption_resolution,[],[f156,f55])).
% 2.23/0.68  fof(f156,plain,(
% 2.23/0.68    ( ! [X0,X1] : (sP0(sK3,X0,sK6,sK2,X1) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 2.23/0.68    inference(subsumption_resolution,[],[f155,f56])).
% 2.23/0.68  fof(f155,plain,(
% 2.23/0.68    ( ! [X0,X1] : (sP0(sK3,X0,sK6,sK2,X1) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 2.23/0.68    inference(subsumption_resolution,[],[f154,f62])).
% 2.23/0.68  fof(f154,plain,(
% 2.23/0.68    ( ! [X0,X1] : (sP0(sK3,X0,sK6,sK2,X1) | ~v1_funct_1(sK6) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 2.23/0.68    inference(subsumption_resolution,[],[f150,f63])).
% 2.23/0.68  fof(f150,plain,(
% 2.23/0.68    ( ! [X0,X1] : (sP0(sK3,X0,sK6,sK2,X1) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 2.23/0.68    inference(resolution,[],[f78,f64])).
% 2.23/0.68  fof(f78,plain,(
% 2.23/0.68    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | sP0(X1,X3,X4,X2,X0) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.23/0.68    inference(cnf_transformation,[],[f37])).
% 2.23/0.68  fof(f37,plain,(
% 2.23/0.68    ! [X0,X1,X2,X3,X4] : (sP0(X1,X3,X4,X2,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.23/0.68    inference(definition_folding,[],[f31,f36])).
% 2.23/0.68  fof(f31,plain,(
% 2.23/0.68    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.23/0.68    inference(flattening,[],[f30])).
% 2.23/0.68  fof(f30,plain,(
% 2.23/0.68    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.23/0.68    inference(ennf_transformation,[],[f8])).
% 2.23/0.68  fof(f8,axiom,(
% 2.23/0.68    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 2.23/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).
% 2.23/0.68  fof(f387,plain,(
% 2.23/0.68    ~sP0(sK3,sK5,sK6,sK2,sK2) | spl7_8),
% 2.23/0.68    inference(avatar_component_clause,[],[f385])).
% 2.23/0.68  fof(f392,plain,(
% 2.23/0.68    ~spl7_8 | spl7_9 | ~spl7_5),
% 2.23/0.68    inference(avatar_split_clause,[],[f340,f270,f389,f385])).
% 2.23/0.68  fof(f340,plain,(
% 2.23/0.68    v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK5)) | ~sP0(sK3,sK5,sK6,sK2,sK2) | ~spl7_5),
% 2.23/0.68    inference(superposition,[],[f75,f316])).
% 2.23/0.68  fof(f75,plain,(
% 2.23/0.68    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 2.23/0.68    inference(cnf_transformation,[],[f48])).
% 2.23/0.68  fof(f372,plain,(
% 2.23/0.68    ~spl7_5 | spl7_6),
% 2.23/0.68    inference(avatar_contradiction_clause,[],[f371])).
% 2.23/0.68  fof(f371,plain,(
% 2.23/0.68    $false | (~spl7_5 | spl7_6)),
% 2.23/0.68    inference(subsumption_resolution,[],[f370,f51])).
% 2.23/0.68  fof(f370,plain,(
% 2.23/0.68    v2_struct_0(sK2) | (~spl7_5 | spl7_6)),
% 2.23/0.68    inference(subsumption_resolution,[],[f369,f52])).
% 2.23/0.68  fof(f369,plain,(
% 2.23/0.68    ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl7_5 | spl7_6)),
% 2.23/0.68    inference(subsumption_resolution,[],[f368,f53])).
% 2.23/0.68  fof(f368,plain,(
% 2.23/0.68    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl7_5 | spl7_6)),
% 2.23/0.68    inference(subsumption_resolution,[],[f367,f271])).
% 2.23/0.68  fof(f367,plain,(
% 2.23/0.68    ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl7_6),
% 2.23/0.68    inference(subsumption_resolution,[],[f366,f58])).
% 2.23/0.68  fof(f366,plain,(
% 2.23/0.68    ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl7_6),
% 2.23/0.68    inference(resolution,[],[f360,f158])).
% 2.23/0.68  fof(f360,plain,(
% 2.23/0.68    ~sP0(sK3,sK4,sK6,sK2,sK2) | spl7_6),
% 2.23/0.68    inference(avatar_component_clause,[],[f358])).
% 2.23/0.68  fof(f365,plain,(
% 2.23/0.68    ~spl7_6 | spl7_7 | ~spl7_5),
% 2.23/0.68    inference(avatar_split_clause,[],[f329,f270,f362,f358])).
% 2.23/0.68  fof(f329,plain,(
% 2.23/0.68    v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4)) | ~sP0(sK3,sK4,sK6,sK2,sK2) | ~spl7_5),
% 2.23/0.68    inference(superposition,[],[f75,f315])).
% 2.23/0.68  fof(f276,plain,(
% 2.23/0.68    spl7_5),
% 2.23/0.68    inference(avatar_contradiction_clause,[],[f275])).
% 2.23/0.68  fof(f275,plain,(
% 2.23/0.68    $false | spl7_5),
% 2.23/0.68    inference(subsumption_resolution,[],[f274,f53])).
% 2.23/0.68  fof(f274,plain,(
% 2.23/0.68    ~l1_pre_topc(sK2) | spl7_5),
% 2.23/0.68    inference(resolution,[],[f272,f67])).
% 2.23/0.68  fof(f272,plain,(
% 2.23/0.68    ~m1_pre_topc(sK2,sK2) | spl7_5),
% 2.23/0.68    inference(avatar_component_clause,[],[f270])).
% 2.23/0.68  fof(f174,plain,(
% 2.23/0.68    ~spl7_1),
% 2.23/0.68    inference(avatar_contradiction_clause,[],[f173])).
% 2.23/0.68  fof(f173,plain,(
% 2.23/0.68    $false | ~spl7_1),
% 2.23/0.68    inference(subsumption_resolution,[],[f172,f54])).
% 2.23/0.68  fof(f172,plain,(
% 2.23/0.68    v2_struct_0(sK3) | ~spl7_1),
% 2.23/0.68    inference(subsumption_resolution,[],[f171,f88])).
% 2.23/0.68  fof(f88,plain,(
% 2.23/0.68    l1_struct_0(sK3)),
% 2.23/0.68    inference(resolution,[],[f66,f56])).
% 2.23/0.68  fof(f66,plain,(
% 2.23/0.68    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 2.23/0.68    inference(cnf_transformation,[],[f16])).
% 2.23/0.68  fof(f16,plain,(
% 2.23/0.68    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.23/0.68    inference(ennf_transformation,[],[f2])).
% 2.23/0.68  fof(f2,axiom,(
% 2.23/0.68    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.23/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.23/0.68  fof(f171,plain,(
% 2.23/0.68    ~l1_struct_0(sK3) | v2_struct_0(sK3) | ~spl7_1),
% 2.23/0.68    inference(resolution,[],[f145,f68])).
% 2.23/0.68  fof(f68,plain,(
% 2.23/0.68    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.23/0.68    inference(cnf_transformation,[],[f19])).
% 2.23/0.68  fof(f19,plain,(
% 2.23/0.68    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.23/0.68    inference(flattening,[],[f18])).
% 2.23/0.68  fof(f18,plain,(
% 2.23/0.68    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.23/0.68    inference(ennf_transformation,[],[f3])).
% 2.23/0.68  fof(f3,axiom,(
% 2.23/0.68    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.23/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 2.23/0.68  fof(f145,plain,(
% 2.23/0.68    v1_xboole_0(u1_struct_0(sK3)) | ~spl7_1),
% 2.23/0.68    inference(avatar_component_clause,[],[f143])).
% 2.23/0.68  fof(f170,plain,(
% 2.23/0.68    spl7_1 | spl7_3),
% 2.23/0.68    inference(avatar_split_clause,[],[f165,f168,f143])).
% 2.23/0.68  fof(f165,plain,(
% 2.23/0.68    ( ! [X4,X2,X0,X3,X1] : (~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X2,X3,X4) | ~v1_funct_1(X2) | v1_xboole_0(u1_struct_0(sK3)) | v1_xboole_0(X4) | r1_funct_2(X3,X4,u1_struct_0(X0),u1_struct_0(sK3),X2,X2)) )),
% 2.23/0.68    inference(resolution,[],[f158,f137])).
% 2.23/0.68  fof(f137,plain,(
% 2.23/0.68    ( ! [X6,X4,X10,X8,X7,X5,X3,X9] : (~sP0(X6,X5,X10,X9,X8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X7,X3,X4) | ~v1_funct_1(X7) | v1_xboole_0(u1_struct_0(X6)) | v1_xboole_0(X4) | r1_funct_2(X3,X4,u1_struct_0(X5),u1_struct_0(X6),X7,X7)) )),
% 2.23/0.68    inference(subsumption_resolution,[],[f136,f75])).
% 2.23/0.68  fof(f136,plain,(
% 2.23/0.68    ( ! [X6,X4,X10,X8,X7,X5,X3,X9] : (r1_funct_2(X3,X4,u1_struct_0(X5),u1_struct_0(X6),X7,X7) | ~v1_funct_1(k3_tmap_1(X8,X6,X9,X5,X10)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X7,X3,X4) | ~v1_funct_1(X7) | v1_xboole_0(u1_struct_0(X6)) | v1_xboole_0(X4) | ~sP0(X6,X5,X10,X9,X8)) )),
% 2.23/0.68    inference(subsumption_resolution,[],[f131,f76])).
% 2.23/0.68  fof(f131,plain,(
% 2.23/0.68    ( ! [X6,X4,X10,X8,X7,X5,X3,X9] : (r1_funct_2(X3,X4,u1_struct_0(X5),u1_struct_0(X6),X7,X7) | ~v1_funct_2(k3_tmap_1(X8,X6,X9,X5,X10),u1_struct_0(X5),u1_struct_0(X6)) | ~v1_funct_1(k3_tmap_1(X8,X6,X9,X5,X10)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X7,X3,X4) | ~v1_funct_1(X7) | v1_xboole_0(u1_struct_0(X6)) | v1_xboole_0(X4) | ~sP0(X6,X5,X10,X9,X8)) )),
% 2.23/0.68    inference(resolution,[],[f79,f77])).
% 2.23/0.68  fof(f79,plain,(
% 2.23/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | r1_funct_2(X0,X1,X2,X3,X4,X4) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 2.23/0.68    inference(cnf_transformation,[],[f33])).
% 2.23/0.68  fof(f33,plain,(
% 2.23/0.68    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 2.23/0.68    inference(flattening,[],[f32])).
% 2.23/0.68  fof(f32,plain,(
% 2.23/0.68    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 2.23/0.68    inference(ennf_transformation,[],[f4])).
% 2.23/0.68  fof(f4,axiom,(
% 2.23/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => r1_funct_2(X0,X1,X2,X3,X4,X4))),
% 2.23/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r1_funct_2)).
% 2.23/0.68  % SZS output end Proof for theBenchmark
% 2.23/0.68  % (24262)------------------------------
% 2.23/0.68  % (24262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.23/0.68  % (24262)Termination reason: Refutation
% 2.23/0.68  
% 2.23/0.68  % (24262)Memory used [KB]: 12025
% 2.23/0.68  % (24262)Time elapsed: 0.204 s
% 2.23/0.68  % (24262)------------------------------
% 2.23/0.68  % (24262)------------------------------
% 2.23/0.68  % (24236)Success in time 0.316 s
%------------------------------------------------------------------------------
