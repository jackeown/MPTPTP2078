%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:18 EST 2020

% Result     : Theorem 1.92s
% Output     : Refutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :  281 (1733 expanded)
%              Number of leaves         :   35 ( 623 expanded)
%              Depth                    :   35
%              Number of atoms          : 1655 (17739 expanded)
%              Number of equality atoms :  137 (1572 expanded)
%              Maximal formula depth    :   22 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1526,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f179,f183,f208,f363,f371,f379,f384,f1175,f1305,f1308,f1521])).

fof(f1521,plain,
    ( spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | spl7_38
    | ~ spl7_41 ),
    inference(avatar_contradiction_clause,[],[f1520])).

fof(f1520,plain,
    ( $false
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | spl7_38
    | ~ spl7_41 ),
    inference(subsumption_resolution,[],[f1519,f1367])).

fof(f1367,plain,
    ( sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) != k1_funct_1(k4_tmap_1(sK3,sK4),sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | spl7_38
    | ~ spl7_41 ),
    inference(subsumption_resolution,[],[f1366,f1347])).

fof(f1347,plain,
    ( sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | spl7_38
    | ~ spl7_41 ),
    inference(subsumption_resolution,[],[f1346,f1135])).

fof(f1135,plain,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,k4_tmap_1(sK3,sK4))
    | spl7_38 ),
    inference(avatar_component_clause,[],[f1134])).

fof(f1134,plain,
    ( spl7_38
  <=> r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,k4_tmap_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f1346,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,k4_tmap_1(sK3,sK4))
    | sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_41 ),
    inference(subsumption_resolution,[],[f1345,f378])).

fof(f378,plain,
    ( v1_funct_2(k4_tmap_1(sK3,sK4),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f376])).

fof(f376,plain,
    ( spl7_10
  <=> v1_funct_2(k4_tmap_1(sK3,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f1345,plain,
    ( ~ v1_funct_2(k4_tmap_1(sK3,sK4),u1_struct_0(sK4),u1_struct_0(sK3))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,k4_tmap_1(sK3,sK4))
    | sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_41 ),
    inference(subsumption_resolution,[],[f1340,f362])).

fof(f362,plain,
    ( v1_funct_1(k4_tmap_1(sK3,sK4))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f360])).

fof(f360,plain,
    ( spl7_9
  <=> v1_funct_1(k4_tmap_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f1340,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK3,sK4))
    | ~ v1_funct_2(k4_tmap_1(sK3,sK4),u1_struct_0(sK4),u1_struct_0(sK3))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,k4_tmap_1(sK3,sK4))
    | sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)
    | ~ spl7_11
    | ~ spl7_41 ),
    inference(resolution,[],[f1304,f383])).

fof(f383,plain,
    ( m1_subset_1(k4_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f381])).

fof(f381,plain,
    ( spl7_11
  <=> m1_subset_1(k4_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f1304,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3))
        | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0)
        | sP0(X0,sK5,sK3,sK4,sK4) )
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f1303])).

fof(f1303,plain,
    ( spl7_41
  <=> ! [X0] :
        ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
        | sP0(X0,sK5,sK3,sK4,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f1366,plain,
    ( sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) != k1_funct_1(k4_tmap_1(sK3,sK4),sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4))
    | ~ sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | spl7_38
    | ~ spl7_41 ),
    inference(superposition,[],[f89,f1358])).

fof(f1358,plain,
    ( sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | spl7_38
    | ~ spl7_41 ),
    inference(forward_demodulation,[],[f1351,f1350])).

fof(f1350,plain,
    ( sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k1_funct_1(sK5,sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4))
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | spl7_38
    | ~ spl7_41 ),
    inference(resolution,[],[f1347,f214])).

fof(f214,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ sP0(X0,X1,X2,sK4,X3)
        | sK6(X0,X1,X2,sK4,X3) = k1_funct_1(sK5,sK6(X0,X1,X2,sK4,X3)) )
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f213,f71])).

fof(f71,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k4_tmap_1(sK3,sK4),sK5)
    & ! [X3] :
        ( k1_funct_1(sK5,X3) = X3
        | ~ r2_hidden(X3,u1_struct_0(sK4))
        | ~ m1_subset_1(X3,u1_struct_0(sK3)) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3))
    & v1_funct_1(sK5)
    & m1_pre_topc(sK4,sK3)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f21,f61,f60,f59])).

fof(f59,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
                & ! [X3] :
                    ( k1_funct_1(X2,X3) = X3
                    | ~ r2_hidden(X3,u1_struct_0(X1))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(sK3),k4_tmap_1(sK3,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(sK3)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,sK3)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(sK3),k4_tmap_1(sK3,X1),X2)
            & ! [X3] :
                ( k1_funct_1(X2,X3) = X3
                | ~ r2_hidden(X3,u1_struct_0(X1))
                | ~ m1_subset_1(X3,u1_struct_0(sK3)) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
            & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3))
            & v1_funct_1(X2) )
        & m1_pre_topc(X1,sK3)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k4_tmap_1(sK3,sK4),X2)
          & ! [X3] :
              ( k1_funct_1(X2,X3) = X3
              | ~ r2_hidden(X3,u1_struct_0(sK4))
              | ~ m1_subset_1(X3,u1_struct_0(sK3)) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
          & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(sK3))
          & v1_funct_1(X2) )
      & m1_pre_topc(sK4,sK3)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ? [X2] :
        ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k4_tmap_1(sK3,sK4),X2)
        & ! [X3] :
            ( k1_funct_1(X2,X3) = X3
            | ~ r2_hidden(X3,u1_struct_0(sK4))
            | ~ m1_subset_1(X3,u1_struct_0(sK3)) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
        & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(sK3))
        & v1_funct_1(X2) )
   => ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k4_tmap_1(sK3,sK4),sK5)
      & ! [X3] :
          ( k1_funct_1(sK5,X3) = X3
          | ~ r2_hidden(X3,u1_struct_0(sK4))
          | ~ m1_subset_1(X3,u1_struct_0(sK3)) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
      & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X2) )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_hidden(X3,u1_struct_0(X1))
                       => k1_funct_1(X2,X3) = X3 ) )
                 => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,u1_struct_0(X1))
                     => k1_funct_1(X2,X3) = X3 ) )
               => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_tmap_1)).

fof(f213,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ sP0(X0,X1,X2,sK4,X3)
        | sK6(X0,X1,X2,sK4,X3) = k1_funct_1(sK5,sK6(X0,X1,X2,sK4,X3))
        | v2_struct_0(sK3) )
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f212,f73])).

fof(f73,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f212,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ sP0(X0,X1,X2,sK4,X3)
        | sK6(X0,X1,X2,sK4,X3) = k1_funct_1(sK5,sK6(X0,X1,X2,sK4,X3))
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f211,f74])).

fof(f74,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f211,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ sP0(X0,X1,X2,sK4,X3)
        | sK6(X0,X1,X2,sK4,X3) = k1_funct_1(sK5,sK6(X0,X1,X2,sK4,X3))
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f210,f75])).

fof(f75,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f210,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ sP0(X0,X1,X2,sK4,X3)
        | sK6(X0,X1,X2,sK4,X3) = k1_funct_1(sK5,sK6(X0,X1,X2,sK4,X3))
        | ~ m1_pre_topc(sK4,sK3)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl7_5 ),
    inference(duplicate_literal_removal,[],[f209])).

fof(f209,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ sP0(X0,X1,X2,sK4,X3)
        | sK6(X0,X1,X2,sK4,X3) = k1_funct_1(sK5,sK6(X0,X1,X2,sK4,X3))
        | ~ m1_pre_topc(sK4,sK3)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ sP0(X0,X1,X2,sK4,X3) )
    | ~ spl7_5 ),
    inference(resolution,[],[f207,f144])).

fof(f144,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3,X4),u1_struct_0(X5))
      | ~ m1_pre_topc(X3,X5)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(resolution,[],[f93,f87])).

fof(f87,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3,X4),u1_struct_0(X3))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X2),X1,sK6(X0,X1,X2,X3,X4)) != k1_funct_1(X0,sK6(X0,X1,X2,X3,X4))
        & r2_hidden(sK6(X0,X1,X2,X3,X4),u1_struct_0(X4))
        & m1_subset_1(sK6(X0,X1,X2,X3,X4),u1_struct_0(X3)) )
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f64,f65])).

fof(f65,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X2),X1,X5) != k1_funct_1(X0,X5)
          & r2_hidden(X5,u1_struct_0(X4))
          & m1_subset_1(X5,u1_struct_0(X3)) )
     => ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X2),X1,sK6(X0,X1,X2,X3,X4)) != k1_funct_1(X0,sK6(X0,X1,X2,X3,X4))
        & r2_hidden(sK6(X0,X1,X2,X3,X4),u1_struct_0(X4))
        & m1_subset_1(sK6(X0,X1,X2,X3,X4),u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ? [X5] :
          ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X2),X1,X5) != k1_funct_1(X0,X5)
          & r2_hidden(X5,u1_struct_0(X4))
          & m1_subset_1(X5,u1_struct_0(X3)) )
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f63])).

fof(f63,plain,(
    ! [X4,X3,X0,X1,X2] :
      ( ? [X5] :
          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
          & r2_hidden(X5,u1_struct_0(X2))
          & m1_subset_1(X5,u1_struct_0(X1)) )
      | ~ sP0(X4,X3,X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X4,X3,X0,X1,X2] :
      ( ? [X5] :
          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
          & r2_hidden(X5,u1_struct_0(X2))
          & m1_subset_1(X5,u1_struct_0(X1)) )
      | ~ sP0(X4,X3,X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f207,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK6(X0,X1,X2,sK4,X3),u1_struct_0(sK3))
        | ~ sP0(X0,X1,X2,sK4,X3)
        | sK6(X0,X1,X2,sK4,X3) = k1_funct_1(sK5,sK6(X0,X1,X2,sK4,X3)) )
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl7_5
  <=> ! [X1,X3,X0,X2] :
        ( ~ sP0(X0,X1,X2,sK4,X3)
        | ~ m1_subset_1(sK6(X0,X1,X2,sK4,X3),u1_struct_0(sK3))
        | sK6(X0,X1,X2,sK4,X3) = k1_funct_1(sK5,sK6(X0,X1,X2,sK4,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f1351,plain,
    ( k1_funct_1(sK5,sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4))
    | ~ spl7_4
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | spl7_38
    | ~ spl7_41 ),
    inference(resolution,[],[f1347,f184])).

fof(f184,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ sP0(X0,X1,X2,sK4,X3)
        | k1_funct_1(sK5,sK6(X0,X1,X2,sK4,X3)) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK6(X0,X1,X2,sK4,X3)) )
    | ~ spl7_4 ),
    inference(resolution,[],[f178,f87])).

fof(f178,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK4))
        | k1_funct_1(sK5,X0) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) )
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl7_4
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK4))
        | k1_funct_1(sK5,X0) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f89,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X2),X1,sK6(X0,X1,X2,X3,X4)) != k1_funct_1(X0,sK6(X0,X1,X2,X3,X4))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f1519,plain,
    ( sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k1_funct_1(k4_tmap_1(sK3,sK4),sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4))
    | spl7_3
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | spl7_38
    | ~ spl7_41 ),
    inference(subsumption_resolution,[],[f1518,f71])).

fof(f1518,plain,
    ( v2_struct_0(sK3)
    | sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k1_funct_1(k4_tmap_1(sK3,sK4),sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4))
    | spl7_3
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | spl7_38
    | ~ spl7_41 ),
    inference(subsumption_resolution,[],[f1517,f72])).

fof(f72,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f1517,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k1_funct_1(k4_tmap_1(sK3,sK4),sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4))
    | spl7_3
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | spl7_38
    | ~ spl7_41 ),
    inference(subsumption_resolution,[],[f1513,f73])).

fof(f1513,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k1_funct_1(k4_tmap_1(sK3,sK4),sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4))
    | spl7_3
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | spl7_38
    | ~ spl7_41 ),
    inference(resolution,[],[f1361,f75])).

fof(f1361,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK4,X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k1_funct_1(k4_tmap_1(X1,sK4),sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)) )
    | spl7_3
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | spl7_38
    | ~ spl7_41 ),
    inference(subsumption_resolution,[],[f1360,f174])).

fof(f174,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | spl7_3 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl7_3
  <=> v1_xboole_0(u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f1360,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK4,X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | v1_xboole_0(u1_struct_0(sK4))
        | sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k1_funct_1(k4_tmap_1(X1,sK4),sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)) )
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | spl7_38
    | ~ spl7_41 ),
    inference(subsumption_resolution,[],[f1354,f74])).

fof(f1354,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(sK4,X1)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | v1_xboole_0(u1_struct_0(sK4))
        | sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k1_funct_1(k4_tmap_1(X1,sK4),sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)) )
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | spl7_38
    | ~ spl7_41 ),
    inference(resolution,[],[f1347,f162])).

fof(f162,plain,(
    ! [X6,X10,X8,X7,X11,X9] :
      ( ~ sP0(X8,X9,X10,X7,X11)
      | ~ m1_pre_topc(X7,X6)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | v1_xboole_0(u1_struct_0(X7))
      | sK6(X8,X9,X10,X7,X11) = k1_funct_1(k4_tmap_1(X6,X7),sK6(X8,X9,X10,X7,X11)) ) ),
    inference(subsumption_resolution,[],[f161,f144])).

fof(f161,plain,(
    ! [X6,X10,X8,X7,X11,X9] :
      ( sK6(X8,X9,X10,X7,X11) = k1_funct_1(k4_tmap_1(X6,X7),sK6(X8,X9,X10,X7,X11))
      | ~ m1_subset_1(sK6(X8,X9,X10,X7,X11),u1_struct_0(X6))
      | ~ m1_pre_topc(X7,X6)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | v1_xboole_0(u1_struct_0(X7))
      | ~ sP0(X8,X9,X10,X7,X11) ) ),
    inference(resolution,[],[f92,f142])).

fof(f142,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK6(X0,X1,X2,X3,X4),u1_struct_0(X3))
      | v1_xboole_0(u1_struct_0(X3))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(resolution,[],[f87,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,u1_struct_0(X1))
      | k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
              | ~ r2_hidden(X2,u1_struct_0(X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
              | ~ r2_hidden(X2,u1_struct_0(X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,u1_struct_0(X1))
               => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_tmap_1)).

fof(f1308,plain,(
    spl7_40 ),
    inference(avatar_contradiction_clause,[],[f1307])).

fof(f1307,plain,
    ( $false
    | spl7_40 ),
    inference(subsumption_resolution,[],[f1306,f114])).

fof(f114,plain,(
    l1_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f111,f73])).

fof(f111,plain,
    ( l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f83,f75])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f1306,plain,
    ( ~ l1_pre_topc(sK4)
    | spl7_40 ),
    inference(resolution,[],[f1301,f82])).

fof(f82,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f1301,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | spl7_40 ),
    inference(avatar_component_clause,[],[f1299])).

fof(f1299,plain,
    ( spl7_40
  <=> m1_pre_topc(sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f1305,plain,
    ( ~ spl7_40
    | spl7_41 ),
    inference(avatar_split_clause,[],[f731,f1303,f1299])).

fof(f731,plain,(
    ! [X0] :
      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0)
      | sP0(X0,sK5,sK3,sK4,sK4)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
      | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK4,sK4) ) ),
    inference(subsumption_resolution,[],[f730,f71])).

fof(f730,plain,(
    ! [X0] :
      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0)
      | sP0(X0,sK5,sK3,sK4,sK4)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
      | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK4,sK4)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f729,f72])).

fof(f729,plain,(
    ! [X0] :
      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0)
      | sP0(X0,sK5,sK3,sK4,sK4)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
      | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK4,sK4)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f728,f73])).

fof(f728,plain,(
    ! [X0] :
      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0)
      | sP0(X0,sK5,sK3,sK4,sK4)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
      | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK4,sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f727,f121])).

fof(f121,plain,(
    v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f120,f72])).

fof(f120,plain,
    ( v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f117,f73])).

fof(f117,plain,
    ( v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(resolution,[],[f94,f75])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f727,plain,(
    ! [X0] :
      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0)
      | sP0(X0,sK5,sK3,sK4,sK4)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
      | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK4,sK4)
      | ~ v2_pre_topc(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f726,f114])).

fof(f726,plain,(
    ! [X0] :
      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0)
      | sP0(X0,sK5,sK3,sK4,sK4)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
      | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK4,sK4)
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f725,f74])).

fof(f725,plain,(
    ! [X0] :
      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0)
      | sP0(X0,sK5,sK3,sK4,sK4)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
      | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK4,sK4)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f724,f76])).

fof(f76,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f62])).

fof(f724,plain,(
    ! [X0] :
      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0)
      | sP0(X0,sK5,sK3,sK4,sK4)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
      | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_1(sK5)
      | ~ m1_pre_topc(sK4,sK4)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f723,f77])).

fof(f77,plain,(
    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f62])).

fof(f723,plain,(
    ! [X0] :
      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0)
      | sP0(X0,sK5,sK3,sK4,sK4)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
      | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(sK5)
      | ~ m1_pre_topc(sK4,sK4)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f722,f78])).

fof(f78,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f62])).

fof(f722,plain,(
    ! [X0] :
      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0)
      | sP0(X0,sK5,sK3,sK4,sK4)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
      | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
      | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(sK5)
      | ~ m1_pre_topc(sK4,sK4)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(duplicate_literal_removal,[],[f721])).

fof(f721,plain,(
    ! [X0] :
      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0)
      | sP0(X0,sK5,sK3,sK4,sK4)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
      | ~ v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
      | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(sK5)
      | ~ m1_pre_topc(sK4,sK4)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(superposition,[],[f90,f719])).

fof(f719,plain,(
    sK5 = k2_tmap_1(sK4,sK3,sK5,sK4) ),
    inference(forward_demodulation,[],[f718,f287])).

fof(f287,plain,(
    sK5 = k3_tmap_1(sK3,sK3,sK4,sK4,sK5) ),
    inference(subsumption_resolution,[],[f286,f71])).

fof(f286,plain,
    ( sK5 = k3_tmap_1(sK3,sK3,sK4,sK4,sK5)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f285,f72])).

fof(f285,plain,
    ( sK5 = k3_tmap_1(sK3,sK3,sK4,sK4,sK5)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f282,f73])).

fof(f282,plain,
    ( sK5 = k3_tmap_1(sK3,sK3,sK4,sK4,sK5)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f277,f75])).

fof(f277,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK4,X0)
      | sK5 = k3_tmap_1(X0,sK3,sK4,sK4,sK5)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f276,f71])).

fof(f276,plain,(
    ! [X0] :
      ( sK5 = k3_tmap_1(X0,sK3,sK4,sK4,sK5)
      | ~ m1_pre_topc(sK4,X0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f275,f72])).

fof(f275,plain,(
    ! [X0] :
      ( sK5 = k3_tmap_1(X0,sK3,sK4,sK4,sK5)
      | ~ m1_pre_topc(sK4,X0)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f274,f73])).

fof(f274,plain,(
    ! [X0] :
      ( sK5 = k3_tmap_1(X0,sK3,sK4,sK4,sK5)
      | ~ m1_pre_topc(sK4,X0)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f273,f74])).

fof(f273,plain,(
    ! [X0] :
      ( sK5 = k3_tmap_1(X0,sK3,sK4,sK4,sK5)
      | ~ m1_pre_topc(sK4,X0)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f272,f76])).

fof(f272,plain,(
    ! [X0] :
      ( sK5 = k3_tmap_1(X0,sK3,sK4,sK4,sK5)
      | ~ v1_funct_1(sK5)
      | ~ m1_pre_topc(sK4,X0)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f269,f77])).

fof(f269,plain,(
    ! [X0] :
      ( sK5 = k3_tmap_1(X0,sK3,sK4,sK4,sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(sK5)
      | ~ m1_pre_topc(sK4,X0)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f268,f78])).

fof(f268,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | k3_tmap_1(X0,X1,X2,X2,X3) = X3
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f267,f107])).

fof(f107,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | sP2(X1,X3,X4,X2,X0)
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
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( sP2(X1,X3,X4,X2,X0)
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
    inference(definition_folding,[],[f52,f57])).

fof(f57,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ sP2(X1,X3,X4,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f51,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f267,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_tmap_1(X0,X1,X2,X2,X3) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ sP2(X1,X2,X3,X2,X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f264])).

fof(f264,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_tmap_1(X0,X1,X2,X2,X3) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ sP2(X1,X2,X3,X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f238,f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tmap_1)).

fof(f238,plain,(
    ! [X6,X4,X8,X7,X5,X9] :
      ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X5),X6,k3_tmap_1(X7,X5,X8,X4,X9))
      | k3_tmap_1(X7,X5,X8,X4,X9) = X6
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))
      | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X5))
      | ~ v1_funct_1(X6)
      | ~ sP2(X5,X4,X9,X8,X7) ) ),
    inference(subsumption_resolution,[],[f237,f104])).

fof(f104,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2))
      | ~ sP2(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2)) )
      | ~ sP2(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f69])).

fof(f69,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ sP2(X1,X3,X4,X2,X0) ) ),
    inference(nnf_transformation,[],[f57])).

fof(f237,plain,(
    ! [X6,X4,X8,X7,X5,X9] :
      ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X5),X6,k3_tmap_1(X7,X5,X8,X4,X9))
      | k3_tmap_1(X7,X5,X8,X4,X9) = X6
      | ~ v1_funct_1(k3_tmap_1(X7,X5,X8,X4,X9))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))
      | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X5))
      | ~ v1_funct_1(X6)
      | ~ sP2(X5,X4,X9,X8,X7) ) ),
    inference(subsumption_resolution,[],[f232,f105])).

fof(f105,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP2(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f232,plain,(
    ! [X6,X4,X8,X7,X5,X9] :
      ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X5),X6,k3_tmap_1(X7,X5,X8,X4,X9))
      | k3_tmap_1(X7,X5,X8,X4,X9) = X6
      | ~ v1_funct_2(k3_tmap_1(X7,X5,X8,X4,X9),u1_struct_0(X4),u1_struct_0(X5))
      | ~ v1_funct_1(k3_tmap_1(X7,X5,X8,X4,X9))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))
      | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X5))
      | ~ v1_funct_1(X6)
      | ~ sP2(X5,X4,X9,X8,X7) ) ),
    inference(resolution,[],[f102,f106])).

fof(f106,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP2(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f70])).

% (21259)Refutation not found, incomplete strategy% (21259)------------------------------
% (21259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (21259)Termination reason: Refutation not found, incomplete strategy

% (21259)Memory used [KB]: 6140
% (21259)Time elapsed: 0.214 s
% (21259)------------------------------
% (21259)------------------------------
fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
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
    inference(nnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f718,plain,(
    k3_tmap_1(sK3,sK3,sK4,sK4,sK5) = k2_tmap_1(sK4,sK3,sK5,sK4) ),
    inference(forward_demodulation,[],[f717,f482])).

fof(f482,plain,(
    k2_tmap_1(sK4,sK3,sK5,sK4) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4)) ),
    inference(subsumption_resolution,[],[f481,f114])).

fof(f481,plain,
    ( k2_tmap_1(sK4,sK3,sK5,sK4) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4) ),
    inference(resolution,[],[f437,f82])).

fof(f437,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK4)
      | k2_tmap_1(sK4,sK3,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f436,f74])).

fof(f436,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK4)
      | k2_tmap_1(sK4,sK3,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0))
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f435,f121])).

fof(f435,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK4)
      | k2_tmap_1(sK4,sK3,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0))
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f434,f114])).

fof(f434,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK4)
      | k2_tmap_1(sK4,sK3,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0))
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f433,f71])).

fof(f433,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK4)
      | k2_tmap_1(sK4,sK3,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0))
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f432,f72])).

fof(f432,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK4)
      | k2_tmap_1(sK4,sK3,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0))
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f431,f73])).

fof(f431,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK4)
      | k2_tmap_1(sK4,sK3,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0))
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f430,f76])).

fof(f430,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK4)
      | k2_tmap_1(sK4,sK3,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0))
      | ~ v1_funct_1(sK5)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f426,f77])).

fof(f426,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK4)
      | k2_tmap_1(sK4,sK3,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0))
      | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(sK5)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4) ) ),
    inference(resolution,[],[f91,f78])).

fof(f91,plain,(
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f717,plain,(
    k3_tmap_1(sK3,sK3,sK4,sK4,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4)) ),
    inference(subsumption_resolution,[],[f716,f114])).

fof(f716,plain,
    ( k3_tmap_1(sK3,sK3,sK4,sK4,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4) ),
    inference(resolution,[],[f704,f82])).

fof(f704,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK4)
      | k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0)) = k3_tmap_1(sK3,sK3,sK4,X0,sK5) ) ),
    inference(subsumption_resolution,[],[f703,f71])).

fof(f703,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0)) = k3_tmap_1(sK3,sK3,sK4,X0,sK5)
      | ~ m1_pre_topc(X0,sK4)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f702,f72])).

fof(f702,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0)) = k3_tmap_1(sK3,sK3,sK4,X0,sK5)
      | ~ m1_pre_topc(X0,sK4)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f699,f73])).

fof(f699,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0)) = k3_tmap_1(sK3,sK3,sK4,X0,sK5)
      | ~ m1_pre_topc(X0,sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f595,f75])).

fof(f595,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK4,X1)
      | k3_tmap_1(X1,sK3,sK4,X0,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK4)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f594,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f594,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK4)
      | k3_tmap_1(X1,sK3,sK4,X0,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK4,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f593,f71])).

fof(f593,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK4)
      | k3_tmap_1(X1,sK3,sK4,X0,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK4,X1)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f592,f72])).

fof(f592,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK4)
      | k3_tmap_1(X1,sK3,sK4,X0,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK4,X1)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f591,f73])).

fof(f591,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK4)
      | k3_tmap_1(X1,sK3,sK4,X0,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK4,X1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f590,f76])).

fof(f590,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK4)
      | k3_tmap_1(X1,sK3,sK4,X0,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0))
      | ~ v1_funct_1(sK5)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK4,X1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f585,f77])).

fof(f585,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK4)
      | k3_tmap_1(X1,sK3,sK4,X0,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0))
      | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(sK5)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK4,X1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f85,f78])).

fof(f85,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f90,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
      | sP0(X4,X3,X0,X1,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X2,X1)
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
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | sP0(X4,X3,X0,X1,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f32,f53])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | ? [X5] :
                          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X1)
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
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | ? [X5] :
                          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X1)
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
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( r2_hidden(X5,u1_struct_0(X2))
                             => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5) ) )
                       => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_tmap_1)).

fof(f1175,plain,(
    ~ spl7_38 ),
    inference(avatar_contradiction_clause,[],[f1174])).

fof(f1174,plain,
    ( $false
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f1148,f148])).

fof(f148,plain,(
    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK5) ),
    inference(subsumption_resolution,[],[f147,f76])).

fof(f147,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK5)
    | ~ v1_funct_1(sK5) ),
    inference(subsumption_resolution,[],[f145,f77])).

fof(f145,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK5) ),
    inference(resolution,[],[f109,f78])).

fof(f109,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f108])).

fof(f108,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f1148,plain,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK5)
    | ~ spl7_38 ),
    inference(backward_demodulation,[],[f80,f1147])).

fof(f1147,plain,
    ( k4_tmap_1(sK3,sK4) = sK5
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f1146,f127])).

fof(f127,plain,(
    sP1(sK3,sK4) ),
    inference(subsumption_resolution,[],[f126,f71])).

fof(f126,plain,
    ( sP1(sK3,sK4)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f125,f72])).

fof(f125,plain,
    ( sP1(sK3,sK4)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f122,f73])).

fof(f122,plain,
    ( sP1(sK3,sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f100,f75])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | sP1(X0,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f46,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_tmap_1)).

fof(f1146,plain,
    ( k4_tmap_1(sK3,sK4) = sK5
    | ~ sP1(sK3,sK4)
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f1145,f76])).

fof(f1145,plain,
    ( k4_tmap_1(sK3,sK4) = sK5
    | ~ v1_funct_1(sK5)
    | ~ sP1(sK3,sK4)
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f1144,f77])).

fof(f1144,plain,
    ( k4_tmap_1(sK3,sK4) = sK5
    | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK5)
    | ~ sP1(sK3,sK4)
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f1142,f78])).

fof(f1142,plain,
    ( k4_tmap_1(sK3,sK4) = sK5
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK5)
    | ~ sP1(sK3,sK4)
    | ~ spl7_38 ),
    inference(resolution,[],[f1136,f236])).

fof(f236,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,k4_tmap_1(X2,X1))
      | k4_tmap_1(X2,X1) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ sP1(X2,X1) ) ),
    inference(subsumption_resolution,[],[f235,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k4_tmap_1(X0,X1))
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f55])).

fof(f235,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,k4_tmap_1(X2,X1))
      | k4_tmap_1(X2,X1) = X3
      | ~ v1_funct_1(k4_tmap_1(X2,X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ sP1(X2,X1) ) ),
    inference(subsumption_resolution,[],[f231,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f231,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,k4_tmap_1(X2,X1))
      | k4_tmap_1(X2,X1) = X3
      | ~ v1_funct_2(k4_tmap_1(X2,X1),u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(k4_tmap_1(X2,X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ sP1(X2,X1) ) ),
    inference(resolution,[],[f102,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f1136,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,k4_tmap_1(sK3,sK4))
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f1134])).

fof(f80,plain,(
    ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k4_tmap_1(sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f62])).

fof(f384,plain,
    ( ~ spl7_8
    | spl7_11 ),
    inference(avatar_split_clause,[],[f332,f381,f356])).

fof(f356,plain,
    ( spl7_8
  <=> sP2(sK3,sK4,k4_tmap_1(sK3,sK4),sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f332,plain,
    ( m1_subset_1(k4_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ sP2(sK3,sK4,k4_tmap_1(sK3,sK4),sK4,sK3) ),
    inference(superposition,[],[f106,f325])).

fof(f325,plain,(
    k4_tmap_1(sK3,sK4) = k3_tmap_1(sK3,sK3,sK4,sK4,k4_tmap_1(sK3,sK4)) ),
    inference(subsumption_resolution,[],[f324,f71])).

fof(f324,plain,
    ( v2_struct_0(sK3)
    | k4_tmap_1(sK3,sK4) = k3_tmap_1(sK3,sK3,sK4,sK4,k4_tmap_1(sK3,sK4)) ),
    inference(subsumption_resolution,[],[f323,f72])).

fof(f323,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | k4_tmap_1(sK3,sK4) = k3_tmap_1(sK3,sK3,sK4,sK4,k4_tmap_1(sK3,sK4)) ),
    inference(subsumption_resolution,[],[f320,f73])).

fof(f320,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | k4_tmap_1(sK3,sK4) = k3_tmap_1(sK3,sK3,sK4,sK4,k4_tmap_1(sK3,sK4)) ),
    inference(resolution,[],[f317,f75])).

fof(f317,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK4,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k4_tmap_1(sK3,sK4) = k3_tmap_1(X0,sK3,sK4,sK4,k4_tmap_1(sK3,sK4)) ) ),
    inference(subsumption_resolution,[],[f316,f71])).

fof(f316,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK4,X0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k4_tmap_1(sK3,sK4) = k3_tmap_1(X0,sK3,sK4,sK4,k4_tmap_1(sK3,sK4)) ) ),
    inference(subsumption_resolution,[],[f315,f72])).

fof(f315,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK4,X0)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k4_tmap_1(sK3,sK4) = k3_tmap_1(X0,sK3,sK4,sK4,k4_tmap_1(sK3,sK4)) ) ),
    inference(subsumption_resolution,[],[f314,f73])).

fof(f314,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK4,X0)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k4_tmap_1(sK3,sK4) = k3_tmap_1(X0,sK3,sK4,sK4,k4_tmap_1(sK3,sK4)) ) ),
    inference(subsumption_resolution,[],[f311,f74])).

fof(f311,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK4,X0)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k4_tmap_1(sK3,sK4) = k3_tmap_1(X0,sK3,sK4,sK4,k4_tmap_1(sK3,sK4)) ) ),
    inference(resolution,[],[f279,f127])).

fof(f279,plain,(
    ! [X2,X3,X1] :
      ( ~ sP1(X2,X3)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | k4_tmap_1(X2,X3) = k3_tmap_1(X1,X2,X3,X3,k4_tmap_1(X2,X3)) ) ),
    inference(subsumption_resolution,[],[f278,f97])).

fof(f278,plain,(
    ! [X2,X3,X1] :
      ( k4_tmap_1(X2,X3) = k3_tmap_1(X1,X2,X3,X3,k4_tmap_1(X2,X3))
      | ~ v1_funct_1(k4_tmap_1(X2,X3))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ sP1(X2,X3) ) ),
    inference(subsumption_resolution,[],[f270,f98])).

fof(f270,plain,(
    ! [X2,X3,X1] :
      ( k4_tmap_1(X2,X3) = k3_tmap_1(X1,X2,X3,X3,k4_tmap_1(X2,X3))
      | ~ v1_funct_2(k4_tmap_1(X2,X3),u1_struct_0(X3),u1_struct_0(X2))
      | ~ v1_funct_1(k4_tmap_1(X2,X3))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ sP1(X2,X3) ) ),
    inference(resolution,[],[f268,f99])).

fof(f379,plain,
    ( ~ spl7_8
    | spl7_10 ),
    inference(avatar_split_clause,[],[f331,f376,f356])).

fof(f331,plain,
    ( v1_funct_2(k4_tmap_1(sK3,sK4),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ sP2(sK3,sK4,k4_tmap_1(sK3,sK4),sK4,sK3) ),
    inference(superposition,[],[f105,f325])).

fof(f371,plain,(
    spl7_8 ),
    inference(avatar_contradiction_clause,[],[f370])).

fof(f370,plain,
    ( $false
    | spl7_8 ),
    inference(subsumption_resolution,[],[f369,f127])).

fof(f369,plain,
    ( ~ sP1(sK3,sK4)
    | spl7_8 ),
    inference(subsumption_resolution,[],[f368,f71])).

fof(f368,plain,
    ( v2_struct_0(sK3)
    | ~ sP1(sK3,sK4)
    | spl7_8 ),
    inference(subsumption_resolution,[],[f367,f72])).

fof(f367,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ sP1(sK3,sK4)
    | spl7_8 ),
    inference(subsumption_resolution,[],[f366,f73])).

fof(f366,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ sP1(sK3,sK4)
    | spl7_8 ),
    inference(subsumption_resolution,[],[f365,f75])).

fof(f365,plain,
    ( ~ m1_pre_topc(sK4,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ sP1(sK3,sK4)
    | spl7_8 ),
    inference(duplicate_literal_removal,[],[f364])).

fof(f364,plain,
    ( ~ m1_pre_topc(sK4,sK3)
    | ~ m1_pre_topc(sK4,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ sP1(sK3,sK4)
    | spl7_8 ),
    inference(resolution,[],[f358,f255])).

fof(f255,plain,(
    ! [X4,X2,X5,X3] :
      ( sP2(X2,X3,k4_tmap_1(X2,X4),X4,X5)
      | ~ m1_pre_topc(X3,X5)
      | ~ m1_pre_topc(X4,X5)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ sP1(X2,X4) ) ),
    inference(subsumption_resolution,[],[f254,f97])).

fof(f254,plain,(
    ! [X4,X2,X5,X3] :
      ( sP2(X2,X3,k4_tmap_1(X2,X4),X4,X5)
      | ~ v1_funct_1(k4_tmap_1(X2,X4))
      | ~ m1_pre_topc(X3,X5)
      | ~ m1_pre_topc(X4,X5)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ sP1(X2,X4) ) ),
    inference(subsumption_resolution,[],[f247,f98])).

fof(f247,plain,(
    ! [X4,X2,X5,X3] :
      ( sP2(X2,X3,k4_tmap_1(X2,X4),X4,X5)
      | ~ v1_funct_2(k4_tmap_1(X2,X4),u1_struct_0(X4),u1_struct_0(X2))
      | ~ v1_funct_1(k4_tmap_1(X2,X4))
      | ~ m1_pre_topc(X3,X5)
      | ~ m1_pre_topc(X4,X5)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ sP1(X2,X4) ) ),
    inference(resolution,[],[f107,f99])).

fof(f358,plain,
    ( ~ sP2(sK3,sK4,k4_tmap_1(sK3,sK4),sK4,sK3)
    | spl7_8 ),
    inference(avatar_component_clause,[],[f356])).

fof(f363,plain,
    ( ~ spl7_8
    | spl7_9 ),
    inference(avatar_split_clause,[],[f330,f360,f356])).

fof(f330,plain,
    ( v1_funct_1(k4_tmap_1(sK3,sK4))
    | ~ sP2(sK3,sK4,k4_tmap_1(sK3,sK4),sK4,sK3) ),
    inference(superposition,[],[f104,f325])).

fof(f208,plain,
    ( spl7_5
    | spl7_3 ),
    inference(avatar_split_clause,[],[f151,f173,f206])).

fof(f151,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(u1_struct_0(sK4))
      | ~ sP0(X0,X1,X2,sK4,X3)
      | sK6(X0,X1,X2,sK4,X3) = k1_funct_1(sK5,sK6(X0,X1,X2,sK4,X3))
      | ~ m1_subset_1(sK6(X0,X1,X2,sK4,X3),u1_struct_0(sK3)) ) ),
    inference(resolution,[],[f142,f79])).

fof(f79,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,u1_struct_0(sK4))
      | k1_funct_1(sK5,X3) = X3
      | ~ m1_subset_1(X3,u1_struct_0(sK3)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f183,plain,(
    ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f181,f74])).

fof(f181,plain,
    ( v2_struct_0(sK4)
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f180,f115])).

fof(f115,plain,(
    l1_struct_0(sK4) ),
    inference(resolution,[],[f114,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f180,plain,
    ( ~ l1_struct_0(sK4)
    | v2_struct_0(sK4)
    | ~ spl7_3 ),
    inference(resolution,[],[f175,f84])).

fof(f84,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f175,plain,
    ( v1_xboole_0(u1_struct_0(sK4))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f173])).

fof(f179,plain,
    ( spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f167,f177,f173])).

fof(f167,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
      | k1_funct_1(sK5,X0) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0)
      | v1_xboole_0(u1_struct_0(sK4)) ) ),
    inference(subsumption_resolution,[],[f166,f76])).

fof(f166,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
      | k1_funct_1(sK5,X0) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0)
      | ~ v1_funct_1(sK5)
      | v1_xboole_0(u1_struct_0(sK4)) ) ),
    inference(subsumption_resolution,[],[f163,f77])).

fof(f163,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
      | k1_funct_1(sK5,X0) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0)
      | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(sK5)
      | v1_xboole_0(u1_struct_0(sK4)) ) ),
    inference(resolution,[],[f101,f78])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:29:10 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (21252)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.51  % (21268)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.51  % (21253)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  % (21258)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.52  % (21259)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.52  % (21265)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.52  % (21273)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.52  % (21266)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.52  % (21267)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.52  % (21260)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.52  % (21274)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.53  % (21257)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.53  % (21254)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.53  % (21251)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (21275)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.54  % (21269)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.54  % (21261)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.54  % (21250)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.54  % (21271)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.54  % (21270)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.54  % (21256)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.54  % (21255)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.54  % (21264)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.55  % (21262)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.55  % (21250)Refutation not found, incomplete strategy% (21250)------------------------------
% 0.20/0.55  % (21250)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (21250)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (21250)Memory used [KB]: 10618
% 0.20/0.55  % (21250)Time elapsed: 0.127 s
% 0.20/0.55  % (21250)------------------------------
% 0.20/0.55  % (21250)------------------------------
% 0.20/0.55  % (21263)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.55  % (21272)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.92/0.62  % (21275)Refutation found. Thanks to Tanya!
% 1.92/0.62  % SZS status Theorem for theBenchmark
% 1.92/0.62  % SZS output start Proof for theBenchmark
% 1.92/0.62  fof(f1526,plain,(
% 1.92/0.62    $false),
% 1.92/0.62    inference(avatar_sat_refutation,[],[f179,f183,f208,f363,f371,f379,f384,f1175,f1305,f1308,f1521])).
% 1.92/0.62  fof(f1521,plain,(
% 1.92/0.62    spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_9 | ~spl7_10 | ~spl7_11 | spl7_38 | ~spl7_41),
% 1.92/0.62    inference(avatar_contradiction_clause,[],[f1520])).
% 1.92/0.62  fof(f1520,plain,(
% 1.92/0.62    $false | (spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_9 | ~spl7_10 | ~spl7_11 | spl7_38 | ~spl7_41)),
% 1.92/0.62    inference(subsumption_resolution,[],[f1519,f1367])).
% 1.92/0.62  fof(f1367,plain,(
% 1.92/0.62    sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) != k1_funct_1(k4_tmap_1(sK3,sK4),sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)) | (~spl7_4 | ~spl7_5 | ~spl7_9 | ~spl7_10 | ~spl7_11 | spl7_38 | ~spl7_41)),
% 1.92/0.62    inference(subsumption_resolution,[],[f1366,f1347])).
% 1.92/0.62  fof(f1347,plain,(
% 1.92/0.62    sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) | (~spl7_9 | ~spl7_10 | ~spl7_11 | spl7_38 | ~spl7_41)),
% 1.92/0.62    inference(subsumption_resolution,[],[f1346,f1135])).
% 1.92/0.62  fof(f1135,plain,(
% 1.92/0.62    ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,k4_tmap_1(sK3,sK4)) | spl7_38),
% 1.92/0.62    inference(avatar_component_clause,[],[f1134])).
% 1.92/0.62  fof(f1134,plain,(
% 1.92/0.62    spl7_38 <=> r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,k4_tmap_1(sK3,sK4))),
% 1.92/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).
% 1.92/0.62  fof(f1346,plain,(
% 1.92/0.62    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,k4_tmap_1(sK3,sK4)) | sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) | (~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_41)),
% 1.92/0.62    inference(subsumption_resolution,[],[f1345,f378])).
% 1.92/0.62  fof(f378,plain,(
% 1.92/0.62    v1_funct_2(k4_tmap_1(sK3,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) | ~spl7_10),
% 1.92/0.62    inference(avatar_component_clause,[],[f376])).
% 1.92/0.62  fof(f376,plain,(
% 1.92/0.62    spl7_10 <=> v1_funct_2(k4_tmap_1(sK3,sK4),u1_struct_0(sK4),u1_struct_0(sK3))),
% 1.92/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.92/0.62  fof(f1345,plain,(
% 1.92/0.62    ~v1_funct_2(k4_tmap_1(sK3,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,k4_tmap_1(sK3,sK4)) | sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) | (~spl7_9 | ~spl7_11 | ~spl7_41)),
% 1.92/0.62    inference(subsumption_resolution,[],[f1340,f362])).
% 1.92/0.62  fof(f362,plain,(
% 1.92/0.62    v1_funct_1(k4_tmap_1(sK3,sK4)) | ~spl7_9),
% 1.92/0.62    inference(avatar_component_clause,[],[f360])).
% 1.92/0.62  fof(f360,plain,(
% 1.92/0.62    spl7_9 <=> v1_funct_1(k4_tmap_1(sK3,sK4))),
% 1.92/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.92/0.62  fof(f1340,plain,(
% 1.92/0.62    ~v1_funct_1(k4_tmap_1(sK3,sK4)) | ~v1_funct_2(k4_tmap_1(sK3,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,k4_tmap_1(sK3,sK4)) | sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) | (~spl7_11 | ~spl7_41)),
% 1.92/0.62    inference(resolution,[],[f1304,f383])).
% 1.92/0.62  fof(f383,plain,(
% 1.92/0.62    m1_subset_1(k4_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~spl7_11),
% 1.92/0.62    inference(avatar_component_clause,[],[f381])).
% 1.92/0.62  fof(f381,plain,(
% 1.92/0.62    spl7_11 <=> m1_subset_1(k4_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))),
% 1.92/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 1.92/0.62  fof(f1304,plain,(
% 1.92/0.62    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) | sP0(X0,sK5,sK3,sK4,sK4)) ) | ~spl7_41),
% 1.92/0.62    inference(avatar_component_clause,[],[f1303])).
% 1.92/0.62  fof(f1303,plain,(
% 1.92/0.62    spl7_41 <=> ! [X0] : (r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | sP0(X0,sK5,sK3,sK4,sK4))),
% 1.92/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).
% 1.92/0.62  fof(f1366,plain,(
% 1.92/0.62    sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) != k1_funct_1(k4_tmap_1(sK3,sK4),sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)) | ~sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) | (~spl7_4 | ~spl7_5 | ~spl7_9 | ~spl7_10 | ~spl7_11 | spl7_38 | ~spl7_41)),
% 1.92/0.62    inference(superposition,[],[f89,f1358])).
% 1.92/0.62  fof(f1358,plain,(
% 1.92/0.62    sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)) | (~spl7_4 | ~spl7_5 | ~spl7_9 | ~spl7_10 | ~spl7_11 | spl7_38 | ~spl7_41)),
% 1.92/0.62    inference(forward_demodulation,[],[f1351,f1350])).
% 1.92/0.62  fof(f1350,plain,(
% 1.92/0.62    sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k1_funct_1(sK5,sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)) | (~spl7_5 | ~spl7_9 | ~spl7_10 | ~spl7_11 | spl7_38 | ~spl7_41)),
% 1.92/0.62    inference(resolution,[],[f1347,f214])).
% 1.92/0.62  fof(f214,plain,(
% 1.92/0.62    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,sK4,X3) | sK6(X0,X1,X2,sK4,X3) = k1_funct_1(sK5,sK6(X0,X1,X2,sK4,X3))) ) | ~spl7_5),
% 1.92/0.62    inference(subsumption_resolution,[],[f213,f71])).
% 1.92/0.62  fof(f71,plain,(
% 1.92/0.62    ~v2_struct_0(sK3)),
% 1.92/0.62    inference(cnf_transformation,[],[f62])).
% 1.92/0.62  fof(f62,plain,(
% 1.92/0.62    ((~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k4_tmap_1(sK3,sK4),sK5) & ! [X3] : (k1_funct_1(sK5,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK4)) | ~m1_subset_1(X3,u1_struct_0(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK3) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 1.92/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f21,f61,f60,f59])).
% 1.92/0.62  fof(f59,plain,(
% 1.92/0.62    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(sK3),k4_tmap_1(sK3,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(sK3))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK3) & ~v2_struct_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 1.92/0.62    introduced(choice_axiom,[])).
% 1.92/0.62  fof(f60,plain,(
% 1.92/0.62    ? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(sK3),k4_tmap_1(sK3,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(sK3))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK3) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k4_tmap_1(sK3,sK4),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK4)) | ~m1_subset_1(X3,u1_struct_0(sK3))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(X2)) & m1_pre_topc(sK4,sK3) & ~v2_struct_0(sK4))),
% 1.92/0.62    introduced(choice_axiom,[])).
% 1.92/0.62  fof(f61,plain,(
% 1.92/0.62    ? [X2] : (~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k4_tmap_1(sK3,sK4),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK4)) | ~m1_subset_1(X3,u1_struct_0(sK3))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k4_tmap_1(sK3,sK4),sK5) & ! [X3] : (k1_funct_1(sK5,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK4)) | ~m1_subset_1(X3,u1_struct_0(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(sK5))),
% 1.92/0.62    introduced(choice_axiom,[])).
% 1.92/0.62  fof(f21,plain,(
% 1.92/0.62    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.92/0.62    inference(flattening,[],[f20])).
% 1.92/0.62  fof(f20,plain,(
% 1.92/0.62    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : ((k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.92/0.62    inference(ennf_transformation,[],[f19])).
% 1.92/0.62  fof(f19,negated_conjecture,(
% 1.92/0.62    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 1.92/0.62    inference(negated_conjecture,[],[f18])).
% 1.92/0.62  fof(f18,conjecture,(
% 1.92/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 1.92/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_tmap_1)).
% 1.92/0.62  fof(f213,plain,(
% 1.92/0.62    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,sK4,X3) | sK6(X0,X1,X2,sK4,X3) = k1_funct_1(sK5,sK6(X0,X1,X2,sK4,X3)) | v2_struct_0(sK3)) ) | ~spl7_5),
% 1.92/0.62    inference(subsumption_resolution,[],[f212,f73])).
% 1.92/0.62  fof(f73,plain,(
% 1.92/0.62    l1_pre_topc(sK3)),
% 1.92/0.62    inference(cnf_transformation,[],[f62])).
% 1.92/0.62  fof(f212,plain,(
% 1.92/0.62    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,sK4,X3) | sK6(X0,X1,X2,sK4,X3) = k1_funct_1(sK5,sK6(X0,X1,X2,sK4,X3)) | ~l1_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl7_5),
% 1.92/0.62    inference(subsumption_resolution,[],[f211,f74])).
% 1.92/0.62  fof(f74,plain,(
% 1.92/0.62    ~v2_struct_0(sK4)),
% 1.92/0.62    inference(cnf_transformation,[],[f62])).
% 1.92/0.62  fof(f211,plain,(
% 1.92/0.62    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,sK4,X3) | sK6(X0,X1,X2,sK4,X3) = k1_funct_1(sK5,sK6(X0,X1,X2,sK4,X3)) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl7_5),
% 1.92/0.62    inference(subsumption_resolution,[],[f210,f75])).
% 1.92/0.62  fof(f75,plain,(
% 1.92/0.62    m1_pre_topc(sK4,sK3)),
% 1.92/0.62    inference(cnf_transformation,[],[f62])).
% 1.92/0.62  fof(f210,plain,(
% 1.92/0.62    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,sK4,X3) | sK6(X0,X1,X2,sK4,X3) = k1_funct_1(sK5,sK6(X0,X1,X2,sK4,X3)) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl7_5),
% 1.92/0.62    inference(duplicate_literal_removal,[],[f209])).
% 1.92/0.62  fof(f209,plain,(
% 1.92/0.62    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,sK4,X3) | sK6(X0,X1,X2,sK4,X3) = k1_funct_1(sK5,sK6(X0,X1,X2,sK4,X3)) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | v2_struct_0(sK3) | ~sP0(X0,X1,X2,sK4,X3)) ) | ~spl7_5),
% 1.92/0.62    inference(resolution,[],[f207,f144])).
% 1.92/0.62  fof(f144,plain,(
% 1.92/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(sK6(X0,X1,X2,X3,X4),u1_struct_0(X5)) | ~m1_pre_topc(X3,X5) | v2_struct_0(X3) | ~l1_pre_topc(X5) | v2_struct_0(X5) | ~sP0(X0,X1,X2,X3,X4)) )),
% 1.92/0.62    inference(resolution,[],[f93,f87])).
% 1.92/0.62  fof(f87,plain,(
% 1.92/0.62    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK6(X0,X1,X2,X3,X4),u1_struct_0(X3)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 1.92/0.62    inference(cnf_transformation,[],[f66])).
% 1.92/0.62  fof(f66,plain,(
% 1.92/0.62    ! [X0,X1,X2,X3,X4] : ((k3_funct_2(u1_struct_0(X3),u1_struct_0(X2),X1,sK6(X0,X1,X2,X3,X4)) != k1_funct_1(X0,sK6(X0,X1,X2,X3,X4)) & r2_hidden(sK6(X0,X1,X2,X3,X4),u1_struct_0(X4)) & m1_subset_1(sK6(X0,X1,X2,X3,X4),u1_struct_0(X3))) | ~sP0(X0,X1,X2,X3,X4))),
% 1.92/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f64,f65])).
% 1.92/0.62  fof(f65,plain,(
% 1.92/0.62    ! [X4,X3,X2,X1,X0] : (? [X5] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X2),X1,X5) != k1_funct_1(X0,X5) & r2_hidden(X5,u1_struct_0(X4)) & m1_subset_1(X5,u1_struct_0(X3))) => (k3_funct_2(u1_struct_0(X3),u1_struct_0(X2),X1,sK6(X0,X1,X2,X3,X4)) != k1_funct_1(X0,sK6(X0,X1,X2,X3,X4)) & r2_hidden(sK6(X0,X1,X2,X3,X4),u1_struct_0(X4)) & m1_subset_1(sK6(X0,X1,X2,X3,X4),u1_struct_0(X3))))),
% 1.92/0.62    introduced(choice_axiom,[])).
% 1.92/0.62  fof(f64,plain,(
% 1.92/0.62    ! [X0,X1,X2,X3,X4] : (? [X5] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X2),X1,X5) != k1_funct_1(X0,X5) & r2_hidden(X5,u1_struct_0(X4)) & m1_subset_1(X5,u1_struct_0(X3))) | ~sP0(X0,X1,X2,X3,X4))),
% 1.92/0.62    inference(rectify,[],[f63])).
% 1.92/0.62  fof(f63,plain,(
% 1.92/0.62    ! [X4,X3,X0,X1,X2] : (? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) | ~sP0(X4,X3,X0,X1,X2))),
% 1.92/0.62    inference(nnf_transformation,[],[f53])).
% 1.92/0.62  fof(f53,plain,(
% 1.92/0.62    ! [X4,X3,X0,X1,X2] : (? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) | ~sP0(X4,X3,X0,X1,X2))),
% 1.92/0.62    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.92/0.62  fof(f93,plain,(
% 1.92/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.92/0.62    inference(cnf_transformation,[],[f38])).
% 1.92/0.62  fof(f38,plain,(
% 1.92/0.62    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.92/0.62    inference(flattening,[],[f37])).
% 1.92/0.62  fof(f37,plain,(
% 1.92/0.62    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.92/0.62    inference(ennf_transformation,[],[f8])).
% 1.92/0.62  fof(f8,axiom,(
% 1.92/0.62    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 1.92/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).
% 1.92/0.62  fof(f207,plain,(
% 1.92/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK6(X0,X1,X2,sK4,X3),u1_struct_0(sK3)) | ~sP0(X0,X1,X2,sK4,X3) | sK6(X0,X1,X2,sK4,X3) = k1_funct_1(sK5,sK6(X0,X1,X2,sK4,X3))) ) | ~spl7_5),
% 1.92/0.62    inference(avatar_component_clause,[],[f206])).
% 1.92/0.62  fof(f206,plain,(
% 1.92/0.62    spl7_5 <=> ! [X1,X3,X0,X2] : (~sP0(X0,X1,X2,sK4,X3) | ~m1_subset_1(sK6(X0,X1,X2,sK4,X3),u1_struct_0(sK3)) | sK6(X0,X1,X2,sK4,X3) = k1_funct_1(sK5,sK6(X0,X1,X2,sK4,X3)))),
% 1.92/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.92/0.62  fof(f1351,plain,(
% 1.92/0.62    k1_funct_1(sK5,sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)) | (~spl7_4 | ~spl7_9 | ~spl7_10 | ~spl7_11 | spl7_38 | ~spl7_41)),
% 1.92/0.62    inference(resolution,[],[f1347,f184])).
% 1.92/0.62  fof(f184,plain,(
% 1.92/0.62    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,sK4,X3) | k1_funct_1(sK5,sK6(X0,X1,X2,sK4,X3)) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK6(X0,X1,X2,sK4,X3))) ) | ~spl7_4),
% 1.92/0.62    inference(resolution,[],[f178,f87])).
% 1.92/0.62  fof(f178,plain,(
% 1.92/0.62    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK4)) | k1_funct_1(sK5,X0) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0)) ) | ~spl7_4),
% 1.92/0.62    inference(avatar_component_clause,[],[f177])).
% 1.92/0.62  fof(f177,plain,(
% 1.92/0.62    spl7_4 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK4)) | k1_funct_1(sK5,X0) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0))),
% 1.92/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.92/0.62  fof(f89,plain,(
% 1.92/0.62    ( ! [X4,X2,X0,X3,X1] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X2),X1,sK6(X0,X1,X2,X3,X4)) != k1_funct_1(X0,sK6(X0,X1,X2,X3,X4)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 1.92/0.62    inference(cnf_transformation,[],[f66])).
% 1.92/0.62  fof(f1519,plain,(
% 1.92/0.62    sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k1_funct_1(k4_tmap_1(sK3,sK4),sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)) | (spl7_3 | ~spl7_9 | ~spl7_10 | ~spl7_11 | spl7_38 | ~spl7_41)),
% 1.92/0.62    inference(subsumption_resolution,[],[f1518,f71])).
% 1.92/0.62  fof(f1518,plain,(
% 1.92/0.62    v2_struct_0(sK3) | sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k1_funct_1(k4_tmap_1(sK3,sK4),sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)) | (spl7_3 | ~spl7_9 | ~spl7_10 | ~spl7_11 | spl7_38 | ~spl7_41)),
% 1.92/0.62    inference(subsumption_resolution,[],[f1517,f72])).
% 1.92/0.62  fof(f72,plain,(
% 1.92/0.62    v2_pre_topc(sK3)),
% 1.92/0.62    inference(cnf_transformation,[],[f62])).
% 1.92/0.62  fof(f1517,plain,(
% 1.92/0.62    ~v2_pre_topc(sK3) | v2_struct_0(sK3) | sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k1_funct_1(k4_tmap_1(sK3,sK4),sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)) | (spl7_3 | ~spl7_9 | ~spl7_10 | ~spl7_11 | spl7_38 | ~spl7_41)),
% 1.92/0.62    inference(subsumption_resolution,[],[f1513,f73])).
% 1.92/0.62  fof(f1513,plain,(
% 1.92/0.62    ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k1_funct_1(k4_tmap_1(sK3,sK4),sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)) | (spl7_3 | ~spl7_9 | ~spl7_10 | ~spl7_11 | spl7_38 | ~spl7_41)),
% 1.92/0.62    inference(resolution,[],[f1361,f75])).
% 1.92/0.62  fof(f1361,plain,(
% 1.92/0.62    ( ! [X1] : (~m1_pre_topc(sK4,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k1_funct_1(k4_tmap_1(X1,sK4),sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4))) ) | (spl7_3 | ~spl7_9 | ~spl7_10 | ~spl7_11 | spl7_38 | ~spl7_41)),
% 1.92/0.62    inference(subsumption_resolution,[],[f1360,f174])).
% 1.92/0.62  fof(f174,plain,(
% 1.92/0.62    ~v1_xboole_0(u1_struct_0(sK4)) | spl7_3),
% 1.92/0.62    inference(avatar_component_clause,[],[f173])).
% 1.92/0.62  fof(f173,plain,(
% 1.92/0.62    spl7_3 <=> v1_xboole_0(u1_struct_0(sK4))),
% 1.92/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.92/0.62  fof(f1360,plain,(
% 1.92/0.62    ( ! [X1] : (~m1_pre_topc(sK4,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | v1_xboole_0(u1_struct_0(sK4)) | sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k1_funct_1(k4_tmap_1(X1,sK4),sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4))) ) | (~spl7_9 | ~spl7_10 | ~spl7_11 | spl7_38 | ~spl7_41)),
% 1.92/0.62    inference(subsumption_resolution,[],[f1354,f74])).
% 1.92/0.62  fof(f1354,plain,(
% 1.92/0.62    ( ! [X1] : (~m1_pre_topc(sK4,X1) | v2_struct_0(sK4) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | v1_xboole_0(u1_struct_0(sK4)) | sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k1_funct_1(k4_tmap_1(X1,sK4),sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4))) ) | (~spl7_9 | ~spl7_10 | ~spl7_11 | spl7_38 | ~spl7_41)),
% 1.92/0.62    inference(resolution,[],[f1347,f162])).
% 1.92/0.62  fof(f162,plain,(
% 1.92/0.62    ( ! [X6,X10,X8,X7,X11,X9] : (~sP0(X8,X9,X10,X7,X11) | ~m1_pre_topc(X7,X6) | v2_struct_0(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | v1_xboole_0(u1_struct_0(X7)) | sK6(X8,X9,X10,X7,X11) = k1_funct_1(k4_tmap_1(X6,X7),sK6(X8,X9,X10,X7,X11))) )),
% 1.92/0.62    inference(subsumption_resolution,[],[f161,f144])).
% 1.92/0.62  fof(f161,plain,(
% 1.92/0.62    ( ! [X6,X10,X8,X7,X11,X9] : (sK6(X8,X9,X10,X7,X11) = k1_funct_1(k4_tmap_1(X6,X7),sK6(X8,X9,X10,X7,X11)) | ~m1_subset_1(sK6(X8,X9,X10,X7,X11),u1_struct_0(X6)) | ~m1_pre_topc(X7,X6) | v2_struct_0(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | v1_xboole_0(u1_struct_0(X7)) | ~sP0(X8,X9,X10,X7,X11)) )),
% 1.92/0.62    inference(resolution,[],[f92,f142])).
% 1.92/0.62  fof(f142,plain,(
% 1.92/0.62    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(sK6(X0,X1,X2,X3,X4),u1_struct_0(X3)) | v1_xboole_0(u1_struct_0(X3)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 1.92/0.62    inference(resolution,[],[f87,f96])).
% 1.92/0.62  fof(f96,plain,(
% 1.92/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.92/0.62    inference(cnf_transformation,[],[f44])).
% 1.92/0.62  fof(f44,plain,(
% 1.92/0.62    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.92/0.62    inference(flattening,[],[f43])).
% 1.92/0.62  fof(f43,plain,(
% 1.92/0.62    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.92/0.62    inference(ennf_transformation,[],[f1])).
% 1.92/0.62  fof(f1,axiom,(
% 1.92/0.62    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.92/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.92/0.62  fof(f92,plain,(
% 1.92/0.62    ( ! [X2,X0,X1] : (~r2_hidden(X2,u1_struct_0(X1)) | k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.92/0.62    inference(cnf_transformation,[],[f36])).
% 1.92/0.62  fof(f36,plain,(
% 1.92/0.62    ! [X0] : (! [X1] : (! [X2] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.92/0.62    inference(flattening,[],[f35])).
% 1.92/0.62  fof(f35,plain,(
% 1.92/0.62    ! [X0] : (! [X1] : (! [X2] : ((k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.92/0.62    inference(ennf_transformation,[],[f17])).
% 1.92/0.62  fof(f17,axiom,(
% 1.92/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,u1_struct_0(X1)) => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2))))),
% 1.92/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_tmap_1)).
% 1.92/0.62  fof(f1308,plain,(
% 1.92/0.62    spl7_40),
% 1.92/0.62    inference(avatar_contradiction_clause,[],[f1307])).
% 1.92/0.62  fof(f1307,plain,(
% 1.92/0.62    $false | spl7_40),
% 1.92/0.62    inference(subsumption_resolution,[],[f1306,f114])).
% 1.92/0.62  fof(f114,plain,(
% 1.92/0.62    l1_pre_topc(sK4)),
% 1.92/0.62    inference(subsumption_resolution,[],[f111,f73])).
% 1.92/0.62  fof(f111,plain,(
% 1.92/0.62    l1_pre_topc(sK4) | ~l1_pre_topc(sK3)),
% 1.92/0.62    inference(resolution,[],[f83,f75])).
% 1.92/0.62  fof(f83,plain,(
% 1.92/0.62    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.92/0.62    inference(cnf_transformation,[],[f24])).
% 1.92/0.62  fof(f24,plain,(
% 1.92/0.62    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.92/0.62    inference(ennf_transformation,[],[f6])).
% 1.92/0.62  fof(f6,axiom,(
% 1.92/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.92/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.92/0.62  fof(f1306,plain,(
% 1.92/0.62    ~l1_pre_topc(sK4) | spl7_40),
% 1.92/0.62    inference(resolution,[],[f1301,f82])).
% 1.92/0.62  fof(f82,plain,(
% 1.92/0.62    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 1.92/0.62    inference(cnf_transformation,[],[f23])).
% 1.92/0.62  fof(f23,plain,(
% 1.92/0.62    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 1.92/0.62    inference(ennf_transformation,[],[f13])).
% 1.92/0.62  fof(f13,axiom,(
% 1.92/0.62    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 1.92/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 1.92/0.62  fof(f1301,plain,(
% 1.92/0.62    ~m1_pre_topc(sK4,sK4) | spl7_40),
% 1.92/0.62    inference(avatar_component_clause,[],[f1299])).
% 1.92/0.62  fof(f1299,plain,(
% 1.92/0.62    spl7_40 <=> m1_pre_topc(sK4,sK4)),
% 1.92/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).
% 1.92/0.62  fof(f1305,plain,(
% 1.92/0.62    ~spl7_40 | spl7_41),
% 1.92/0.62    inference(avatar_split_clause,[],[f731,f1303,f1299])).
% 1.92/0.62  fof(f731,plain,(
% 1.92/0.62    ( ! [X0] : (r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) | sP0(X0,sK5,sK3,sK4,sK4) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK4,sK4)) )),
% 1.92/0.62    inference(subsumption_resolution,[],[f730,f71])).
% 1.92/0.62  fof(f730,plain,(
% 1.92/0.62    ( ! [X0] : (r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) | sP0(X0,sK5,sK3,sK4,sK4) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK4,sK4) | v2_struct_0(sK3)) )),
% 1.92/0.62    inference(subsumption_resolution,[],[f729,f72])).
% 1.92/0.62  fof(f729,plain,(
% 1.92/0.62    ( ! [X0] : (r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) | sP0(X0,sK5,sK3,sK4,sK4) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK4,sK4) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 1.92/0.62    inference(subsumption_resolution,[],[f728,f73])).
% 1.92/0.62  fof(f728,plain,(
% 1.92/0.62    ( ! [X0] : (r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) | sP0(X0,sK5,sK3,sK4,sK4) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK4,sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 1.92/0.62    inference(subsumption_resolution,[],[f727,f121])).
% 1.92/0.62  fof(f121,plain,(
% 1.92/0.62    v2_pre_topc(sK4)),
% 1.92/0.62    inference(subsumption_resolution,[],[f120,f72])).
% 1.92/0.62  fof(f120,plain,(
% 1.92/0.62    v2_pre_topc(sK4) | ~v2_pre_topc(sK3)),
% 1.92/0.62    inference(subsumption_resolution,[],[f117,f73])).
% 1.92/0.62  fof(f117,plain,(
% 1.92/0.62    v2_pre_topc(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3)),
% 1.92/0.62    inference(resolution,[],[f94,f75])).
% 1.92/0.62  fof(f94,plain,(
% 1.92/0.62    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.92/0.62    inference(cnf_transformation,[],[f40])).
% 1.92/0.62  fof(f40,plain,(
% 1.92/0.62    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.92/0.62    inference(flattening,[],[f39])).
% 1.92/0.62  fof(f39,plain,(
% 1.92/0.62    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.92/0.62    inference(ennf_transformation,[],[f4])).
% 1.92/0.62  fof(f4,axiom,(
% 1.92/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.92/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.92/0.62  fof(f727,plain,(
% 1.92/0.62    ( ! [X0] : (r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) | sP0(X0,sK5,sK3,sK4,sK4) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK4,sK4) | ~v2_pre_topc(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 1.92/0.62    inference(subsumption_resolution,[],[f726,f114])).
% 1.92/0.62  fof(f726,plain,(
% 1.92/0.62    ( ! [X0] : (r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) | sP0(X0,sK5,sK3,sK4,sK4) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK4,sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 1.92/0.62    inference(subsumption_resolution,[],[f725,f74])).
% 1.92/0.62  fof(f725,plain,(
% 1.92/0.62    ( ! [X0] : (r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) | sP0(X0,sK5,sK3,sK4,sK4) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK4,sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 1.92/0.62    inference(subsumption_resolution,[],[f724,f76])).
% 1.92/0.62  fof(f76,plain,(
% 1.92/0.62    v1_funct_1(sK5)),
% 1.92/0.62    inference(cnf_transformation,[],[f62])).
% 1.92/0.62  fof(f724,plain,(
% 1.92/0.62    ( ! [X0] : (r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) | sP0(X0,sK5,sK3,sK4,sK4) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(X0) | ~v1_funct_1(sK5) | ~m1_pre_topc(sK4,sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 1.92/0.62    inference(subsumption_resolution,[],[f723,f77])).
% 1.92/0.62  fof(f77,plain,(
% 1.92/0.62    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3))),
% 1.92/0.62    inference(cnf_transformation,[],[f62])).
% 1.92/0.62  fof(f723,plain,(
% 1.92/0.62    ( ! [X0] : (r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) | sP0(X0,sK5,sK3,sK4,sK4) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(X0) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK5) | ~m1_pre_topc(sK4,sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 1.92/0.62    inference(subsumption_resolution,[],[f722,f78])).
% 1.92/0.62  fof(f78,plain,(
% 1.92/0.62    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))),
% 1.92/0.62    inference(cnf_transformation,[],[f62])).
% 1.92/0.62  fof(f722,plain,(
% 1.92/0.62    ( ! [X0] : (r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) | sP0(X0,sK5,sK3,sK4,sK4) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(X0) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK5) | ~m1_pre_topc(sK4,sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 1.92/0.62    inference(duplicate_literal_removal,[],[f721])).
% 1.92/0.62  fof(f721,plain,(
% 1.92/0.62    ( ! [X0] : (r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) | sP0(X0,sK5,sK3,sK4,sK4) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(X0,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(X0) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK5) | ~m1_pre_topc(sK4,sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 1.92/0.62    inference(superposition,[],[f90,f719])).
% 1.92/0.62  fof(f719,plain,(
% 1.92/0.62    sK5 = k2_tmap_1(sK4,sK3,sK5,sK4)),
% 1.92/0.62    inference(forward_demodulation,[],[f718,f287])).
% 1.92/0.62  fof(f287,plain,(
% 1.92/0.62    sK5 = k3_tmap_1(sK3,sK3,sK4,sK4,sK5)),
% 1.92/0.62    inference(subsumption_resolution,[],[f286,f71])).
% 1.92/0.62  fof(f286,plain,(
% 1.92/0.62    sK5 = k3_tmap_1(sK3,sK3,sK4,sK4,sK5) | v2_struct_0(sK3)),
% 1.92/0.62    inference(subsumption_resolution,[],[f285,f72])).
% 1.92/0.62  fof(f285,plain,(
% 1.92/0.62    sK5 = k3_tmap_1(sK3,sK3,sK4,sK4,sK5) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.92/0.62    inference(subsumption_resolution,[],[f282,f73])).
% 1.92/0.62  fof(f282,plain,(
% 1.92/0.62    sK5 = k3_tmap_1(sK3,sK3,sK4,sK4,sK5) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.92/0.62    inference(resolution,[],[f277,f75])).
% 1.92/0.62  fof(f277,plain,(
% 1.92/0.62    ( ! [X0] : (~m1_pre_topc(sK4,X0) | sK5 = k3_tmap_1(X0,sK3,sK4,sK4,sK5) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.92/0.62    inference(subsumption_resolution,[],[f276,f71])).
% 1.92/0.62  fof(f276,plain,(
% 1.92/0.62    ( ! [X0] : (sK5 = k3_tmap_1(X0,sK3,sK4,sK4,sK5) | ~m1_pre_topc(sK4,X0) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.92/0.62    inference(subsumption_resolution,[],[f275,f72])).
% 1.92/0.62  fof(f275,plain,(
% 1.92/0.62    ( ! [X0] : (sK5 = k3_tmap_1(X0,sK3,sK4,sK4,sK5) | ~m1_pre_topc(sK4,X0) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.92/0.62    inference(subsumption_resolution,[],[f274,f73])).
% 1.92/0.62  fof(f274,plain,(
% 1.92/0.62    ( ! [X0] : (sK5 = k3_tmap_1(X0,sK3,sK4,sK4,sK5) | ~m1_pre_topc(sK4,X0) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.92/0.62    inference(subsumption_resolution,[],[f273,f74])).
% 1.92/0.62  fof(f273,plain,(
% 1.92/0.62    ( ! [X0] : (sK5 = k3_tmap_1(X0,sK3,sK4,sK4,sK5) | ~m1_pre_topc(sK4,X0) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.92/0.62    inference(subsumption_resolution,[],[f272,f76])).
% 1.92/0.62  fof(f272,plain,(
% 1.92/0.62    ( ! [X0] : (sK5 = k3_tmap_1(X0,sK3,sK4,sK4,sK5) | ~v1_funct_1(sK5) | ~m1_pre_topc(sK4,X0) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.92/0.62    inference(subsumption_resolution,[],[f269,f77])).
% 1.92/0.62  fof(f269,plain,(
% 1.92/0.62    ( ! [X0] : (sK5 = k3_tmap_1(X0,sK3,sK4,sK4,sK5) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK5) | ~m1_pre_topc(sK4,X0) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.92/0.62    inference(resolution,[],[f268,f78])).
% 1.92/0.62  fof(f268,plain,(
% 1.92/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | k3_tmap_1(X0,X1,X2,X2,X3) = X3 | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.92/0.62    inference(subsumption_resolution,[],[f267,f107])).
% 1.92/0.62  fof(f107,plain,(
% 1.92/0.62    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | sP2(X1,X3,X4,X2,X0) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.92/0.62    inference(cnf_transformation,[],[f58])).
% 1.92/0.62  fof(f58,plain,(
% 1.92/0.62    ! [X0,X1,X2,X3,X4] : (sP2(X1,X3,X4,X2,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.92/0.62    inference(definition_folding,[],[f52,f57])).
% 1.92/0.62  fof(f57,plain,(
% 1.92/0.62    ! [X1,X3,X4,X2,X0] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~sP2(X1,X3,X4,X2,X0))),
% 1.92/0.62    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.92/0.62  fof(f52,plain,(
% 1.92/0.62    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.92/0.62    inference(flattening,[],[f51])).
% 1.92/0.62  fof(f51,plain,(
% 1.92/0.62    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.92/0.62    inference(ennf_transformation,[],[f11])).
% 1.92/0.62  fof(f11,axiom,(
% 1.92/0.62    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 1.92/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).
% 1.92/0.62  fof(f267,plain,(
% 1.92/0.62    ( ! [X2,X0,X3,X1] : (k3_tmap_1(X0,X1,X2,X2,X3) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~sP2(X1,X2,X3,X2,X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.92/0.62    inference(duplicate_literal_removal,[],[f264])).
% 1.92/0.62  fof(f264,plain,(
% 1.92/0.62    ( ! [X2,X0,X3,X1] : (k3_tmap_1(X0,X1,X2,X2,X3) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~sP2(X1,X2,X3,X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.92/0.62    inference(resolution,[],[f238,f86])).
% 1.92/0.62  fof(f86,plain,(
% 1.92/0.62    ( ! [X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.92/0.62    inference(cnf_transformation,[],[f30])).
% 1.92/0.62  fof(f30,plain,(
% 1.92/0.62    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.92/0.62    inference(flattening,[],[f29])).
% 1.92/0.62  fof(f29,plain,(
% 1.92/0.62    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.92/0.62    inference(ennf_transformation,[],[f15])).
% 1.92/0.62  fof(f15,axiom,(
% 1.92/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))))))),
% 1.92/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tmap_1)).
% 1.92/0.62  fof(f238,plain,(
% 1.92/0.62    ( ! [X6,X4,X8,X7,X5,X9] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X5),X6,k3_tmap_1(X7,X5,X8,X4,X9)) | k3_tmap_1(X7,X5,X8,X4,X9) = X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5)))) | ~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X5)) | ~v1_funct_1(X6) | ~sP2(X5,X4,X9,X8,X7)) )),
% 1.92/0.62    inference(subsumption_resolution,[],[f237,f104])).
% 1.92/0.62  fof(f104,plain,(
% 1.92/0.62    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2)) | ~sP2(X0,X1,X2,X3,X4)) )),
% 1.92/0.62    inference(cnf_transformation,[],[f70])).
% 1.92/0.62  fof(f70,plain,(
% 1.92/0.62    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2))) | ~sP2(X0,X1,X2,X3,X4))),
% 1.92/0.62    inference(rectify,[],[f69])).
% 1.92/0.62  fof(f69,plain,(
% 1.92/0.62    ! [X1,X3,X4,X2,X0] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~sP2(X1,X3,X4,X2,X0))),
% 1.92/0.62    inference(nnf_transformation,[],[f57])).
% 1.92/0.62  fof(f237,plain,(
% 1.92/0.62    ( ! [X6,X4,X8,X7,X5,X9] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X5),X6,k3_tmap_1(X7,X5,X8,X4,X9)) | k3_tmap_1(X7,X5,X8,X4,X9) = X6 | ~v1_funct_1(k3_tmap_1(X7,X5,X8,X4,X9)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5)))) | ~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X5)) | ~v1_funct_1(X6) | ~sP2(X5,X4,X9,X8,X7)) )),
% 1.92/0.62    inference(subsumption_resolution,[],[f232,f105])).
% 1.92/0.62  fof(f105,plain,(
% 1.92/0.62    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~sP2(X0,X1,X2,X3,X4)) )),
% 1.92/0.62    inference(cnf_transformation,[],[f70])).
% 1.92/0.62  fof(f232,plain,(
% 1.92/0.62    ( ! [X6,X4,X8,X7,X5,X9] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X5),X6,k3_tmap_1(X7,X5,X8,X4,X9)) | k3_tmap_1(X7,X5,X8,X4,X9) = X6 | ~v1_funct_2(k3_tmap_1(X7,X5,X8,X4,X9),u1_struct_0(X4),u1_struct_0(X5)) | ~v1_funct_1(k3_tmap_1(X7,X5,X8,X4,X9)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5)))) | ~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X5)) | ~v1_funct_1(X6) | ~sP2(X5,X4,X9,X8,X7)) )),
% 1.92/0.62    inference(resolution,[],[f102,f106])).
% 1.92/0.62  fof(f106,plain,(
% 1.92/0.62    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~sP2(X0,X1,X2,X3,X4)) )),
% 1.92/0.62    inference(cnf_transformation,[],[f70])).
% 1.92/0.63  % (21259)Refutation not found, incomplete strategy% (21259)------------------------------
% 1.92/0.63  % (21259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.92/0.63  % (21259)Termination reason: Refutation not found, incomplete strategy
% 1.92/0.63  
% 1.92/0.63  % (21259)Memory used [KB]: 6140
% 1.92/0.63  % (21259)Time elapsed: 0.214 s
% 1.92/0.63  % (21259)------------------------------
% 1.92/0.63  % (21259)------------------------------
% 1.92/0.64  fof(f102,plain,(
% 1.92/0.64    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_funct_2(X0,X1,X2,X3) | X2 = X3 | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.92/0.64    inference(cnf_transformation,[],[f68])).
% 1.92/0.64  fof(f68,plain,(
% 1.92/0.64    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.92/0.64    inference(nnf_transformation,[],[f50])).
% 1.92/0.64  fof(f50,plain,(
% 1.92/0.64    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.92/0.64    inference(flattening,[],[f49])).
% 1.92/0.64  fof(f49,plain,(
% 1.92/0.64    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.92/0.64    inference(ennf_transformation,[],[f3])).
% 1.92/0.64  fof(f3,axiom,(
% 1.92/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 1.92/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 1.92/0.64  fof(f718,plain,(
% 1.92/0.64    k3_tmap_1(sK3,sK3,sK4,sK4,sK5) = k2_tmap_1(sK4,sK3,sK5,sK4)),
% 1.92/0.64    inference(forward_demodulation,[],[f717,f482])).
% 1.92/0.64  fof(f482,plain,(
% 1.92/0.64    k2_tmap_1(sK4,sK3,sK5,sK4) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4))),
% 1.92/0.64    inference(subsumption_resolution,[],[f481,f114])).
% 1.92/0.64  fof(f481,plain,(
% 1.92/0.64    k2_tmap_1(sK4,sK3,sK5,sK4) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4)) | ~l1_pre_topc(sK4)),
% 1.92/0.64    inference(resolution,[],[f437,f82])).
% 1.92/0.64  fof(f437,plain,(
% 1.92/0.64    ( ! [X0] : (~m1_pre_topc(X0,sK4) | k2_tmap_1(sK4,sK3,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0))) )),
% 1.92/0.64    inference(subsumption_resolution,[],[f436,f74])).
% 1.92/0.64  fof(f436,plain,(
% 1.92/0.64    ( ! [X0] : (~m1_pre_topc(X0,sK4) | k2_tmap_1(sK4,sK3,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0)) | v2_struct_0(sK4)) )),
% 1.92/0.64    inference(subsumption_resolution,[],[f435,f121])).
% 1.92/0.64  fof(f435,plain,(
% 1.92/0.64    ( ! [X0] : (~m1_pre_topc(X0,sK4) | k2_tmap_1(sK4,sK3,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0)) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) )),
% 1.92/0.64    inference(subsumption_resolution,[],[f434,f114])).
% 1.92/0.64  fof(f434,plain,(
% 1.92/0.64    ( ! [X0] : (~m1_pre_topc(X0,sK4) | k2_tmap_1(sK4,sK3,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) )),
% 1.92/0.64    inference(subsumption_resolution,[],[f433,f71])).
% 1.92/0.64  fof(f433,plain,(
% 1.92/0.64    ( ! [X0] : (~m1_pre_topc(X0,sK4) | k2_tmap_1(sK4,sK3,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0)) | v2_struct_0(sK3) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) )),
% 1.92/0.64    inference(subsumption_resolution,[],[f432,f72])).
% 1.92/0.64  fof(f432,plain,(
% 1.92/0.64    ( ! [X0] : (~m1_pre_topc(X0,sK4) | k2_tmap_1(sK4,sK3,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) )),
% 1.92/0.64    inference(subsumption_resolution,[],[f431,f73])).
% 1.92/0.64  fof(f431,plain,(
% 1.92/0.64    ( ! [X0] : (~m1_pre_topc(X0,sK4) | k2_tmap_1(sK4,sK3,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) )),
% 1.92/0.64    inference(subsumption_resolution,[],[f430,f76])).
% 1.92/0.64  fof(f430,plain,(
% 1.92/0.64    ( ! [X0] : (~m1_pre_topc(X0,sK4) | k2_tmap_1(sK4,sK3,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) )),
% 1.92/0.64    inference(subsumption_resolution,[],[f426,f77])).
% 1.92/0.64  fof(f426,plain,(
% 1.92/0.64    ( ! [X0] : (~m1_pre_topc(X0,sK4) | k2_tmap_1(sK4,sK3,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0)) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) )),
% 1.92/0.64    inference(resolution,[],[f91,f78])).
% 1.92/0.64  fof(f91,plain,(
% 1.92/0.64    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.92/0.64    inference(cnf_transformation,[],[f34])).
% 1.92/0.64  fof(f34,plain,(
% 1.92/0.64    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.92/0.64    inference(flattening,[],[f33])).
% 1.92/0.64  fof(f33,plain,(
% 1.92/0.64    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.92/0.64    inference(ennf_transformation,[],[f9])).
% 1.92/0.64  fof(f9,axiom,(
% 1.92/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 1.92/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 1.92/0.64  fof(f717,plain,(
% 1.92/0.64    k3_tmap_1(sK3,sK3,sK4,sK4,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4))),
% 1.92/0.64    inference(subsumption_resolution,[],[f716,f114])).
% 1.92/0.64  fof(f716,plain,(
% 1.92/0.64    k3_tmap_1(sK3,sK3,sK4,sK4,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(sK4)) | ~l1_pre_topc(sK4)),
% 1.92/0.64    inference(resolution,[],[f704,f82])).
% 1.92/0.64  fof(f704,plain,(
% 1.92/0.64    ( ! [X0] : (~m1_pre_topc(X0,sK4) | k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0)) = k3_tmap_1(sK3,sK3,sK4,X0,sK5)) )),
% 1.92/0.64    inference(subsumption_resolution,[],[f703,f71])).
% 1.92/0.64  fof(f703,plain,(
% 1.92/0.64    ( ! [X0] : (k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0)) = k3_tmap_1(sK3,sK3,sK4,X0,sK5) | ~m1_pre_topc(X0,sK4) | v2_struct_0(sK3)) )),
% 1.92/0.64    inference(subsumption_resolution,[],[f702,f72])).
% 1.92/0.64  fof(f702,plain,(
% 1.92/0.64    ( ! [X0] : (k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0)) = k3_tmap_1(sK3,sK3,sK4,X0,sK5) | ~m1_pre_topc(X0,sK4) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 1.92/0.64    inference(subsumption_resolution,[],[f699,f73])).
% 1.92/0.64  fof(f699,plain,(
% 1.92/0.64    ( ! [X0] : (k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0)) = k3_tmap_1(sK3,sK3,sK4,X0,sK5) | ~m1_pre_topc(X0,sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 1.92/0.64    inference(resolution,[],[f595,f75])).
% 1.92/0.64  fof(f595,plain,(
% 1.92/0.64    ( ! [X0,X1] : (~m1_pre_topc(sK4,X1) | k3_tmap_1(X1,sK3,sK4,X0,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK4) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.92/0.64    inference(subsumption_resolution,[],[f594,f95])).
% 1.92/0.64  fof(f95,plain,(
% 1.92/0.64    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.92/0.64    inference(cnf_transformation,[],[f42])).
% 1.92/0.64  fof(f42,plain,(
% 1.92/0.64    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.92/0.64    inference(flattening,[],[f41])).
% 1.92/0.64  fof(f41,plain,(
% 1.92/0.64    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.92/0.64    inference(ennf_transformation,[],[f16])).
% 1.92/0.64  fof(f16,axiom,(
% 1.92/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 1.92/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).
% 1.92/0.64  fof(f594,plain,(
% 1.92/0.64    ( ! [X0,X1] : (~m1_pre_topc(X0,sK4) | k3_tmap_1(X1,sK3,sK4,X0,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK4,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.92/0.64    inference(subsumption_resolution,[],[f593,f71])).
% 1.92/0.64  fof(f593,plain,(
% 1.92/0.64    ( ! [X0,X1] : (~m1_pre_topc(X0,sK4) | k3_tmap_1(X1,sK3,sK4,X0,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK4,X1) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.92/0.64    inference(subsumption_resolution,[],[f592,f72])).
% 1.92/0.64  fof(f592,plain,(
% 1.92/0.64    ( ! [X0,X1] : (~m1_pre_topc(X0,sK4) | k3_tmap_1(X1,sK3,sK4,X0,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK4,X1) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.92/0.64    inference(subsumption_resolution,[],[f591,f73])).
% 1.92/0.64  fof(f591,plain,(
% 1.92/0.64    ( ! [X0,X1] : (~m1_pre_topc(X0,sK4) | k3_tmap_1(X1,sK3,sK4,X0,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK4,X1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.92/0.64    inference(subsumption_resolution,[],[f590,f76])).
% 1.92/0.64  fof(f590,plain,(
% 1.92/0.64    ( ! [X0,X1] : (~m1_pre_topc(X0,sK4) | k3_tmap_1(X1,sK3,sK4,X0,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0)) | ~v1_funct_1(sK5) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK4,X1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.92/0.64    inference(subsumption_resolution,[],[f585,f77])).
% 1.92/0.64  fof(f585,plain,(
% 1.92/0.64    ( ! [X0,X1] : (~m1_pre_topc(X0,sK4) | k3_tmap_1(X1,sK3,sK4,X0,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK5,u1_struct_0(X0)) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK5) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK4,X1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.92/0.64    inference(resolution,[],[f85,f78])).
% 1.92/0.64  fof(f85,plain,(
% 1.92/0.64    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.92/0.64    inference(cnf_transformation,[],[f28])).
% 1.92/0.64  fof(f28,plain,(
% 1.92/0.64    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.92/0.64    inference(flattening,[],[f27])).
% 1.92/0.64  fof(f27,plain,(
% 1.92/0.64    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.92/0.64    inference(ennf_transformation,[],[f10])).
% 1.92/0.64  fof(f10,axiom,(
% 1.92/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 1.92/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).
% 1.92/0.64  fof(f90,plain,(
% 1.92/0.64    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | sP0(X4,X3,X0,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.92/0.64    inference(cnf_transformation,[],[f54])).
% 1.92/0.64  fof(f54,plain,(
% 1.92/0.64    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | sP0(X4,X3,X0,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.92/0.64    inference(definition_folding,[],[f32,f53])).
% 1.92/0.64  fof(f32,plain,(
% 1.92/0.64    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.92/0.64    inference(flattening,[],[f31])).
% 1.92/0.64  fof(f31,plain,(
% 1.92/0.64    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : ((k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X1)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X1) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.92/0.64    inference(ennf_transformation,[],[f14])).
% 1.92/0.64  fof(f14,axiom,(
% 1.92/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => (r2_hidden(X5,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 1.92/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_tmap_1)).
% 1.92/0.64  fof(f1175,plain,(
% 1.92/0.64    ~spl7_38),
% 1.92/0.64    inference(avatar_contradiction_clause,[],[f1174])).
% 1.92/0.64  fof(f1174,plain,(
% 1.92/0.64    $false | ~spl7_38),
% 1.92/0.64    inference(subsumption_resolution,[],[f1148,f148])).
% 1.92/0.64  fof(f148,plain,(
% 1.92/0.64    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK5)),
% 1.92/0.64    inference(subsumption_resolution,[],[f147,f76])).
% 1.92/0.64  fof(f147,plain,(
% 1.92/0.64    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK5) | ~v1_funct_1(sK5)),
% 1.92/0.64    inference(subsumption_resolution,[],[f145,f77])).
% 1.92/0.64  fof(f145,plain,(
% 1.92/0.64    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK5) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK5)),
% 1.92/0.64    inference(resolution,[],[f109,f78])).
% 1.92/0.64  fof(f109,plain,(
% 1.92/0.64    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.92/0.64    inference(duplicate_literal_removal,[],[f108])).
% 1.92/0.64  fof(f108,plain,(
% 1.92/0.64    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.92/0.64    inference(equality_resolution,[],[f103])).
% 1.92/0.64  fof(f103,plain,(
% 1.92/0.64    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.92/0.64    inference(cnf_transformation,[],[f68])).
% 1.92/0.64  fof(f1148,plain,(
% 1.92/0.64    ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK5) | ~spl7_38),
% 1.92/0.64    inference(backward_demodulation,[],[f80,f1147])).
% 1.92/0.64  fof(f1147,plain,(
% 1.92/0.64    k4_tmap_1(sK3,sK4) = sK5 | ~spl7_38),
% 1.92/0.64    inference(subsumption_resolution,[],[f1146,f127])).
% 1.92/0.64  fof(f127,plain,(
% 1.92/0.64    sP1(sK3,sK4)),
% 1.92/0.64    inference(subsumption_resolution,[],[f126,f71])).
% 1.92/0.64  fof(f126,plain,(
% 1.92/0.64    sP1(sK3,sK4) | v2_struct_0(sK3)),
% 1.92/0.64    inference(subsumption_resolution,[],[f125,f72])).
% 1.92/0.64  fof(f125,plain,(
% 1.92/0.64    sP1(sK3,sK4) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.92/0.64    inference(subsumption_resolution,[],[f122,f73])).
% 1.92/0.64  fof(f122,plain,(
% 1.92/0.64    sP1(sK3,sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.92/0.64    inference(resolution,[],[f100,f75])).
% 1.92/0.64  fof(f100,plain,(
% 1.92/0.64    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | sP1(X0,X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.92/0.64    inference(cnf_transformation,[],[f56])).
% 1.92/0.64  fof(f56,plain,(
% 1.92/0.64    ! [X0,X1] : (sP1(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.92/0.64    inference(definition_folding,[],[f46,f55])).
% 1.92/0.64  fof(f55,plain,(
% 1.92/0.64    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~sP1(X0,X1))),
% 1.92/0.64    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.92/0.64  fof(f46,plain,(
% 1.92/0.64    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.92/0.64    inference(flattening,[],[f45])).
% 1.92/0.64  fof(f45,plain,(
% 1.92/0.64    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.92/0.64    inference(ennf_transformation,[],[f12])).
% 1.92/0.64  fof(f12,axiom,(
% 1.92/0.64    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))))),
% 1.92/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_tmap_1)).
% 1.92/0.64  fof(f1146,plain,(
% 1.92/0.64    k4_tmap_1(sK3,sK4) = sK5 | ~sP1(sK3,sK4) | ~spl7_38),
% 1.92/0.64    inference(subsumption_resolution,[],[f1145,f76])).
% 1.92/0.64  fof(f1145,plain,(
% 1.92/0.64    k4_tmap_1(sK3,sK4) = sK5 | ~v1_funct_1(sK5) | ~sP1(sK3,sK4) | ~spl7_38),
% 1.92/0.64    inference(subsumption_resolution,[],[f1144,f77])).
% 1.92/0.64  fof(f1144,plain,(
% 1.92/0.64    k4_tmap_1(sK3,sK4) = sK5 | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK5) | ~sP1(sK3,sK4) | ~spl7_38),
% 1.92/0.64    inference(subsumption_resolution,[],[f1142,f78])).
% 1.92/0.64  fof(f1142,plain,(
% 1.92/0.64    k4_tmap_1(sK3,sK4) = sK5 | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK5) | ~sP1(sK3,sK4) | ~spl7_38),
% 1.92/0.64    inference(resolution,[],[f1136,f236])).
% 1.92/0.64  fof(f236,plain,(
% 1.92/0.64    ( ! [X2,X3,X1] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,k4_tmap_1(X2,X1)) | k4_tmap_1(X2,X1) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~sP1(X2,X1)) )),
% 1.92/0.64    inference(subsumption_resolution,[],[f235,f97])).
% 1.92/0.64  fof(f97,plain,(
% 1.92/0.64    ( ! [X0,X1] : (v1_funct_1(k4_tmap_1(X0,X1)) | ~sP1(X0,X1)) )),
% 1.92/0.64    inference(cnf_transformation,[],[f67])).
% 1.92/0.64  fof(f67,plain,(
% 1.92/0.64    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~sP1(X0,X1))),
% 1.92/0.64    inference(nnf_transformation,[],[f55])).
% 1.92/0.64  fof(f235,plain,(
% 1.92/0.64    ( ! [X2,X3,X1] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,k4_tmap_1(X2,X1)) | k4_tmap_1(X2,X1) = X3 | ~v1_funct_1(k4_tmap_1(X2,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~sP1(X2,X1)) )),
% 1.92/0.64    inference(subsumption_resolution,[],[f231,f98])).
% 1.92/0.64  fof(f98,plain,(
% 1.92/0.64    ( ! [X0,X1] : (v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~sP1(X0,X1)) )),
% 1.92/0.64    inference(cnf_transformation,[],[f67])).
% 1.92/0.64  fof(f231,plain,(
% 1.92/0.64    ( ! [X2,X3,X1] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,k4_tmap_1(X2,X1)) | k4_tmap_1(X2,X1) = X3 | ~v1_funct_2(k4_tmap_1(X2,X1),u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(k4_tmap_1(X2,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~sP1(X2,X1)) )),
% 1.92/0.64    inference(resolution,[],[f102,f99])).
% 1.92/0.64  fof(f99,plain,(
% 1.92/0.64    ( ! [X0,X1] : (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~sP1(X0,X1)) )),
% 1.92/0.64    inference(cnf_transformation,[],[f67])).
% 1.92/0.64  fof(f1136,plain,(
% 1.92/0.64    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,k4_tmap_1(sK3,sK4)) | ~spl7_38),
% 1.92/0.64    inference(avatar_component_clause,[],[f1134])).
% 1.92/0.64  fof(f80,plain,(
% 1.92/0.64    ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k4_tmap_1(sK3,sK4),sK5)),
% 1.92/0.64    inference(cnf_transformation,[],[f62])).
% 1.92/0.64  fof(f384,plain,(
% 1.92/0.64    ~spl7_8 | spl7_11),
% 1.92/0.64    inference(avatar_split_clause,[],[f332,f381,f356])).
% 1.92/0.64  fof(f356,plain,(
% 1.92/0.64    spl7_8 <=> sP2(sK3,sK4,k4_tmap_1(sK3,sK4),sK4,sK3)),
% 1.92/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.92/0.64  fof(f332,plain,(
% 1.92/0.64    m1_subset_1(k4_tmap_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~sP2(sK3,sK4,k4_tmap_1(sK3,sK4),sK4,sK3)),
% 1.92/0.64    inference(superposition,[],[f106,f325])).
% 1.92/0.64  fof(f325,plain,(
% 1.92/0.64    k4_tmap_1(sK3,sK4) = k3_tmap_1(sK3,sK3,sK4,sK4,k4_tmap_1(sK3,sK4))),
% 1.92/0.64    inference(subsumption_resolution,[],[f324,f71])).
% 1.92/0.64  fof(f324,plain,(
% 1.92/0.64    v2_struct_0(sK3) | k4_tmap_1(sK3,sK4) = k3_tmap_1(sK3,sK3,sK4,sK4,k4_tmap_1(sK3,sK4))),
% 1.92/0.64    inference(subsumption_resolution,[],[f323,f72])).
% 1.92/0.64  fof(f323,plain,(
% 1.92/0.64    ~v2_pre_topc(sK3) | v2_struct_0(sK3) | k4_tmap_1(sK3,sK4) = k3_tmap_1(sK3,sK3,sK4,sK4,k4_tmap_1(sK3,sK4))),
% 1.92/0.64    inference(subsumption_resolution,[],[f320,f73])).
% 1.92/0.64  fof(f320,plain,(
% 1.92/0.64    ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | k4_tmap_1(sK3,sK4) = k3_tmap_1(sK3,sK3,sK4,sK4,k4_tmap_1(sK3,sK4))),
% 1.92/0.64    inference(resolution,[],[f317,f75])).
% 1.92/0.64  fof(f317,plain,(
% 1.92/0.64    ( ! [X0] : (~m1_pre_topc(sK4,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k4_tmap_1(sK3,sK4) = k3_tmap_1(X0,sK3,sK4,sK4,k4_tmap_1(sK3,sK4))) )),
% 1.92/0.64    inference(subsumption_resolution,[],[f316,f71])).
% 1.92/0.64  fof(f316,plain,(
% 1.92/0.64    ( ! [X0] : (~m1_pre_topc(sK4,X0) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k4_tmap_1(sK3,sK4) = k3_tmap_1(X0,sK3,sK4,sK4,k4_tmap_1(sK3,sK4))) )),
% 1.92/0.64    inference(subsumption_resolution,[],[f315,f72])).
% 1.92/0.64  fof(f315,plain,(
% 1.92/0.64    ( ! [X0] : (~m1_pre_topc(sK4,X0) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k4_tmap_1(sK3,sK4) = k3_tmap_1(X0,sK3,sK4,sK4,k4_tmap_1(sK3,sK4))) )),
% 1.92/0.64    inference(subsumption_resolution,[],[f314,f73])).
% 1.92/0.64  fof(f314,plain,(
% 1.92/0.64    ( ! [X0] : (~m1_pre_topc(sK4,X0) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k4_tmap_1(sK3,sK4) = k3_tmap_1(X0,sK3,sK4,sK4,k4_tmap_1(sK3,sK4))) )),
% 1.92/0.64    inference(subsumption_resolution,[],[f311,f74])).
% 1.92/0.64  fof(f311,plain,(
% 1.92/0.64    ( ! [X0] : (~m1_pre_topc(sK4,X0) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k4_tmap_1(sK3,sK4) = k3_tmap_1(X0,sK3,sK4,sK4,k4_tmap_1(sK3,sK4))) )),
% 1.92/0.64    inference(resolution,[],[f279,f127])).
% 1.92/0.64  fof(f279,plain,(
% 1.92/0.64    ( ! [X2,X3,X1] : (~sP1(X2,X3) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | k4_tmap_1(X2,X3) = k3_tmap_1(X1,X2,X3,X3,k4_tmap_1(X2,X3))) )),
% 1.92/0.64    inference(subsumption_resolution,[],[f278,f97])).
% 1.92/0.64  fof(f278,plain,(
% 1.92/0.64    ( ! [X2,X3,X1] : (k4_tmap_1(X2,X3) = k3_tmap_1(X1,X2,X3,X3,k4_tmap_1(X2,X3)) | ~v1_funct_1(k4_tmap_1(X2,X3)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~sP1(X2,X3)) )),
% 1.92/0.64    inference(subsumption_resolution,[],[f270,f98])).
% 1.92/0.64  fof(f270,plain,(
% 1.92/0.64    ( ! [X2,X3,X1] : (k4_tmap_1(X2,X3) = k3_tmap_1(X1,X2,X3,X3,k4_tmap_1(X2,X3)) | ~v1_funct_2(k4_tmap_1(X2,X3),u1_struct_0(X3),u1_struct_0(X2)) | ~v1_funct_1(k4_tmap_1(X2,X3)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~sP1(X2,X3)) )),
% 1.92/0.64    inference(resolution,[],[f268,f99])).
% 1.92/0.64  fof(f379,plain,(
% 1.92/0.64    ~spl7_8 | spl7_10),
% 1.92/0.64    inference(avatar_split_clause,[],[f331,f376,f356])).
% 1.92/0.64  fof(f331,plain,(
% 1.92/0.64    v1_funct_2(k4_tmap_1(sK3,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) | ~sP2(sK3,sK4,k4_tmap_1(sK3,sK4),sK4,sK3)),
% 1.92/0.64    inference(superposition,[],[f105,f325])).
% 1.92/0.64  fof(f371,plain,(
% 1.92/0.64    spl7_8),
% 1.92/0.64    inference(avatar_contradiction_clause,[],[f370])).
% 1.92/0.64  fof(f370,plain,(
% 1.92/0.64    $false | spl7_8),
% 1.92/0.64    inference(subsumption_resolution,[],[f369,f127])).
% 1.92/0.64  fof(f369,plain,(
% 1.92/0.64    ~sP1(sK3,sK4) | spl7_8),
% 1.92/0.64    inference(subsumption_resolution,[],[f368,f71])).
% 1.92/0.64  fof(f368,plain,(
% 1.92/0.64    v2_struct_0(sK3) | ~sP1(sK3,sK4) | spl7_8),
% 1.92/0.64    inference(subsumption_resolution,[],[f367,f72])).
% 1.92/0.64  fof(f367,plain,(
% 1.92/0.64    ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~sP1(sK3,sK4) | spl7_8),
% 1.92/0.64    inference(subsumption_resolution,[],[f366,f73])).
% 1.92/0.64  fof(f366,plain,(
% 1.92/0.64    ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~sP1(sK3,sK4) | spl7_8),
% 1.92/0.64    inference(subsumption_resolution,[],[f365,f75])).
% 1.92/0.64  fof(f365,plain,(
% 1.92/0.64    ~m1_pre_topc(sK4,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~sP1(sK3,sK4) | spl7_8),
% 1.92/0.64    inference(duplicate_literal_removal,[],[f364])).
% 1.92/0.64  fof(f364,plain,(
% 1.92/0.64    ~m1_pre_topc(sK4,sK3) | ~m1_pre_topc(sK4,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~sP1(sK3,sK4) | spl7_8),
% 1.92/0.64    inference(resolution,[],[f358,f255])).
% 1.92/0.64  fof(f255,plain,(
% 1.92/0.64    ( ! [X4,X2,X5,X3] : (sP2(X2,X3,k4_tmap_1(X2,X4),X4,X5) | ~m1_pre_topc(X3,X5) | ~m1_pre_topc(X4,X5) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5) | ~sP1(X2,X4)) )),
% 1.92/0.64    inference(subsumption_resolution,[],[f254,f97])).
% 1.92/0.64  fof(f254,plain,(
% 1.92/0.64    ( ! [X4,X2,X5,X3] : (sP2(X2,X3,k4_tmap_1(X2,X4),X4,X5) | ~v1_funct_1(k4_tmap_1(X2,X4)) | ~m1_pre_topc(X3,X5) | ~m1_pre_topc(X4,X5) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5) | ~sP1(X2,X4)) )),
% 1.92/0.64    inference(subsumption_resolution,[],[f247,f98])).
% 1.92/0.64  fof(f247,plain,(
% 1.92/0.64    ( ! [X4,X2,X5,X3] : (sP2(X2,X3,k4_tmap_1(X2,X4),X4,X5) | ~v1_funct_2(k4_tmap_1(X2,X4),u1_struct_0(X4),u1_struct_0(X2)) | ~v1_funct_1(k4_tmap_1(X2,X4)) | ~m1_pre_topc(X3,X5) | ~m1_pre_topc(X4,X5) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5) | ~sP1(X2,X4)) )),
% 1.92/0.64    inference(resolution,[],[f107,f99])).
% 1.92/0.64  fof(f358,plain,(
% 1.92/0.64    ~sP2(sK3,sK4,k4_tmap_1(sK3,sK4),sK4,sK3) | spl7_8),
% 1.92/0.64    inference(avatar_component_clause,[],[f356])).
% 1.92/0.64  fof(f363,plain,(
% 1.92/0.64    ~spl7_8 | spl7_9),
% 1.92/0.64    inference(avatar_split_clause,[],[f330,f360,f356])).
% 1.92/0.64  fof(f330,plain,(
% 1.92/0.64    v1_funct_1(k4_tmap_1(sK3,sK4)) | ~sP2(sK3,sK4,k4_tmap_1(sK3,sK4),sK4,sK3)),
% 1.92/0.64    inference(superposition,[],[f104,f325])).
% 1.92/0.64  fof(f208,plain,(
% 1.92/0.64    spl7_5 | spl7_3),
% 1.92/0.64    inference(avatar_split_clause,[],[f151,f173,f206])).
% 1.92/0.64  fof(f151,plain,(
% 1.92/0.64    ( ! [X2,X0,X3,X1] : (v1_xboole_0(u1_struct_0(sK4)) | ~sP0(X0,X1,X2,sK4,X3) | sK6(X0,X1,X2,sK4,X3) = k1_funct_1(sK5,sK6(X0,X1,X2,sK4,X3)) | ~m1_subset_1(sK6(X0,X1,X2,sK4,X3),u1_struct_0(sK3))) )),
% 1.92/0.64    inference(resolution,[],[f142,f79])).
% 1.92/0.64  fof(f79,plain,(
% 1.92/0.64    ( ! [X3] : (~r2_hidden(X3,u1_struct_0(sK4)) | k1_funct_1(sK5,X3) = X3 | ~m1_subset_1(X3,u1_struct_0(sK3))) )),
% 1.92/0.64    inference(cnf_transformation,[],[f62])).
% 1.92/0.64  fof(f183,plain,(
% 1.92/0.64    ~spl7_3),
% 1.92/0.64    inference(avatar_contradiction_clause,[],[f182])).
% 1.92/0.64  fof(f182,plain,(
% 1.92/0.64    $false | ~spl7_3),
% 1.92/0.64    inference(subsumption_resolution,[],[f181,f74])).
% 1.92/0.64  fof(f181,plain,(
% 1.92/0.64    v2_struct_0(sK4) | ~spl7_3),
% 1.92/0.64    inference(subsumption_resolution,[],[f180,f115])).
% 1.92/0.64  fof(f115,plain,(
% 1.92/0.64    l1_struct_0(sK4)),
% 1.92/0.64    inference(resolution,[],[f114,f81])).
% 1.92/0.64  fof(f81,plain,(
% 1.92/0.64    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.92/0.64    inference(cnf_transformation,[],[f22])).
% 1.92/0.64  fof(f22,plain,(
% 1.92/0.64    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.92/0.64    inference(ennf_transformation,[],[f5])).
% 1.92/0.64  fof(f5,axiom,(
% 1.92/0.64    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.92/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.92/0.64  fof(f180,plain,(
% 1.92/0.64    ~l1_struct_0(sK4) | v2_struct_0(sK4) | ~spl7_3),
% 1.92/0.64    inference(resolution,[],[f175,f84])).
% 1.92/0.64  fof(f84,plain,(
% 1.92/0.64    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.92/0.64    inference(cnf_transformation,[],[f26])).
% 1.92/0.64  fof(f26,plain,(
% 1.92/0.64    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.92/0.64    inference(flattening,[],[f25])).
% 1.92/0.64  fof(f25,plain,(
% 1.92/0.64    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.92/0.64    inference(ennf_transformation,[],[f7])).
% 1.92/0.64  fof(f7,axiom,(
% 1.92/0.64    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.92/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.92/0.64  fof(f175,plain,(
% 1.92/0.64    v1_xboole_0(u1_struct_0(sK4)) | ~spl7_3),
% 1.92/0.64    inference(avatar_component_clause,[],[f173])).
% 1.92/0.64  fof(f179,plain,(
% 1.92/0.64    spl7_3 | spl7_4),
% 1.92/0.64    inference(avatar_split_clause,[],[f167,f177,f173])).
% 1.92/0.64  fof(f167,plain,(
% 1.92/0.64    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK4)) | k1_funct_1(sK5,X0) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) | v1_xboole_0(u1_struct_0(sK4))) )),
% 1.92/0.64    inference(subsumption_resolution,[],[f166,f76])).
% 1.92/0.64  fof(f166,plain,(
% 1.92/0.64    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK4)) | k1_funct_1(sK5,X0) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) | ~v1_funct_1(sK5) | v1_xboole_0(u1_struct_0(sK4))) )),
% 1.92/0.64    inference(subsumption_resolution,[],[f163,f77])).
% 1.92/0.64  fof(f163,plain,(
% 1.92/0.64    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK4)) | k1_funct_1(sK5,X0) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X0) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK5) | v1_xboole_0(u1_struct_0(sK4))) )),
% 1.92/0.64    inference(resolution,[],[f101,f78])).
% 1.92/0.64  fof(f101,plain,(
% 1.92/0.64    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 1.92/0.64    inference(cnf_transformation,[],[f48])).
% 1.92/0.64  fof(f48,plain,(
% 1.92/0.64    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 1.92/0.64    inference(flattening,[],[f47])).
% 1.92/0.64  fof(f47,plain,(
% 1.92/0.64    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 1.92/0.64    inference(ennf_transformation,[],[f2])).
% 1.92/0.64  fof(f2,axiom,(
% 1.92/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 1.92/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 1.92/0.64  % SZS output end Proof for theBenchmark
% 1.92/0.64  % (21275)------------------------------
% 1.92/0.64  % (21275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.92/0.64  % (21275)Termination reason: Refutation
% 1.92/0.64  
% 1.92/0.64  % (21275)Memory used [KB]: 11769
% 1.92/0.64  % (21275)Time elapsed: 0.218 s
% 1.92/0.64  % (21275)------------------------------
% 1.92/0.64  % (21275)------------------------------
% 1.92/0.64  % (21249)Success in time 0.279 s
%------------------------------------------------------------------------------
