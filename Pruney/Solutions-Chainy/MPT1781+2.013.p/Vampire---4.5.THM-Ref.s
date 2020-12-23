%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :  233 (1130 expanded)
%              Number of leaves         :   29 ( 406 expanded)
%              Depth                    :   27
%              Number of atoms          : 1275 (10967 expanded)
%              Number of equality atoms :  116 (1058 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1083,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f158,f261,f264,f267,f371,f531,f899,f925,f972,f1082])).

fof(f1082,plain,
    ( ~ spl7_3
    | ~ spl7_11 ),
    inference(avatar_contradiction_clause,[],[f1081])).

fof(f1081,plain,
    ( $false
    | ~ spl7_3
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f154,f1012])).

fof(f1012,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f645,f96])).

fof(f96,plain,(
    l1_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f93,f59])).

fof(f59,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f17,f47,f46,f45])).

fof(f45,plain,
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

fof(f46,plain,
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

fof(f47,plain,
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

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_tmap_1)).

fof(f93,plain,
    ( l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f69,f61])).

fof(f61,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f645,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ spl7_11 ),
    inference(duplicate_literal_removal,[],[f644])).

fof(f644,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ spl7_11 ),
    inference(resolution,[],[f601,f68])).

fof(f68,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f601,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK4,X0)
        | ~ v1_xboole_0(u1_struct_0(X0))
        | ~ l1_pre_topc(X0) )
    | ~ spl7_11 ),
    inference(resolution,[],[f526,f121])).

fof(f121,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4)
      | ~ l1_pre_topc(X5)
      | ~ v1_xboole_0(u1_struct_0(X5))
      | ~ m1_pre_topc(X4,X5) ) ),
    inference(resolution,[],[f72,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | ~ v1_xboole_0(u1_struct_0(X1))
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(resolution,[],[f70,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK6(X0,X1,X2,X3,X4),u1_struct_0(X4))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X2),X1,sK6(X0,X1,X2,X3,X4)) != k1_funct_1(X0,sK6(X0,X1,X2,X3,X4))
        & r2_hidden(sK6(X0,X1,X2,X3,X4),u1_struct_0(X4))
        & m1_subset_1(sK6(X0,X1,X2,X3,X4),u1_struct_0(X3)) )
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f50,f51])).

fof(f51,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X2),X1,X5) != k1_funct_1(X0,X5)
          & r2_hidden(X5,u1_struct_0(X4))
          & m1_subset_1(X5,u1_struct_0(X3)) )
     => ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X2),X1,sK6(X0,X1,X2,X3,X4)) != k1_funct_1(X0,sK6(X0,X1,X2,X3,X4))
        & r2_hidden(sK6(X0,X1,X2,X3,X4),u1_struct_0(X4))
        & m1_subset_1(sK6(X0,X1,X2,X3,X4),u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ? [X5] :
          ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X2),X1,X5) != k1_funct_1(X0,X5)
          & r2_hidden(X5,u1_struct_0(X4))
          & m1_subset_1(X5,u1_struct_0(X3)) )
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X4,X3,X0,X1,X2] :
      ( ? [X5] :
          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
          & r2_hidden(X5,u1_struct_0(X2))
          & m1_subset_1(X5,u1_struct_0(X1)) )
      | ~ sP0(X4,X3,X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X4,X3,X0,X1,X2] :
      ( ? [X5] :
          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
          & r2_hidden(X5,u1_struct_0(X2))
          & m1_subset_1(X5,u1_struct_0(X1)) )
      | ~ sP0(X4,X3,X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f526,plain,
    ( sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f524])).

fof(f524,plain,
    ( spl7_11
  <=> sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f154,plain,
    ( v1_xboole_0(u1_struct_0(sK4))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl7_3
  <=> v1_xboole_0(u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f972,plain,
    ( ~ spl7_4
    | ~ spl7_8 ),
    inference(avatar_contradiction_clause,[],[f971])).

fof(f971,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f970,f260])).

fof(f260,plain,
    ( sP0(sK5,sK5,sK3,sK4,sK4)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f258])).

fof(f258,plain,
    ( spl7_8
  <=> sP0(sK5,sK5,sK3,sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f970,plain,
    ( ~ sP0(sK5,sK5,sK3,sK4,sK4)
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f969,f350])).

fof(f350,plain,
    ( sK6(sK5,sK5,sK3,sK4,sK4) = k1_funct_1(sK5,sK6(sK5,sK5,sK3,sK4,sK4))
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f349,f61])).

fof(f349,plain,
    ( ~ m1_pre_topc(sK4,sK3)
    | sK6(sK5,sK5,sK3,sK4,sK4) = k1_funct_1(sK5,sK6(sK5,sK5,sK3,sK4,sK4))
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f337,f60])).

fof(f60,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f337,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK3)
    | sK6(sK5,sK5,sK3,sK4,sK4) = k1_funct_1(sK5,sK6(sK5,sK5,sK3,sK4,sK4))
    | ~ spl7_8 ),
    inference(resolution,[],[f260,f195])).

fof(f195,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X1,X2,X3,X0,sK4)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK3)
      | sK6(X1,X2,X3,X0,sK4) = k1_funct_1(sK5,sK6(X1,X2,X3,X0,sK4)) ) ),
    inference(duplicate_literal_removal,[],[f194])).

fof(f194,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ sP0(X1,X2,X3,X0,sK4)
      | ~ m1_pre_topc(X0,sK3)
      | sK6(X1,X2,X3,X0,sK4) = k1_funct_1(sK5,sK6(X1,X2,X3,X0,sK4))
      | ~ sP0(X1,X2,X3,X0,sK4) ) ),
    inference(resolution,[],[f137,f72])).

fof(f137,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(sK6(X1,X2,X3,X0,X4),u1_struct_0(sK4))
      | v2_struct_0(X0)
      | ~ sP0(X1,X2,X3,X0,X4)
      | ~ m1_pre_topc(X0,sK3)
      | sK6(X1,X2,X3,X0,X4) = k1_funct_1(sK5,sK6(X1,X2,X3,X0,X4)) ) ),
    inference(subsumption_resolution,[],[f136,f57])).

fof(f57,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f136,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_pre_topc(X0,sK3)
      | v2_struct_0(X0)
      | v2_struct_0(sK3)
      | ~ sP0(X1,X2,X3,X0,X4)
      | ~ r2_hidden(sK6(X1,X2,X3,X0,X4),u1_struct_0(sK4))
      | sK6(X1,X2,X3,X0,X4) = k1_funct_1(sK5,sK6(X1,X2,X3,X0,X4)) ) ),
    inference(subsumption_resolution,[],[f133,f59])).

fof(f133,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_pre_topc(X0,sK3)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ sP0(X1,X2,X3,X0,X4)
      | ~ r2_hidden(sK6(X1,X2,X3,X0,X4),u1_struct_0(sK4))
      | sK6(X1,X2,X3,X0,X4) = k1_funct_1(sK5,sK6(X1,X2,X3,X0,X4)) ) ),
    inference(resolution,[],[f122,f65])).

fof(f65,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK3))
      | ~ r2_hidden(X3,u1_struct_0(sK4))
      | k1_funct_1(sK5,X3) = X3 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f122,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3,X4),u1_struct_0(X5))
      | ~ m1_pre_topc(X3,X5)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(resolution,[],[f76,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3,X4),u1_struct_0(X3))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f969,plain,
    ( sK6(sK5,sK5,sK3,sK4,sK4) != k1_funct_1(sK5,sK6(sK5,sK5,sK3,sK4,sK4))
    | ~ sP0(sK5,sK5,sK3,sK4,sK4)
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(superposition,[],[f73,f964])).

fof(f964,plain,
    ( sK6(sK5,sK5,sK3,sK4,sK4) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK6(sK5,sK5,sK3,sK4,sK4))
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(forward_demodulation,[],[f951,f350])).

fof(f951,plain,
    ( k1_funct_1(sK5,sK6(sK5,sK5,sK3,sK4,sK4)) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK6(sK5,sK5,sK3,sK4,sK4))
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(resolution,[],[f260,f631])).

fof(f631,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ sP0(X0,X1,X2,sK4,X3)
        | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK6(X0,X1,X2,sK4,X3)) = k1_funct_1(sK5,sK6(X0,X1,X2,sK4,X3)) )
    | ~ spl7_4 ),
    inference(resolution,[],[f157,f71])).

fof(f157,plain,
    ( ! [X8] :
        ( ~ m1_subset_1(X8,u1_struct_0(sK4))
        | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X8) = k1_funct_1(sK5,X8) )
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl7_4
  <=> ! [X8] :
        ( ~ m1_subset_1(X8,u1_struct_0(sK4))
        | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X8) = k1_funct_1(sK5,X8) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X2),X1,sK6(X0,X1,X2,X3,X4)) != k1_funct_1(X0,sK6(X0,X1,X2,X3,X4))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f925,plain,(
    ~ spl7_12 ),
    inference(avatar_contradiction_clause,[],[f924])).

fof(f924,plain,
    ( $false
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f912,f132])).

fof(f132,plain,(
    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK5) ),
    inference(subsumption_resolution,[],[f131,f62])).

fof(f62,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f131,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK5)
    | ~ v1_funct_1(sK5) ),
    inference(subsumption_resolution,[],[f126,f63])).

fof(f63,plain,(
    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f48])).

fof(f126,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK5) ),
    inference(resolution,[],[f91,f64])).

fof(f64,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f48])).

fof(f91,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f90])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f912,plain,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK5)
    | ~ spl7_12 ),
    inference(backward_demodulation,[],[f66,f530])).

fof(f530,plain,
    ( k4_tmap_1(sK3,sK4) = sK5
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f528])).

fof(f528,plain,
    ( spl7_12
  <=> k4_tmap_1(sK3,sK4) = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f66,plain,(
    ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k4_tmap_1(sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f899,plain,
    ( ~ spl7_4
    | ~ spl7_11 ),
    inference(avatar_contradiction_clause,[],[f898])).

fof(f898,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f897,f755])).

fof(f755,plain,
    ( sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) != k1_funct_1(k4_tmap_1(sK3,sK4),sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4))
    | ~ spl7_4
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f754,f526])).

fof(f754,plain,
    ( sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) != k1_funct_1(k4_tmap_1(sK3,sK4),sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4))
    | ~ sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)
    | ~ spl7_4
    | ~ spl7_11 ),
    inference(superposition,[],[f73,f713])).

fof(f713,plain,
    ( sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4))
    | ~ spl7_4
    | ~ spl7_11 ),
    inference(forward_demodulation,[],[f712,f613])).

fof(f613,plain,
    ( sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k1_funct_1(sK5,sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4))
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f612,f61])).

fof(f612,plain,
    ( ~ m1_pre_topc(sK4,sK3)
    | sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k1_funct_1(sK5,sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4))
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f600,f60])).

fof(f600,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK3)
    | sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k1_funct_1(sK5,sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4))
    | ~ spl7_11 ),
    inference(resolution,[],[f526,f195])).

fof(f712,plain,
    ( k1_funct_1(sK5,sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4))
    | ~ spl7_4
    | ~ spl7_11 ),
    inference(resolution,[],[f631,f526])).

fof(f897,plain,
    ( sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k1_funct_1(k4_tmap_1(sK3,sK4),sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4))
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f896,f57])).

fof(f896,plain,
    ( v2_struct_0(sK3)
    | sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k1_funct_1(k4_tmap_1(sK3,sK4),sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4))
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f895,f58])).

fof(f58,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f895,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k1_funct_1(k4_tmap_1(sK3,sK4),sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4))
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f891,f59])).

fof(f891,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k1_funct_1(k4_tmap_1(sK3,sK4),sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4))
    | ~ spl7_11 ),
    inference(resolution,[],[f630,f61])).

fof(f630,plain,
    ( ! [X8] :
        ( ~ m1_pre_topc(sK4,X8)
        | ~ l1_pre_topc(X8)
        | ~ v2_pre_topc(X8)
        | v2_struct_0(X8)
        | sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k1_funct_1(k4_tmap_1(X8,sK4),sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)) )
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f610,f60])).

fof(f610,plain,
    ( ! [X8] :
        ( ~ m1_pre_topc(sK4,X8)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(X8)
        | ~ v2_pre_topc(X8)
        | v2_struct_0(X8)
        | sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k1_funct_1(k4_tmap_1(X8,sK4),sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)) )
    | ~ spl7_11 ),
    inference(duplicate_literal_removal,[],[f609])).

fof(f609,plain,
    ( ! [X8] :
        ( ~ m1_pre_topc(sK4,X8)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(X8)
        | ~ v2_pre_topc(X8)
        | v2_struct_0(X8)
        | ~ m1_pre_topc(sK4,X8)
        | v2_struct_0(sK4)
        | sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k1_funct_1(k4_tmap_1(X8,sK4),sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)) )
    | ~ spl7_11 ),
    inference(resolution,[],[f526,f216])).

fof(f216,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4)
      | ~ m1_pre_topc(X4,X5)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X3,X5)
      | v2_struct_0(X3)
      | sK6(X0,X1,X2,X3,X4) = k1_funct_1(k4_tmap_1(X5,X4),sK6(X0,X1,X2,X3,X4)) ) ),
    inference(duplicate_literal_removal,[],[f215])).

fof(f215,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sK6(X0,X1,X2,X3,X4) = k1_funct_1(k4_tmap_1(X5,X4),sK6(X0,X1,X2,X3,X4))
      | ~ m1_pre_topc(X4,X5)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X3,X5)
      | v2_struct_0(X3)
      | ~ sP0(X0,X1,X2,X3,X4)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(resolution,[],[f141,f72])).

fof(f141,plain,(
    ! [X6,X12,X10,X8,X7,X11,X9] :
      ( ~ r2_hidden(sK6(X6,X7,X8,X9,X10),u1_struct_0(X11))
      | sK6(X6,X7,X8,X9,X10) = k1_funct_1(k4_tmap_1(X12,X11),sK6(X6,X7,X8,X9,X10))
      | ~ m1_pre_topc(X11,X12)
      | v2_struct_0(X11)
      | ~ l1_pre_topc(X12)
      | ~ v2_pre_topc(X12)
      | v2_struct_0(X12)
      | ~ m1_pre_topc(X9,X12)
      | v2_struct_0(X9)
      | ~ sP0(X6,X7,X8,X9,X10) ) ),
    inference(duplicate_literal_removal,[],[f140])).

fof(f140,plain,(
    ! [X6,X12,X10,X8,X7,X11,X9] :
      ( ~ r2_hidden(sK6(X6,X7,X8,X9,X10),u1_struct_0(X11))
      | sK6(X6,X7,X8,X9,X10) = k1_funct_1(k4_tmap_1(X12,X11),sK6(X6,X7,X8,X9,X10))
      | ~ m1_pre_topc(X11,X12)
      | v2_struct_0(X11)
      | ~ l1_pre_topc(X12)
      | ~ v2_pre_topc(X12)
      | v2_struct_0(X12)
      | ~ m1_pre_topc(X9,X12)
      | v2_struct_0(X9)
      | ~ l1_pre_topc(X12)
      | v2_struct_0(X12)
      | ~ sP0(X6,X7,X8,X9,X10) ) ),
    inference(resolution,[],[f75,f122])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,u1_struct_0(X1))
      | k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_tmap_1)).

fof(f531,plain,
    ( spl7_11
    | spl7_12
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f476,f254,f250,f528,f524])).

fof(f250,plain,
    ( spl7_6
  <=> sK5 = k2_tmap_1(sK4,sK3,sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f254,plain,
    ( spl7_7
  <=> m1_pre_topc(sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f476,plain,
    ( k4_tmap_1(sK3,sK4) = sK5
    | sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f475,f118])).

fof(f118,plain,(
    sP1(sK3,sK4) ),
    inference(subsumption_resolution,[],[f117,f57])).

fof(f117,plain,
    ( sP1(sK3,sK4)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f116,f58])).

fof(f116,plain,
    ( sP1(sK3,sK4)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f113,f59])).

fof(f113,plain,
    ( sP1(sK3,sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f81,f61])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | sP1(X0,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f31,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_tmap_1)).

fof(f475,plain,
    ( k4_tmap_1(sK3,sK4) = sK5
    | sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)
    | ~ sP1(sK3,sK4)
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f474,f57])).

fof(f474,plain,
    ( v2_struct_0(sK3)
    | k4_tmap_1(sK3,sK4) = sK5
    | sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)
    | ~ sP1(sK3,sK4)
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f473,f58])).

fof(f473,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | k4_tmap_1(sK3,sK4) = sK5
    | sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)
    | ~ sP1(sK3,sK4)
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f472,f59])).

fof(f472,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | k4_tmap_1(sK3,sK4) = sK5
    | sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)
    | ~ sP1(sK3,sK4)
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f471,f102])).

fof(f102,plain,(
    v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f101,f58])).

fof(f101,plain,
    ( v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f98,f59])).

fof(f98,plain,
    ( v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(resolution,[],[f77,f61])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f471,plain,
    ( ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | k4_tmap_1(sK3,sK4) = sK5
    | sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)
    | ~ sP1(sK3,sK4)
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f470,f96])).

fof(f470,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | k4_tmap_1(sK3,sK4) = sK5
    | sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)
    | ~ sP1(sK3,sK4)
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f469,f60])).

fof(f469,plain,
    ( v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | k4_tmap_1(sK3,sK4) = sK5
    | sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)
    | ~ sP1(sK3,sK4)
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f468,f255])).

fof(f255,plain,
    ( m1_pre_topc(sK4,sK4)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f254])).

fof(f468,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | k4_tmap_1(sK3,sK4) = sK5
    | sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)
    | ~ sP1(sK3,sK4)
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f467,f62])).

fof(f467,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_pre_topc(sK4,sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | k4_tmap_1(sK3,sK4) = sK5
    | sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)
    | ~ sP1(sK3,sK4)
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f466,f63])).

fof(f466,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK5)
    | ~ m1_pre_topc(sK4,sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | k4_tmap_1(sK3,sK4) = sK5
    | sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)
    | ~ sP1(sK3,sK4)
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f463,f64])).

fof(f463,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK5)
    | ~ m1_pre_topc(sK4,sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | k4_tmap_1(sK3,sK4) = sK5
    | sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)
    | ~ sP1(sK3,sK4)
    | ~ spl7_6 ),
    inference(duplicate_literal_removal,[],[f458])).

fof(f458,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
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
    | v2_struct_0(sK3)
    | k4_tmap_1(sK3,sK4) = sK5
    | sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)
    | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK5)
    | ~ sP1(sK3,sK4)
    | ~ spl7_6 ),
    inference(superposition,[],[f229,f252])).

fof(f252,plain,
    ( sK5 = k2_tmap_1(sK4,sK3,sK5,sK4)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f250])).

fof(f229,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ m1_subset_1(k2_tmap_1(X5,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2))))
      | ~ v1_funct_2(X4,u1_struct_0(X5),u1_struct_0(X2))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X5)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | k4_tmap_1(X2,X3) = k2_tmap_1(X5,X2,X4,X3)
      | sP0(k4_tmap_1(X2,X3),X4,X2,X5,X3)
      | ~ v1_funct_2(k2_tmap_1(X5,X2,X4,X3),u1_struct_0(X3),u1_struct_0(X2))
      | ~ v1_funct_1(k2_tmap_1(X5,X2,X4,X3))
      | ~ sP1(X2,X3) ) ),
    inference(subsumption_resolution,[],[f228,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k4_tmap_1(X0,X1))
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f228,plain,(
    ! [X4,X2,X5,X3] :
      ( sP0(k4_tmap_1(X2,X3),X4,X2,X5,X3)
      | ~ v1_funct_1(k4_tmap_1(X2,X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2))))
      | ~ v1_funct_2(X4,u1_struct_0(X5),u1_struct_0(X2))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X5)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | k4_tmap_1(X2,X3) = k2_tmap_1(X5,X2,X4,X3)
      | ~ m1_subset_1(k2_tmap_1(X5,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
      | ~ v1_funct_2(k2_tmap_1(X5,X2,X4,X3),u1_struct_0(X3),u1_struct_0(X2))
      | ~ v1_funct_1(k2_tmap_1(X5,X2,X4,X3))
      | ~ sP1(X2,X3) ) ),
    inference(subsumption_resolution,[],[f227,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f227,plain,(
    ! [X4,X2,X5,X3] :
      ( sP0(k4_tmap_1(X2,X3),X4,X2,X5,X3)
      | ~ v1_funct_2(k4_tmap_1(X2,X3),u1_struct_0(X3),u1_struct_0(X2))
      | ~ v1_funct_1(k4_tmap_1(X2,X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2))))
      | ~ v1_funct_2(X4,u1_struct_0(X5),u1_struct_0(X2))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X5)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | k4_tmap_1(X2,X3) = k2_tmap_1(X5,X2,X4,X3)
      | ~ m1_subset_1(k2_tmap_1(X5,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
      | ~ v1_funct_2(k2_tmap_1(X5,X2,X4,X3),u1_struct_0(X3),u1_struct_0(X2))
      | ~ v1_funct_1(k2_tmap_1(X5,X2,X4,X3))
      | ~ sP1(X2,X3) ) ),
    inference(subsumption_resolution,[],[f218,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f218,plain,(
    ! [X4,X2,X5,X3] :
      ( sP0(k4_tmap_1(X2,X3),X4,X2,X5,X3)
      | ~ m1_subset_1(k4_tmap_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
      | ~ v1_funct_2(k4_tmap_1(X2,X3),u1_struct_0(X3),u1_struct_0(X2))
      | ~ v1_funct_1(k4_tmap_1(X2,X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2))))
      | ~ v1_funct_2(X4,u1_struct_0(X5),u1_struct_0(X2))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X5)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | k4_tmap_1(X2,X3) = k2_tmap_1(X5,X2,X4,X3)
      | ~ m1_subset_1(k2_tmap_1(X5,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
      | ~ v1_funct_2(k2_tmap_1(X5,X2,X4,X3),u1_struct_0(X3),u1_struct_0(X2))
      | ~ v1_funct_1(k2_tmap_1(X5,X2,X4,X3))
      | ~ sP1(X2,X3) ) ),
    inference(resolution,[],[f74,f178])).

fof(f178,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_funct_2(u1_struct_0(X5),u1_struct_0(X6),X7,k4_tmap_1(X6,X5))
      | k4_tmap_1(X6,X5) = X7
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X6))))
      | ~ v1_funct_2(X7,u1_struct_0(X5),u1_struct_0(X6))
      | ~ v1_funct_1(X7)
      | ~ sP1(X6,X5) ) ),
    inference(subsumption_resolution,[],[f177,f78])).

fof(f177,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_funct_2(u1_struct_0(X5),u1_struct_0(X6),X7,k4_tmap_1(X6,X5))
      | k4_tmap_1(X6,X5) = X7
      | ~ v1_funct_1(k4_tmap_1(X6,X5))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X6))))
      | ~ v1_funct_2(X7,u1_struct_0(X5),u1_struct_0(X6))
      | ~ v1_funct_1(X7)
      | ~ sP1(X6,X5) ) ),
    inference(subsumption_resolution,[],[f173,f79])).

fof(f173,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_funct_2(u1_struct_0(X5),u1_struct_0(X6),X7,k4_tmap_1(X6,X5))
      | k4_tmap_1(X6,X5) = X7
      | ~ v1_funct_2(k4_tmap_1(X6,X5),u1_struct_0(X5),u1_struct_0(X6))
      | ~ v1_funct_1(k4_tmap_1(X6,X5))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X6))))
      | ~ v1_funct_2(X7,u1_struct_0(X5),u1_struct_0(X6))
      | ~ v1_funct_1(X7)
      | ~ sP1(X6,X5) ) ),
    inference(resolution,[],[f88,f80])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f74,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(definition_folding,[],[f23,f39])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tmap_1)).

fof(f371,plain,
    ( ~ spl7_3
    | ~ spl7_8 ),
    inference(avatar_contradiction_clause,[],[f370])).

fof(f370,plain,
    ( $false
    | ~ spl7_3
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f369,f96])).

fof(f369,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ spl7_3
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f364,f154])).

fof(f364,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ spl7_8 ),
    inference(duplicate_literal_removal,[],[f363])).

fof(f363,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ spl7_8 ),
    inference(resolution,[],[f338,f68])).

fof(f338,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK4,X0)
        | ~ v1_xboole_0(u1_struct_0(X0))
        | ~ l1_pre_topc(X0) )
    | ~ spl7_8 ),
    inference(resolution,[],[f260,f121])).

fof(f267,plain,(
    spl7_7 ),
    inference(avatar_contradiction_clause,[],[f266])).

fof(f266,plain,
    ( $false
    | spl7_7 ),
    inference(subsumption_resolution,[],[f265,f96])).

fof(f265,plain,
    ( ~ l1_pre_topc(sK4)
    | spl7_7 ),
    inference(resolution,[],[f256,f68])).

fof(f256,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f254])).

fof(f264,plain,(
    spl7_5 ),
    inference(avatar_contradiction_clause,[],[f263])).

fof(f263,plain,
    ( $false
    | spl7_5 ),
    inference(subsumption_resolution,[],[f262,f97])).

fof(f97,plain,(
    l1_struct_0(sK4) ),
    inference(resolution,[],[f96,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f262,plain,
    ( ~ l1_struct_0(sK4)
    | spl7_5 ),
    inference(resolution,[],[f248,f171])).

fof(f171,plain,(
    ! [X8] :
      ( sP2(sK3,X8,sK5,sK4)
      | ~ l1_struct_0(X8) ) ),
    inference(subsumption_resolution,[],[f170,f97])).

fof(f170,plain,(
    ! [X8] :
      ( ~ l1_struct_0(X8)
      | sP2(sK3,X8,sK5,sK4)
      | ~ l1_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f169,f92])).

fof(f92,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f67,f59])).

fof(f169,plain,(
    ! [X8] :
      ( ~ l1_struct_0(X8)
      | sP2(sK3,X8,sK5,sK4)
      | ~ l1_struct_0(sK3)
      | ~ l1_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f168,f62])).

fof(f168,plain,(
    ! [X8] :
      ( ~ l1_struct_0(X8)
      | sP2(sK3,X8,sK5,sK4)
      | ~ v1_funct_1(sK5)
      | ~ l1_struct_0(sK3)
      | ~ l1_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f163,f63])).

fof(f163,plain,(
    ! [X8] :
      ( ~ l1_struct_0(X8)
      | sP2(sK3,X8,sK5,sK4)
      | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(sK5)
      | ~ l1_struct_0(sK3)
      | ~ l1_struct_0(sK4) ) ),
    inference(resolution,[],[f87,f64])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | sP2(X1,X3,X2,X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( sP2(X1,X3,X2,X0)
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(definition_folding,[],[f36,f43])).

fof(f43,plain,(
    ! [X1,X3,X2,X0] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ sP2(X1,X3,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( l1_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(f248,plain,
    ( ~ sP2(sK3,sK4,sK5,sK4)
    | spl7_5 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl7_5
  <=> sP2(sK3,sK4,sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f261,plain,
    ( ~ spl7_5
    | spl7_6
    | ~ spl7_7
    | spl7_8 ),
    inference(avatar_split_clause,[],[f244,f258,f254,f250,f246])).

fof(f244,plain,
    ( sP0(sK5,sK5,sK3,sK4,sK4)
    | ~ m1_pre_topc(sK4,sK4)
    | sK5 = k2_tmap_1(sK4,sK3,sK5,sK4)
    | ~ sP2(sK3,sK4,sK5,sK4) ),
    inference(subsumption_resolution,[],[f243,f60])).

fof(f243,plain,
    ( sP0(sK5,sK5,sK3,sK4,sK4)
    | ~ m1_pre_topc(sK4,sK4)
    | v2_struct_0(sK4)
    | sK5 = k2_tmap_1(sK4,sK3,sK5,sK4)
    | ~ sP2(sK3,sK4,sK5,sK4) ),
    inference(subsumption_resolution,[],[f242,f102])).

fof(f242,plain,
    ( sP0(sK5,sK5,sK3,sK4,sK4)
    | ~ m1_pre_topc(sK4,sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | sK5 = k2_tmap_1(sK4,sK3,sK5,sK4)
    | ~ sP2(sK3,sK4,sK5,sK4) ),
    inference(subsumption_resolution,[],[f241,f96])).

fof(f241,plain,
    ( sP0(sK5,sK5,sK3,sK4,sK4)
    | ~ m1_pre_topc(sK4,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | sK5 = k2_tmap_1(sK4,sK3,sK5,sK4)
    | ~ sP2(sK3,sK4,sK5,sK4) ),
    inference(subsumption_resolution,[],[f240,f62])).

fof(f240,plain,
    ( sP0(sK5,sK5,sK3,sK4,sK4)
    | ~ v1_funct_1(sK5)
    | ~ m1_pre_topc(sK4,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | sK5 = k2_tmap_1(sK4,sK3,sK5,sK4)
    | ~ sP2(sK3,sK4,sK5,sK4) ),
    inference(subsumption_resolution,[],[f235,f63])).

fof(f235,plain,
    ( sP0(sK5,sK5,sK3,sK4,sK4)
    | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(sK5)
    | ~ m1_pre_topc(sK4,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | sK5 = k2_tmap_1(sK4,sK3,sK5,sK4)
    | ~ sP2(sK3,sK4,sK5,sK4) ),
    inference(resolution,[],[f226,f64])).

fof(f226,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
      | sP0(sK5,X0,sK3,X1,sK4)
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK4,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | sK5 = k2_tmap_1(X1,sK3,X0,sK4)
      | ~ sP2(sK3,sK4,X0,X1) ) ),
    inference(subsumption_resolution,[],[f225,f57])).

fof(f225,plain,(
    ! [X0,X1] :
      ( sP0(sK5,X0,sK3,X1,sK4)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK4,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | v2_struct_0(sK3)
      | sK5 = k2_tmap_1(X1,sK3,X0,sK4)
      | ~ sP2(sK3,sK4,X0,X1) ) ),
    inference(subsumption_resolution,[],[f224,f58])).

fof(f224,plain,(
    ! [X0,X1] :
      ( sP0(sK5,X0,sK3,X1,sK4)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK4,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | sK5 = k2_tmap_1(X1,sK3,X0,sK4)
      | ~ sP2(sK3,sK4,X0,X1) ) ),
    inference(subsumption_resolution,[],[f223,f59])).

fof(f223,plain,(
    ! [X0,X1] :
      ( sP0(sK5,X0,sK3,X1,sK4)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK4,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | sK5 = k2_tmap_1(X1,sK3,X0,sK4)
      | ~ sP2(sK3,sK4,X0,X1) ) ),
    inference(subsumption_resolution,[],[f222,f60])).

fof(f222,plain,(
    ! [X0,X1] :
      ( sP0(sK5,X0,sK3,X1,sK4)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK4,X1)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | sK5 = k2_tmap_1(X1,sK3,X0,sK4)
      | ~ sP2(sK3,sK4,X0,X1) ) ),
    inference(subsumption_resolution,[],[f221,f62])).

fof(f221,plain,(
    ! [X0,X1] :
      ( sP0(sK5,X0,sK3,X1,sK4)
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK4,X1)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | sK5 = k2_tmap_1(X1,sK3,X0,sK4)
      | ~ sP2(sK3,sK4,X0,X1) ) ),
    inference(subsumption_resolution,[],[f220,f63])).

fof(f220,plain,(
    ! [X0,X1] :
      ( sP0(sK5,X0,sK3,X1,sK4)
      | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK4,X1)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | sK5 = k2_tmap_1(X1,sK3,X0,sK4)
      | ~ sP2(sK3,sK4,X0,X1) ) ),
    inference(subsumption_resolution,[],[f217,f64])).

fof(f217,plain,(
    ! [X0,X1] :
      ( sP0(sK5,X0,sK3,X1,sK4)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
      | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3))
      | ~ v1_funct_1(X0)
      | ~ m1_pre_topc(sK4,X1)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | sK5 = k2_tmap_1(X1,sK3,X0,sK4)
      | ~ sP2(sK3,sK4,X0,X1) ) ),
    inference(resolution,[],[f74,f185])).

fof(f185,plain,(
    ! [X0,X1] :
      ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(X0,sK3,X1,sK4),sK5)
      | sK5 = k2_tmap_1(X0,sK3,X1,sK4)
      | ~ sP2(sK3,sK4,X1,X0) ) ),
    inference(subsumption_resolution,[],[f184,f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) )
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X1,X3,X2,X0] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ sP2(X1,X3,X2,X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f184,plain,(
    ! [X0,X1] :
      ( sK5 = k2_tmap_1(X0,sK3,X1,sK4)
      | ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(X0,sK3,X1,sK4),sK5)
      | ~ v1_funct_1(k2_tmap_1(X0,sK3,X1,sK4))
      | ~ sP2(sK3,sK4,X1,X0) ) ),
    inference(subsumption_resolution,[],[f181,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f181,plain,(
    ! [X0,X1] :
      ( sK5 = k2_tmap_1(X0,sK3,X1,sK4)
      | ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(X0,sK3,X1,sK4),sK5)
      | ~ v1_funct_2(k2_tmap_1(X0,sK3,X1,sK4),u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(k2_tmap_1(X0,sK3,X1,sK4))
      | ~ sP2(sK3,sK4,X1,X0) ) ),
    inference(resolution,[],[f180,f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f180,plain,(
    ! [X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
      | sK5 = X8
      | ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),X8,sK5)
      | ~ v1_funct_2(X8,u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(X8) ) ),
    inference(subsumption_resolution,[],[f179,f62])).

fof(f179,plain,(
    ! [X8] :
      ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),X8,sK5)
      | sK5 = X8
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
      | ~ v1_funct_2(X8,u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(X8) ) ),
    inference(subsumption_resolution,[],[f174,f63])).

fof(f174,plain,(
    ! [X8] :
      ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),X8,sK5)
      | sK5 = X8
      | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
      | ~ v1_funct_2(X8,u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(X8) ) ),
    inference(resolution,[],[f88,f64])).

fof(f158,plain,
    ( spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f150,f156,f152])).

fof(f150,plain,(
    ! [X8] :
      ( ~ m1_subset_1(X8,u1_struct_0(sK4))
      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X8) = k1_funct_1(sK5,X8)
      | v1_xboole_0(u1_struct_0(sK4)) ) ),
    inference(subsumption_resolution,[],[f149,f62])).

fof(f149,plain,(
    ! [X8] :
      ( ~ m1_subset_1(X8,u1_struct_0(sK4))
      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X8) = k1_funct_1(sK5,X8)
      | ~ v1_funct_1(sK5)
      | v1_xboole_0(u1_struct_0(sK4)) ) ),
    inference(subsumption_resolution,[],[f144,f63])).

fof(f144,plain,(
    ! [X8] :
      ( ~ m1_subset_1(X8,u1_struct_0(sK4))
      | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X8) = k1_funct_1(sK5,X8)
      | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3))
      | ~ v1_funct_1(sK5)
      | v1_xboole_0(u1_struct_0(sK4)) ) ),
    inference(resolution,[],[f83,f64])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:41:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (15102)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.48  % (15100)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.49  % (15121)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.49  % (15101)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.49  % (15111)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.50  % (15110)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.50  % (15119)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.50  % (15103)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  % (15124)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.51  % (15115)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.51  % (15107)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.52  % (15105)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.52  % (15120)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.52  % (15114)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.52  % (15117)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.53  % (15113)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (15109)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.53  % (15126)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.53  % (15098)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.54  % (15106)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.54  % (15098)Refutation not found, incomplete strategy% (15098)------------------------------
% 0.20/0.54  % (15098)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (15098)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (15098)Memory used [KB]: 10618
% 0.20/0.54  % (15098)Time elapsed: 0.125 s
% 0.20/0.54  % (15098)------------------------------
% 0.20/0.54  % (15098)------------------------------
% 0.20/0.54  % (15116)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.54  % (15125)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.54  % (15108)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.54  % (15113)Refutation not found, incomplete strategy% (15113)------------------------------
% 0.20/0.54  % (15113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (15113)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (15113)Memory used [KB]: 6396
% 0.20/0.54  % (15113)Time elapsed: 0.120 s
% 0.20/0.54  % (15113)------------------------------
% 0.20/0.54  % (15113)------------------------------
% 0.20/0.55  % (15122)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.55  % (15112)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.56  % (15118)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.56  % (15106)Refutation not found, incomplete strategy% (15106)------------------------------
% 0.20/0.56  % (15106)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (15106)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (15106)Memory used [KB]: 10874
% 0.20/0.56  % (15106)Time elapsed: 0.129 s
% 0.20/0.56  % (15106)------------------------------
% 0.20/0.56  % (15106)------------------------------
% 0.20/0.59  % (15126)Refutation found. Thanks to Tanya!
% 0.20/0.59  % SZS status Theorem for theBenchmark
% 1.82/0.60  % SZS output start Proof for theBenchmark
% 1.82/0.60  fof(f1083,plain,(
% 1.82/0.60    $false),
% 1.82/0.60    inference(avatar_sat_refutation,[],[f158,f261,f264,f267,f371,f531,f899,f925,f972,f1082])).
% 1.82/0.60  fof(f1082,plain,(
% 1.82/0.60    ~spl7_3 | ~spl7_11),
% 1.82/0.60    inference(avatar_contradiction_clause,[],[f1081])).
% 1.82/0.60  fof(f1081,plain,(
% 1.82/0.60    $false | (~spl7_3 | ~spl7_11)),
% 1.82/0.60    inference(subsumption_resolution,[],[f154,f1012])).
% 1.82/0.60  fof(f1012,plain,(
% 1.82/0.60    ~v1_xboole_0(u1_struct_0(sK4)) | ~spl7_11),
% 1.82/0.60    inference(subsumption_resolution,[],[f645,f96])).
% 1.82/0.60  fof(f96,plain,(
% 1.82/0.60    l1_pre_topc(sK4)),
% 1.82/0.60    inference(subsumption_resolution,[],[f93,f59])).
% 1.82/0.60  fof(f59,plain,(
% 1.82/0.60    l1_pre_topc(sK3)),
% 1.82/0.60    inference(cnf_transformation,[],[f48])).
% 1.82/0.60  fof(f48,plain,(
% 1.82/0.60    ((~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k4_tmap_1(sK3,sK4),sK5) & ! [X3] : (k1_funct_1(sK5,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK4)) | ~m1_subset_1(X3,u1_struct_0(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK3) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 1.82/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f17,f47,f46,f45])).
% 1.82/0.60  fof(f45,plain,(
% 1.82/0.60    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(sK3),k4_tmap_1(sK3,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(sK3))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK3) & ~v2_struct_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 1.82/0.60    introduced(choice_axiom,[])).
% 1.82/0.60  fof(f46,plain,(
% 1.82/0.60    ? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(sK3),k4_tmap_1(sK3,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(sK3))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK3) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k4_tmap_1(sK3,sK4),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK4)) | ~m1_subset_1(X3,u1_struct_0(sK3))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(X2)) & m1_pre_topc(sK4,sK3) & ~v2_struct_0(sK4))),
% 1.82/0.60    introduced(choice_axiom,[])).
% 1.82/0.60  fof(f47,plain,(
% 1.82/0.60    ? [X2] : (~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k4_tmap_1(sK3,sK4),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK4)) | ~m1_subset_1(X3,u1_struct_0(sK3))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k4_tmap_1(sK3,sK4),sK5) & ! [X3] : (k1_funct_1(sK5,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK4)) | ~m1_subset_1(X3,u1_struct_0(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(sK5))),
% 1.82/0.60    introduced(choice_axiom,[])).
% 1.82/0.60  fof(f17,plain,(
% 1.82/0.60    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.82/0.60    inference(flattening,[],[f16])).
% 1.82/0.60  fof(f16,plain,(
% 1.82/0.60    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : ((k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.82/0.60    inference(ennf_transformation,[],[f15])).
% 1.82/0.60  fof(f15,negated_conjecture,(
% 1.82/0.60    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 1.82/0.60    inference(negated_conjecture,[],[f14])).
% 1.82/0.60  fof(f14,conjecture,(
% 1.82/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 1.82/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_tmap_1)).
% 1.82/0.60  fof(f93,plain,(
% 1.82/0.60    l1_pre_topc(sK4) | ~l1_pre_topc(sK3)),
% 1.82/0.60    inference(resolution,[],[f69,f61])).
% 1.82/0.60  fof(f61,plain,(
% 1.82/0.60    m1_pre_topc(sK4,sK3)),
% 1.82/0.60    inference(cnf_transformation,[],[f48])).
% 1.82/0.60  fof(f69,plain,(
% 1.82/0.60    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f20])).
% 1.82/0.60  fof(f20,plain,(
% 1.82/0.60    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.82/0.60    inference(ennf_transformation,[],[f6])).
% 1.82/0.60  fof(f6,axiom,(
% 1.82/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.82/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.82/0.60  fof(f645,plain,(
% 1.82/0.60    ~v1_xboole_0(u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~spl7_11),
% 1.82/0.60    inference(duplicate_literal_removal,[],[f644])).
% 1.82/0.60  fof(f644,plain,(
% 1.82/0.60    ~v1_xboole_0(u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~l1_pre_topc(sK4) | ~spl7_11),
% 1.82/0.60    inference(resolution,[],[f601,f68])).
% 1.82/0.60  fof(f68,plain,(
% 1.82/0.60    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f19])).
% 1.82/0.60  fof(f19,plain,(
% 1.82/0.60    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 1.82/0.60    inference(ennf_transformation,[],[f11])).
% 1.82/0.60  fof(f11,axiom,(
% 1.82/0.60    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 1.82/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 1.82/0.60  fof(f601,plain,(
% 1.82/0.60    ( ! [X0] : (~m1_pre_topc(sK4,X0) | ~v1_xboole_0(u1_struct_0(X0)) | ~l1_pre_topc(X0)) ) | ~spl7_11),
% 1.82/0.60    inference(resolution,[],[f526,f121])).
% 1.82/0.60  fof(f121,plain,(
% 1.82/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (~sP0(X0,X1,X2,X3,X4) | ~l1_pre_topc(X5) | ~v1_xboole_0(u1_struct_0(X5)) | ~m1_pre_topc(X4,X5)) )),
% 1.82/0.60    inference(resolution,[],[f72,f112])).
% 1.82/0.60  fof(f112,plain,(
% 1.82/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X2,u1_struct_0(X0)) | ~l1_pre_topc(X1) | ~v1_xboole_0(u1_struct_0(X1)) | ~m1_pre_topc(X0,X1)) )),
% 1.82/0.60    inference(resolution,[],[f70,f82])).
% 1.82/0.60  fof(f82,plain,(
% 1.82/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f32])).
% 1.82/0.60  fof(f32,plain,(
% 1.82/0.60    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.82/0.60    inference(ennf_transformation,[],[f1])).
% 1.82/0.60  fof(f1,axiom,(
% 1.82/0.60    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.82/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.82/0.60  fof(f70,plain,(
% 1.82/0.60    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f21])).
% 1.82/0.60  fof(f21,plain,(
% 1.82/0.60    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.82/0.60    inference(ennf_transformation,[],[f10])).
% 1.82/0.60  fof(f10,axiom,(
% 1.82/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.82/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.82/0.60  fof(f72,plain,(
% 1.82/0.60    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(sK6(X0,X1,X2,X3,X4),u1_struct_0(X4)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f52])).
% 1.82/0.60  fof(f52,plain,(
% 1.82/0.60    ! [X0,X1,X2,X3,X4] : ((k3_funct_2(u1_struct_0(X3),u1_struct_0(X2),X1,sK6(X0,X1,X2,X3,X4)) != k1_funct_1(X0,sK6(X0,X1,X2,X3,X4)) & r2_hidden(sK6(X0,X1,X2,X3,X4),u1_struct_0(X4)) & m1_subset_1(sK6(X0,X1,X2,X3,X4),u1_struct_0(X3))) | ~sP0(X0,X1,X2,X3,X4))),
% 1.82/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f50,f51])).
% 1.82/0.60  fof(f51,plain,(
% 1.82/0.60    ! [X4,X3,X2,X1,X0] : (? [X5] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X2),X1,X5) != k1_funct_1(X0,X5) & r2_hidden(X5,u1_struct_0(X4)) & m1_subset_1(X5,u1_struct_0(X3))) => (k3_funct_2(u1_struct_0(X3),u1_struct_0(X2),X1,sK6(X0,X1,X2,X3,X4)) != k1_funct_1(X0,sK6(X0,X1,X2,X3,X4)) & r2_hidden(sK6(X0,X1,X2,X3,X4),u1_struct_0(X4)) & m1_subset_1(sK6(X0,X1,X2,X3,X4),u1_struct_0(X3))))),
% 1.82/0.60    introduced(choice_axiom,[])).
% 1.82/0.60  fof(f50,plain,(
% 1.82/0.60    ! [X0,X1,X2,X3,X4] : (? [X5] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X2),X1,X5) != k1_funct_1(X0,X5) & r2_hidden(X5,u1_struct_0(X4)) & m1_subset_1(X5,u1_struct_0(X3))) | ~sP0(X0,X1,X2,X3,X4))),
% 1.82/0.60    inference(rectify,[],[f49])).
% 1.82/0.60  fof(f49,plain,(
% 1.82/0.60    ! [X4,X3,X0,X1,X2] : (? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) | ~sP0(X4,X3,X0,X1,X2))),
% 1.82/0.60    inference(nnf_transformation,[],[f39])).
% 1.82/0.60  fof(f39,plain,(
% 1.82/0.60    ! [X4,X3,X0,X1,X2] : (? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) | ~sP0(X4,X3,X0,X1,X2))),
% 1.82/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.82/0.60  fof(f526,plain,(
% 1.82/0.60    sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) | ~spl7_11),
% 1.82/0.60    inference(avatar_component_clause,[],[f524])).
% 1.82/0.60  fof(f524,plain,(
% 1.82/0.60    spl7_11 <=> sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)),
% 1.82/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 1.82/0.60  fof(f154,plain,(
% 1.82/0.60    v1_xboole_0(u1_struct_0(sK4)) | ~spl7_3),
% 1.82/0.60    inference(avatar_component_clause,[],[f152])).
% 1.82/0.60  fof(f152,plain,(
% 1.82/0.60    spl7_3 <=> v1_xboole_0(u1_struct_0(sK4))),
% 1.82/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.82/0.60  fof(f972,plain,(
% 1.82/0.60    ~spl7_4 | ~spl7_8),
% 1.82/0.60    inference(avatar_contradiction_clause,[],[f971])).
% 1.82/0.60  fof(f971,plain,(
% 1.82/0.60    $false | (~spl7_4 | ~spl7_8)),
% 1.82/0.60    inference(subsumption_resolution,[],[f970,f260])).
% 1.82/0.60  fof(f260,plain,(
% 1.82/0.60    sP0(sK5,sK5,sK3,sK4,sK4) | ~spl7_8),
% 1.82/0.60    inference(avatar_component_clause,[],[f258])).
% 1.82/0.60  fof(f258,plain,(
% 1.82/0.60    spl7_8 <=> sP0(sK5,sK5,sK3,sK4,sK4)),
% 1.82/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.82/0.60  fof(f970,plain,(
% 1.82/0.60    ~sP0(sK5,sK5,sK3,sK4,sK4) | (~spl7_4 | ~spl7_8)),
% 1.82/0.60    inference(subsumption_resolution,[],[f969,f350])).
% 1.82/0.60  fof(f350,plain,(
% 1.82/0.60    sK6(sK5,sK5,sK3,sK4,sK4) = k1_funct_1(sK5,sK6(sK5,sK5,sK3,sK4,sK4)) | ~spl7_8),
% 1.82/0.60    inference(subsumption_resolution,[],[f349,f61])).
% 1.82/0.60  fof(f349,plain,(
% 1.82/0.60    ~m1_pre_topc(sK4,sK3) | sK6(sK5,sK5,sK3,sK4,sK4) = k1_funct_1(sK5,sK6(sK5,sK5,sK3,sK4,sK4)) | ~spl7_8),
% 1.82/0.60    inference(subsumption_resolution,[],[f337,f60])).
% 1.82/0.60  fof(f60,plain,(
% 1.82/0.60    ~v2_struct_0(sK4)),
% 1.82/0.60    inference(cnf_transformation,[],[f48])).
% 1.82/0.60  fof(f337,plain,(
% 1.82/0.60    v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK3) | sK6(sK5,sK5,sK3,sK4,sK4) = k1_funct_1(sK5,sK6(sK5,sK5,sK3,sK4,sK4)) | ~spl7_8),
% 1.82/0.60    inference(resolution,[],[f260,f195])).
% 1.82/0.60  fof(f195,plain,(
% 1.82/0.60    ( ! [X2,X0,X3,X1] : (~sP0(X1,X2,X3,X0,sK4) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | sK6(X1,X2,X3,X0,sK4) = k1_funct_1(sK5,sK6(X1,X2,X3,X0,sK4))) )),
% 1.82/0.60    inference(duplicate_literal_removal,[],[f194])).
% 1.82/0.60  fof(f194,plain,(
% 1.82/0.60    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~sP0(X1,X2,X3,X0,sK4) | ~m1_pre_topc(X0,sK3) | sK6(X1,X2,X3,X0,sK4) = k1_funct_1(sK5,sK6(X1,X2,X3,X0,sK4)) | ~sP0(X1,X2,X3,X0,sK4)) )),
% 1.82/0.60    inference(resolution,[],[f137,f72])).
% 1.82/0.60  fof(f137,plain,(
% 1.82/0.60    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(sK6(X1,X2,X3,X0,X4),u1_struct_0(sK4)) | v2_struct_0(X0) | ~sP0(X1,X2,X3,X0,X4) | ~m1_pre_topc(X0,sK3) | sK6(X1,X2,X3,X0,X4) = k1_funct_1(sK5,sK6(X1,X2,X3,X0,X4))) )),
% 1.82/0.60    inference(subsumption_resolution,[],[f136,f57])).
% 1.82/0.60  fof(f57,plain,(
% 1.82/0.60    ~v2_struct_0(sK3)),
% 1.82/0.60    inference(cnf_transformation,[],[f48])).
% 1.82/0.60  fof(f136,plain,(
% 1.82/0.60    ( ! [X4,X2,X0,X3,X1] : (~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | v2_struct_0(sK3) | ~sP0(X1,X2,X3,X0,X4) | ~r2_hidden(sK6(X1,X2,X3,X0,X4),u1_struct_0(sK4)) | sK6(X1,X2,X3,X0,X4) = k1_funct_1(sK5,sK6(X1,X2,X3,X0,X4))) )),
% 1.82/0.60    inference(subsumption_resolution,[],[f133,f59])).
% 1.82/0.60  fof(f133,plain,(
% 1.82/0.60    ( ! [X4,X2,X0,X3,X1] : (~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~l1_pre_topc(sK3) | v2_struct_0(sK3) | ~sP0(X1,X2,X3,X0,X4) | ~r2_hidden(sK6(X1,X2,X3,X0,X4),u1_struct_0(sK4)) | sK6(X1,X2,X3,X0,X4) = k1_funct_1(sK5,sK6(X1,X2,X3,X0,X4))) )),
% 1.82/0.60    inference(resolution,[],[f122,f65])).
% 1.82/0.60  fof(f65,plain,(
% 1.82/0.60    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK3)) | ~r2_hidden(X3,u1_struct_0(sK4)) | k1_funct_1(sK5,X3) = X3) )),
% 1.82/0.60    inference(cnf_transformation,[],[f48])).
% 1.82/0.60  fof(f122,plain,(
% 1.82/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(sK6(X0,X1,X2,X3,X4),u1_struct_0(X5)) | ~m1_pre_topc(X3,X5) | v2_struct_0(X3) | ~l1_pre_topc(X5) | v2_struct_0(X5) | ~sP0(X0,X1,X2,X3,X4)) )),
% 1.82/0.60    inference(resolution,[],[f76,f71])).
% 1.82/0.60  fof(f71,plain,(
% 1.82/0.60    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK6(X0,X1,X2,X3,X4),u1_struct_0(X3)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f52])).
% 1.82/0.60  fof(f76,plain,(
% 1.82/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f27])).
% 1.82/0.60  fof(f27,plain,(
% 1.82/0.60    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.82/0.60    inference(flattening,[],[f26])).
% 1.82/0.60  fof(f26,plain,(
% 1.82/0.60    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.82/0.60    inference(ennf_transformation,[],[f7])).
% 1.82/0.60  fof(f7,axiom,(
% 1.82/0.60    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 1.82/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).
% 1.82/0.60  fof(f969,plain,(
% 1.82/0.60    sK6(sK5,sK5,sK3,sK4,sK4) != k1_funct_1(sK5,sK6(sK5,sK5,sK3,sK4,sK4)) | ~sP0(sK5,sK5,sK3,sK4,sK4) | (~spl7_4 | ~spl7_8)),
% 1.82/0.60    inference(superposition,[],[f73,f964])).
% 1.82/0.60  fof(f964,plain,(
% 1.82/0.60    sK6(sK5,sK5,sK3,sK4,sK4) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK6(sK5,sK5,sK3,sK4,sK4)) | (~spl7_4 | ~spl7_8)),
% 1.82/0.60    inference(forward_demodulation,[],[f951,f350])).
% 1.82/0.60  fof(f951,plain,(
% 1.82/0.60    k1_funct_1(sK5,sK6(sK5,sK5,sK3,sK4,sK4)) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK6(sK5,sK5,sK3,sK4,sK4)) | (~spl7_4 | ~spl7_8)),
% 1.82/0.60    inference(resolution,[],[f260,f631])).
% 1.82/0.60  fof(f631,plain,(
% 1.82/0.60    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,sK4,X3) | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK6(X0,X1,X2,sK4,X3)) = k1_funct_1(sK5,sK6(X0,X1,X2,sK4,X3))) ) | ~spl7_4),
% 1.82/0.60    inference(resolution,[],[f157,f71])).
% 1.82/0.60  fof(f157,plain,(
% 1.82/0.60    ( ! [X8] : (~m1_subset_1(X8,u1_struct_0(sK4)) | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X8) = k1_funct_1(sK5,X8)) ) | ~spl7_4),
% 1.82/0.60    inference(avatar_component_clause,[],[f156])).
% 1.82/0.60  fof(f156,plain,(
% 1.82/0.60    spl7_4 <=> ! [X8] : (~m1_subset_1(X8,u1_struct_0(sK4)) | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X8) = k1_funct_1(sK5,X8))),
% 1.82/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.82/0.60  fof(f73,plain,(
% 1.82/0.60    ( ! [X4,X2,X0,X3,X1] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X2),X1,sK6(X0,X1,X2,X3,X4)) != k1_funct_1(X0,sK6(X0,X1,X2,X3,X4)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f52])).
% 1.82/0.60  fof(f925,plain,(
% 1.82/0.60    ~spl7_12),
% 1.82/0.60    inference(avatar_contradiction_clause,[],[f924])).
% 1.82/0.60  fof(f924,plain,(
% 1.82/0.60    $false | ~spl7_12),
% 1.82/0.60    inference(subsumption_resolution,[],[f912,f132])).
% 1.82/0.60  fof(f132,plain,(
% 1.82/0.60    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK5)),
% 1.82/0.60    inference(subsumption_resolution,[],[f131,f62])).
% 1.82/0.60  fof(f62,plain,(
% 1.82/0.60    v1_funct_1(sK5)),
% 1.82/0.60    inference(cnf_transformation,[],[f48])).
% 1.82/0.60  fof(f131,plain,(
% 1.82/0.60    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK5) | ~v1_funct_1(sK5)),
% 1.82/0.60    inference(subsumption_resolution,[],[f126,f63])).
% 1.82/0.60  fof(f63,plain,(
% 1.82/0.60    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3))),
% 1.82/0.60    inference(cnf_transformation,[],[f48])).
% 1.82/0.60  fof(f126,plain,(
% 1.82/0.60    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK5) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK5)),
% 1.82/0.60    inference(resolution,[],[f91,f64])).
% 1.82/0.60  fof(f64,plain,(
% 1.82/0.60    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))),
% 1.82/0.60    inference(cnf_transformation,[],[f48])).
% 1.82/0.60  fof(f91,plain,(
% 1.82/0.60    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.82/0.60    inference(duplicate_literal_removal,[],[f90])).
% 1.82/0.60  fof(f90,plain,(
% 1.82/0.60    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.82/0.60    inference(equality_resolution,[],[f89])).
% 1.82/0.60  fof(f89,plain,(
% 1.82/0.60    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f56])).
% 1.82/0.60  fof(f56,plain,(
% 1.82/0.60    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.82/0.60    inference(nnf_transformation,[],[f38])).
% 1.82/0.60  fof(f38,plain,(
% 1.82/0.60    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.82/0.60    inference(flattening,[],[f37])).
% 1.82/0.60  fof(f37,plain,(
% 1.82/0.60    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.82/0.60    inference(ennf_transformation,[],[f3])).
% 1.82/0.60  fof(f3,axiom,(
% 1.82/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 1.82/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 1.82/0.60  fof(f912,plain,(
% 1.82/0.60    ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK5) | ~spl7_12),
% 1.82/0.60    inference(backward_demodulation,[],[f66,f530])).
% 1.82/0.60  fof(f530,plain,(
% 1.82/0.60    k4_tmap_1(sK3,sK4) = sK5 | ~spl7_12),
% 1.82/0.60    inference(avatar_component_clause,[],[f528])).
% 1.82/0.60  fof(f528,plain,(
% 1.82/0.60    spl7_12 <=> k4_tmap_1(sK3,sK4) = sK5),
% 1.82/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 1.82/0.60  fof(f66,plain,(
% 1.82/0.60    ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k4_tmap_1(sK3,sK4),sK5)),
% 1.82/0.60    inference(cnf_transformation,[],[f48])).
% 1.82/0.60  fof(f899,plain,(
% 1.82/0.60    ~spl7_4 | ~spl7_11),
% 1.82/0.60    inference(avatar_contradiction_clause,[],[f898])).
% 1.82/0.60  fof(f898,plain,(
% 1.82/0.60    $false | (~spl7_4 | ~spl7_11)),
% 1.82/0.60    inference(subsumption_resolution,[],[f897,f755])).
% 1.82/0.60  fof(f755,plain,(
% 1.82/0.60    sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) != k1_funct_1(k4_tmap_1(sK3,sK4),sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)) | (~spl7_4 | ~spl7_11)),
% 1.82/0.60    inference(subsumption_resolution,[],[f754,f526])).
% 1.82/0.60  fof(f754,plain,(
% 1.82/0.60    sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) != k1_funct_1(k4_tmap_1(sK3,sK4),sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)) | ~sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) | (~spl7_4 | ~spl7_11)),
% 1.82/0.60    inference(superposition,[],[f73,f713])).
% 1.82/0.60  fof(f713,plain,(
% 1.82/0.60    sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)) | (~spl7_4 | ~spl7_11)),
% 1.82/0.60    inference(forward_demodulation,[],[f712,f613])).
% 1.82/0.60  fof(f613,plain,(
% 1.82/0.60    sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k1_funct_1(sK5,sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)) | ~spl7_11),
% 1.82/0.60    inference(subsumption_resolution,[],[f612,f61])).
% 1.82/0.60  fof(f612,plain,(
% 1.82/0.60    ~m1_pre_topc(sK4,sK3) | sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k1_funct_1(sK5,sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)) | ~spl7_11),
% 1.82/0.60    inference(subsumption_resolution,[],[f600,f60])).
% 1.82/0.60  fof(f600,plain,(
% 1.82/0.60    v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK3) | sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k1_funct_1(sK5,sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)) | ~spl7_11),
% 1.82/0.60    inference(resolution,[],[f526,f195])).
% 1.82/0.60  fof(f712,plain,(
% 1.82/0.60    k1_funct_1(sK5,sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)) = k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)) | (~spl7_4 | ~spl7_11)),
% 1.82/0.60    inference(resolution,[],[f631,f526])).
% 1.82/0.60  fof(f897,plain,(
% 1.82/0.60    sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k1_funct_1(k4_tmap_1(sK3,sK4),sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)) | ~spl7_11),
% 1.82/0.60    inference(subsumption_resolution,[],[f896,f57])).
% 1.82/0.60  fof(f896,plain,(
% 1.82/0.60    v2_struct_0(sK3) | sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k1_funct_1(k4_tmap_1(sK3,sK4),sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)) | ~spl7_11),
% 1.82/0.60    inference(subsumption_resolution,[],[f895,f58])).
% 1.82/0.60  fof(f58,plain,(
% 1.82/0.60    v2_pre_topc(sK3)),
% 1.82/0.60    inference(cnf_transformation,[],[f48])).
% 1.82/0.60  fof(f895,plain,(
% 1.82/0.60    ~v2_pre_topc(sK3) | v2_struct_0(sK3) | sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k1_funct_1(k4_tmap_1(sK3,sK4),sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)) | ~spl7_11),
% 1.82/0.60    inference(subsumption_resolution,[],[f891,f59])).
% 1.82/0.60  fof(f891,plain,(
% 1.82/0.60    ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k1_funct_1(k4_tmap_1(sK3,sK4),sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4)) | ~spl7_11),
% 1.82/0.60    inference(resolution,[],[f630,f61])).
% 1.82/0.60  fof(f630,plain,(
% 1.82/0.60    ( ! [X8] : (~m1_pre_topc(sK4,X8) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k1_funct_1(k4_tmap_1(X8,sK4),sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4))) ) | ~spl7_11),
% 1.82/0.60    inference(subsumption_resolution,[],[f610,f60])).
% 1.82/0.60  fof(f610,plain,(
% 1.82/0.60    ( ! [X8] : (~m1_pre_topc(sK4,X8) | v2_struct_0(sK4) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k1_funct_1(k4_tmap_1(X8,sK4),sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4))) ) | ~spl7_11),
% 1.82/0.60    inference(duplicate_literal_removal,[],[f609])).
% 1.82/0.60  fof(f609,plain,(
% 1.82/0.60    ( ! [X8] : (~m1_pre_topc(sK4,X8) | v2_struct_0(sK4) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~m1_pre_topc(sK4,X8) | v2_struct_0(sK4) | sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) = k1_funct_1(k4_tmap_1(X8,sK4),sK6(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4))) ) | ~spl7_11),
% 1.82/0.60    inference(resolution,[],[f526,f216])).
% 1.82/0.60  fof(f216,plain,(
% 1.82/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (~sP0(X0,X1,X2,X3,X4) | ~m1_pre_topc(X4,X5) | v2_struct_0(X4) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5) | ~m1_pre_topc(X3,X5) | v2_struct_0(X3) | sK6(X0,X1,X2,X3,X4) = k1_funct_1(k4_tmap_1(X5,X4),sK6(X0,X1,X2,X3,X4))) )),
% 1.82/0.60    inference(duplicate_literal_removal,[],[f215])).
% 1.82/0.60  fof(f215,plain,(
% 1.82/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (sK6(X0,X1,X2,X3,X4) = k1_funct_1(k4_tmap_1(X5,X4),sK6(X0,X1,X2,X3,X4)) | ~m1_pre_topc(X4,X5) | v2_struct_0(X4) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5) | ~m1_pre_topc(X3,X5) | v2_struct_0(X3) | ~sP0(X0,X1,X2,X3,X4) | ~sP0(X0,X1,X2,X3,X4)) )),
% 1.82/0.60    inference(resolution,[],[f141,f72])).
% 1.82/0.60  fof(f141,plain,(
% 1.82/0.60    ( ! [X6,X12,X10,X8,X7,X11,X9] : (~r2_hidden(sK6(X6,X7,X8,X9,X10),u1_struct_0(X11)) | sK6(X6,X7,X8,X9,X10) = k1_funct_1(k4_tmap_1(X12,X11),sK6(X6,X7,X8,X9,X10)) | ~m1_pre_topc(X11,X12) | v2_struct_0(X11) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | v2_struct_0(X12) | ~m1_pre_topc(X9,X12) | v2_struct_0(X9) | ~sP0(X6,X7,X8,X9,X10)) )),
% 1.82/0.60    inference(duplicate_literal_removal,[],[f140])).
% 1.82/0.60  fof(f140,plain,(
% 1.82/0.60    ( ! [X6,X12,X10,X8,X7,X11,X9] : (~r2_hidden(sK6(X6,X7,X8,X9,X10),u1_struct_0(X11)) | sK6(X6,X7,X8,X9,X10) = k1_funct_1(k4_tmap_1(X12,X11),sK6(X6,X7,X8,X9,X10)) | ~m1_pre_topc(X11,X12) | v2_struct_0(X11) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | v2_struct_0(X12) | ~m1_pre_topc(X9,X12) | v2_struct_0(X9) | ~l1_pre_topc(X12) | v2_struct_0(X12) | ~sP0(X6,X7,X8,X9,X10)) )),
% 1.82/0.60    inference(resolution,[],[f75,f122])).
% 1.82/0.60  fof(f75,plain,(
% 1.82/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,u1_struct_0(X1)) | k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f25])).
% 1.82/0.60  fof(f25,plain,(
% 1.82/0.60    ! [X0] : (! [X1] : (! [X2] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.82/0.60    inference(flattening,[],[f24])).
% 1.82/0.60  fof(f24,plain,(
% 1.82/0.60    ! [X0] : (! [X1] : (! [X2] : ((k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.82/0.60    inference(ennf_transformation,[],[f13])).
% 1.82/0.60  fof(f13,axiom,(
% 1.82/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,u1_struct_0(X1)) => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2))))),
% 1.82/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_tmap_1)).
% 1.82/0.60  fof(f531,plain,(
% 1.82/0.60    spl7_11 | spl7_12 | ~spl7_6 | ~spl7_7),
% 1.82/0.60    inference(avatar_split_clause,[],[f476,f254,f250,f528,f524])).
% 1.82/0.60  fof(f250,plain,(
% 1.82/0.60    spl7_6 <=> sK5 = k2_tmap_1(sK4,sK3,sK5,sK4)),
% 1.82/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.82/0.60  fof(f254,plain,(
% 1.82/0.60    spl7_7 <=> m1_pre_topc(sK4,sK4)),
% 1.82/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.82/0.60  fof(f476,plain,(
% 1.82/0.60    k4_tmap_1(sK3,sK4) = sK5 | sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) | (~spl7_6 | ~spl7_7)),
% 1.82/0.60    inference(subsumption_resolution,[],[f475,f118])).
% 1.82/0.60  fof(f118,plain,(
% 1.82/0.60    sP1(sK3,sK4)),
% 1.82/0.60    inference(subsumption_resolution,[],[f117,f57])).
% 1.82/0.60  fof(f117,plain,(
% 1.82/0.60    sP1(sK3,sK4) | v2_struct_0(sK3)),
% 1.82/0.60    inference(subsumption_resolution,[],[f116,f58])).
% 1.82/0.60  fof(f116,plain,(
% 1.82/0.60    sP1(sK3,sK4) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.82/0.60    inference(subsumption_resolution,[],[f113,f59])).
% 1.82/0.60  fof(f113,plain,(
% 1.82/0.60    sP1(sK3,sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.82/0.60    inference(resolution,[],[f81,f61])).
% 1.82/0.60  fof(f81,plain,(
% 1.82/0.60    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | sP1(X0,X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f42])).
% 1.82/0.60  fof(f42,plain,(
% 1.82/0.60    ! [X0,X1] : (sP1(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.82/0.60    inference(definition_folding,[],[f31,f41])).
% 1.82/0.60  fof(f41,plain,(
% 1.82/0.60    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~sP1(X0,X1))),
% 1.82/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.82/0.60  fof(f31,plain,(
% 1.82/0.60    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.82/0.60    inference(flattening,[],[f30])).
% 1.82/0.60  fof(f30,plain,(
% 1.82/0.60    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.82/0.60    inference(ennf_transformation,[],[f9])).
% 1.82/0.60  fof(f9,axiom,(
% 1.82/0.60    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))))),
% 1.82/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_tmap_1)).
% 1.82/0.60  fof(f475,plain,(
% 1.82/0.60    k4_tmap_1(sK3,sK4) = sK5 | sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) | ~sP1(sK3,sK4) | (~spl7_6 | ~spl7_7)),
% 1.82/0.60    inference(subsumption_resolution,[],[f474,f57])).
% 1.82/0.60  fof(f474,plain,(
% 1.82/0.60    v2_struct_0(sK3) | k4_tmap_1(sK3,sK4) = sK5 | sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) | ~sP1(sK3,sK4) | (~spl7_6 | ~spl7_7)),
% 1.82/0.60    inference(subsumption_resolution,[],[f473,f58])).
% 1.82/0.60  fof(f473,plain,(
% 1.82/0.60    ~v2_pre_topc(sK3) | v2_struct_0(sK3) | k4_tmap_1(sK3,sK4) = sK5 | sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) | ~sP1(sK3,sK4) | (~spl7_6 | ~spl7_7)),
% 1.82/0.60    inference(subsumption_resolution,[],[f472,f59])).
% 1.82/0.60  fof(f472,plain,(
% 1.82/0.60    ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | k4_tmap_1(sK3,sK4) = sK5 | sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) | ~sP1(sK3,sK4) | (~spl7_6 | ~spl7_7)),
% 1.82/0.60    inference(subsumption_resolution,[],[f471,f102])).
% 1.82/0.60  fof(f102,plain,(
% 1.82/0.60    v2_pre_topc(sK4)),
% 1.82/0.60    inference(subsumption_resolution,[],[f101,f58])).
% 1.82/0.60  fof(f101,plain,(
% 1.82/0.60    v2_pre_topc(sK4) | ~v2_pre_topc(sK3)),
% 1.82/0.60    inference(subsumption_resolution,[],[f98,f59])).
% 1.82/0.60  fof(f98,plain,(
% 1.82/0.60    v2_pre_topc(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3)),
% 1.82/0.60    inference(resolution,[],[f77,f61])).
% 1.82/0.60  fof(f77,plain,(
% 1.82/0.60    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f29])).
% 1.82/0.60  fof(f29,plain,(
% 1.82/0.60    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.82/0.60    inference(flattening,[],[f28])).
% 1.82/0.60  fof(f28,plain,(
% 1.82/0.60    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.82/0.60    inference(ennf_transformation,[],[f4])).
% 1.82/0.60  fof(f4,axiom,(
% 1.82/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.82/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.82/0.60  fof(f471,plain,(
% 1.82/0.60    ~v2_pre_topc(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | k4_tmap_1(sK3,sK4) = sK5 | sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) | ~sP1(sK3,sK4) | (~spl7_6 | ~spl7_7)),
% 1.82/0.60    inference(subsumption_resolution,[],[f470,f96])).
% 1.82/0.60  fof(f470,plain,(
% 1.82/0.60    ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | k4_tmap_1(sK3,sK4) = sK5 | sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) | ~sP1(sK3,sK4) | (~spl7_6 | ~spl7_7)),
% 1.82/0.60    inference(subsumption_resolution,[],[f469,f60])).
% 1.82/0.60  fof(f469,plain,(
% 1.82/0.60    v2_struct_0(sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | k4_tmap_1(sK3,sK4) = sK5 | sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) | ~sP1(sK3,sK4) | (~spl7_6 | ~spl7_7)),
% 1.82/0.60    inference(subsumption_resolution,[],[f468,f255])).
% 1.82/0.60  fof(f255,plain,(
% 1.82/0.60    m1_pre_topc(sK4,sK4) | ~spl7_7),
% 1.82/0.60    inference(avatar_component_clause,[],[f254])).
% 1.82/0.60  fof(f468,plain,(
% 1.82/0.60    ~m1_pre_topc(sK4,sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | k4_tmap_1(sK3,sK4) = sK5 | sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) | ~sP1(sK3,sK4) | ~spl7_6),
% 1.82/0.60    inference(subsumption_resolution,[],[f467,f62])).
% 1.82/0.60  fof(f467,plain,(
% 1.82/0.60    ~v1_funct_1(sK5) | ~m1_pre_topc(sK4,sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | k4_tmap_1(sK3,sK4) = sK5 | sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) | ~sP1(sK3,sK4) | ~spl7_6),
% 1.82/0.60    inference(subsumption_resolution,[],[f466,f63])).
% 1.82/0.60  fof(f466,plain,(
% 1.82/0.60    ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK5) | ~m1_pre_topc(sK4,sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | k4_tmap_1(sK3,sK4) = sK5 | sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) | ~sP1(sK3,sK4) | ~spl7_6),
% 1.82/0.60    inference(subsumption_resolution,[],[f463,f64])).
% 1.82/0.60  fof(f463,plain,(
% 1.82/0.60    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK5) | ~m1_pre_topc(sK4,sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | k4_tmap_1(sK3,sK4) = sK5 | sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) | ~sP1(sK3,sK4) | ~spl7_6),
% 1.82/0.60    inference(duplicate_literal_removal,[],[f458])).
% 1.82/0.60  fof(f458,plain,(
% 1.82/0.60    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK5) | ~m1_pre_topc(sK4,sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | k4_tmap_1(sK3,sK4) = sK5 | sP0(k4_tmap_1(sK3,sK4),sK5,sK3,sK4,sK4) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK5) | ~sP1(sK3,sK4) | ~spl7_6),
% 1.82/0.60    inference(superposition,[],[f229,f252])).
% 1.82/0.60  fof(f252,plain,(
% 1.82/0.60    sK5 = k2_tmap_1(sK4,sK3,sK5,sK4) | ~spl7_6),
% 1.82/0.60    inference(avatar_component_clause,[],[f250])).
% 1.82/0.60  fof(f229,plain,(
% 1.82/0.60    ( ! [X4,X2,X5,X3] : (~m1_subset_1(k2_tmap_1(X5,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2)))) | ~v1_funct_2(X4,u1_struct_0(X5),u1_struct_0(X2)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X5) | v2_struct_0(X3) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | k4_tmap_1(X2,X3) = k2_tmap_1(X5,X2,X4,X3) | sP0(k4_tmap_1(X2,X3),X4,X2,X5,X3) | ~v1_funct_2(k2_tmap_1(X5,X2,X4,X3),u1_struct_0(X3),u1_struct_0(X2)) | ~v1_funct_1(k2_tmap_1(X5,X2,X4,X3)) | ~sP1(X2,X3)) )),
% 1.82/0.60    inference(subsumption_resolution,[],[f228,f78])).
% 1.82/0.60  fof(f78,plain,(
% 1.82/0.60    ( ! [X0,X1] : (v1_funct_1(k4_tmap_1(X0,X1)) | ~sP1(X0,X1)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f53])).
% 1.82/0.60  fof(f53,plain,(
% 1.82/0.60    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~sP1(X0,X1))),
% 1.82/0.60    inference(nnf_transformation,[],[f41])).
% 1.82/0.60  fof(f228,plain,(
% 1.82/0.60    ( ! [X4,X2,X5,X3] : (sP0(k4_tmap_1(X2,X3),X4,X2,X5,X3) | ~v1_funct_1(k4_tmap_1(X2,X3)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2)))) | ~v1_funct_2(X4,u1_struct_0(X5),u1_struct_0(X2)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X5) | v2_struct_0(X3) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | k4_tmap_1(X2,X3) = k2_tmap_1(X5,X2,X4,X3) | ~m1_subset_1(k2_tmap_1(X5,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) | ~v1_funct_2(k2_tmap_1(X5,X2,X4,X3),u1_struct_0(X3),u1_struct_0(X2)) | ~v1_funct_1(k2_tmap_1(X5,X2,X4,X3)) | ~sP1(X2,X3)) )),
% 1.82/0.60    inference(subsumption_resolution,[],[f227,f79])).
% 1.82/0.60  fof(f79,plain,(
% 1.82/0.60    ( ! [X0,X1] : (v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~sP1(X0,X1)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f53])).
% 1.82/0.60  fof(f227,plain,(
% 1.82/0.60    ( ! [X4,X2,X5,X3] : (sP0(k4_tmap_1(X2,X3),X4,X2,X5,X3) | ~v1_funct_2(k4_tmap_1(X2,X3),u1_struct_0(X3),u1_struct_0(X2)) | ~v1_funct_1(k4_tmap_1(X2,X3)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2)))) | ~v1_funct_2(X4,u1_struct_0(X5),u1_struct_0(X2)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X5) | v2_struct_0(X3) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | k4_tmap_1(X2,X3) = k2_tmap_1(X5,X2,X4,X3) | ~m1_subset_1(k2_tmap_1(X5,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) | ~v1_funct_2(k2_tmap_1(X5,X2,X4,X3),u1_struct_0(X3),u1_struct_0(X2)) | ~v1_funct_1(k2_tmap_1(X5,X2,X4,X3)) | ~sP1(X2,X3)) )),
% 1.82/0.60    inference(subsumption_resolution,[],[f218,f80])).
% 1.82/0.60  fof(f80,plain,(
% 1.82/0.60    ( ! [X0,X1] : (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~sP1(X0,X1)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f53])).
% 1.82/0.60  fof(f218,plain,(
% 1.82/0.60    ( ! [X4,X2,X5,X3] : (sP0(k4_tmap_1(X2,X3),X4,X2,X5,X3) | ~m1_subset_1(k4_tmap_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) | ~v1_funct_2(k4_tmap_1(X2,X3),u1_struct_0(X3),u1_struct_0(X2)) | ~v1_funct_1(k4_tmap_1(X2,X3)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2)))) | ~v1_funct_2(X4,u1_struct_0(X5),u1_struct_0(X2)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X5) | v2_struct_0(X3) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | k4_tmap_1(X2,X3) = k2_tmap_1(X5,X2,X4,X3) | ~m1_subset_1(k2_tmap_1(X5,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) | ~v1_funct_2(k2_tmap_1(X5,X2,X4,X3),u1_struct_0(X3),u1_struct_0(X2)) | ~v1_funct_1(k2_tmap_1(X5,X2,X4,X3)) | ~sP1(X2,X3)) )),
% 1.82/0.60    inference(resolution,[],[f74,f178])).
% 1.82/0.60  fof(f178,plain,(
% 1.82/0.60    ( ! [X6,X7,X5] : (~r2_funct_2(u1_struct_0(X5),u1_struct_0(X6),X7,k4_tmap_1(X6,X5)) | k4_tmap_1(X6,X5) = X7 | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X6)))) | ~v1_funct_2(X7,u1_struct_0(X5),u1_struct_0(X6)) | ~v1_funct_1(X7) | ~sP1(X6,X5)) )),
% 1.82/0.60    inference(subsumption_resolution,[],[f177,f78])).
% 1.82/0.60  fof(f177,plain,(
% 1.82/0.60    ( ! [X6,X7,X5] : (~r2_funct_2(u1_struct_0(X5),u1_struct_0(X6),X7,k4_tmap_1(X6,X5)) | k4_tmap_1(X6,X5) = X7 | ~v1_funct_1(k4_tmap_1(X6,X5)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X6)))) | ~v1_funct_2(X7,u1_struct_0(X5),u1_struct_0(X6)) | ~v1_funct_1(X7) | ~sP1(X6,X5)) )),
% 1.82/0.60    inference(subsumption_resolution,[],[f173,f79])).
% 1.82/0.60  fof(f173,plain,(
% 1.82/0.60    ( ! [X6,X7,X5] : (~r2_funct_2(u1_struct_0(X5),u1_struct_0(X6),X7,k4_tmap_1(X6,X5)) | k4_tmap_1(X6,X5) = X7 | ~v1_funct_2(k4_tmap_1(X6,X5),u1_struct_0(X5),u1_struct_0(X6)) | ~v1_funct_1(k4_tmap_1(X6,X5)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X6)))) | ~v1_funct_2(X7,u1_struct_0(X5),u1_struct_0(X6)) | ~v1_funct_1(X7) | ~sP1(X6,X5)) )),
% 1.82/0.60    inference(resolution,[],[f88,f80])).
% 1.82/0.60  fof(f88,plain,(
% 1.82/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_funct_2(X0,X1,X2,X3) | X2 = X3 | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f56])).
% 1.82/0.60  fof(f74,plain,(
% 1.82/0.60    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | sP0(X4,X3,X0,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f40])).
% 1.82/0.60  fof(f40,plain,(
% 1.82/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | sP0(X4,X3,X0,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.82/0.60    inference(definition_folding,[],[f23,f39])).
% 1.82/0.60  fof(f23,plain,(
% 1.82/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.82/0.60    inference(flattening,[],[f22])).
% 1.82/0.60  fof(f22,plain,(
% 1.82/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : ((k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X1)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X1) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.82/0.60    inference(ennf_transformation,[],[f12])).
% 1.82/0.60  fof(f12,axiom,(
% 1.82/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => (r2_hidden(X5,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 1.82/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tmap_1)).
% 1.82/0.60  fof(f371,plain,(
% 1.82/0.60    ~spl7_3 | ~spl7_8),
% 1.82/0.60    inference(avatar_contradiction_clause,[],[f370])).
% 1.82/0.60  fof(f370,plain,(
% 1.82/0.60    $false | (~spl7_3 | ~spl7_8)),
% 1.82/0.60    inference(subsumption_resolution,[],[f369,f96])).
% 1.82/0.60  fof(f369,plain,(
% 1.82/0.60    ~l1_pre_topc(sK4) | (~spl7_3 | ~spl7_8)),
% 1.82/0.60    inference(subsumption_resolution,[],[f364,f154])).
% 1.82/0.60  fof(f364,plain,(
% 1.82/0.60    ~v1_xboole_0(u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~spl7_8),
% 1.82/0.60    inference(duplicate_literal_removal,[],[f363])).
% 1.82/0.60  fof(f363,plain,(
% 1.82/0.60    ~v1_xboole_0(u1_struct_0(sK4)) | ~l1_pre_topc(sK4) | ~l1_pre_topc(sK4) | ~spl7_8),
% 1.82/0.60    inference(resolution,[],[f338,f68])).
% 1.82/0.60  fof(f338,plain,(
% 1.82/0.60    ( ! [X0] : (~m1_pre_topc(sK4,X0) | ~v1_xboole_0(u1_struct_0(X0)) | ~l1_pre_topc(X0)) ) | ~spl7_8),
% 1.82/0.60    inference(resolution,[],[f260,f121])).
% 1.82/0.60  fof(f267,plain,(
% 1.82/0.60    spl7_7),
% 1.82/0.60    inference(avatar_contradiction_clause,[],[f266])).
% 1.82/0.60  fof(f266,plain,(
% 1.82/0.60    $false | spl7_7),
% 1.82/0.60    inference(subsumption_resolution,[],[f265,f96])).
% 1.82/0.60  fof(f265,plain,(
% 1.82/0.60    ~l1_pre_topc(sK4) | spl7_7),
% 1.82/0.60    inference(resolution,[],[f256,f68])).
% 1.82/0.60  fof(f256,plain,(
% 1.82/0.60    ~m1_pre_topc(sK4,sK4) | spl7_7),
% 1.82/0.60    inference(avatar_component_clause,[],[f254])).
% 1.82/0.60  fof(f264,plain,(
% 1.82/0.60    spl7_5),
% 1.82/0.60    inference(avatar_contradiction_clause,[],[f263])).
% 1.82/0.60  fof(f263,plain,(
% 1.82/0.60    $false | spl7_5),
% 1.82/0.60    inference(subsumption_resolution,[],[f262,f97])).
% 1.82/0.60  fof(f97,plain,(
% 1.82/0.60    l1_struct_0(sK4)),
% 1.82/0.60    inference(resolution,[],[f96,f67])).
% 1.82/0.60  fof(f67,plain,(
% 1.82/0.60    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f18])).
% 1.82/0.60  fof(f18,plain,(
% 1.82/0.60    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.82/0.60    inference(ennf_transformation,[],[f5])).
% 1.82/0.60  fof(f5,axiom,(
% 1.82/0.60    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.82/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.82/0.60  fof(f262,plain,(
% 1.82/0.60    ~l1_struct_0(sK4) | spl7_5),
% 1.82/0.60    inference(resolution,[],[f248,f171])).
% 1.82/0.60  fof(f171,plain,(
% 1.82/0.60    ( ! [X8] : (sP2(sK3,X8,sK5,sK4) | ~l1_struct_0(X8)) )),
% 1.82/0.60    inference(subsumption_resolution,[],[f170,f97])).
% 1.82/0.60  fof(f170,plain,(
% 1.82/0.60    ( ! [X8] : (~l1_struct_0(X8) | sP2(sK3,X8,sK5,sK4) | ~l1_struct_0(sK4)) )),
% 1.82/0.60    inference(subsumption_resolution,[],[f169,f92])).
% 1.82/0.60  fof(f92,plain,(
% 1.82/0.60    l1_struct_0(sK3)),
% 1.82/0.60    inference(resolution,[],[f67,f59])).
% 1.82/0.60  fof(f169,plain,(
% 1.82/0.60    ( ! [X8] : (~l1_struct_0(X8) | sP2(sK3,X8,sK5,sK4) | ~l1_struct_0(sK3) | ~l1_struct_0(sK4)) )),
% 1.82/0.60    inference(subsumption_resolution,[],[f168,f62])).
% 1.82/0.60  fof(f168,plain,(
% 1.82/0.60    ( ! [X8] : (~l1_struct_0(X8) | sP2(sK3,X8,sK5,sK4) | ~v1_funct_1(sK5) | ~l1_struct_0(sK3) | ~l1_struct_0(sK4)) )),
% 1.82/0.60    inference(subsumption_resolution,[],[f163,f63])).
% 1.82/0.60  fof(f163,plain,(
% 1.82/0.60    ( ! [X8] : (~l1_struct_0(X8) | sP2(sK3,X8,sK5,sK4) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK5) | ~l1_struct_0(sK3) | ~l1_struct_0(sK4)) )),
% 1.82/0.60    inference(resolution,[],[f87,f64])).
% 1.82/0.60  fof(f87,plain,(
% 1.82/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X3) | sP2(X1,X3,X2,X0) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f44])).
% 1.82/0.60  fof(f44,plain,(
% 1.82/0.60    ! [X0,X1,X2,X3] : (sP2(X1,X3,X2,X0) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 1.82/0.60    inference(definition_folding,[],[f36,f43])).
% 1.82/0.60  fof(f43,plain,(
% 1.82/0.60    ! [X1,X3,X2,X0] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~sP2(X1,X3,X2,X0))),
% 1.82/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.82/0.60  fof(f36,plain,(
% 1.82/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 1.82/0.60    inference(flattening,[],[f35])).
% 1.82/0.60  fof(f35,plain,(
% 1.82/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 1.82/0.60    inference(ennf_transformation,[],[f8])).
% 1.82/0.60  fof(f8,axiom,(
% 1.82/0.60    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 1.82/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).
% 1.82/0.60  fof(f248,plain,(
% 1.82/0.60    ~sP2(sK3,sK4,sK5,sK4) | spl7_5),
% 1.82/0.60    inference(avatar_component_clause,[],[f246])).
% 1.82/0.60  fof(f246,plain,(
% 1.82/0.60    spl7_5 <=> sP2(sK3,sK4,sK5,sK4)),
% 1.82/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.82/0.60  fof(f261,plain,(
% 1.82/0.60    ~spl7_5 | spl7_6 | ~spl7_7 | spl7_8),
% 1.82/0.60    inference(avatar_split_clause,[],[f244,f258,f254,f250,f246])).
% 1.82/0.60  fof(f244,plain,(
% 1.82/0.60    sP0(sK5,sK5,sK3,sK4,sK4) | ~m1_pre_topc(sK4,sK4) | sK5 = k2_tmap_1(sK4,sK3,sK5,sK4) | ~sP2(sK3,sK4,sK5,sK4)),
% 1.82/0.60    inference(subsumption_resolution,[],[f243,f60])).
% 1.82/0.60  fof(f243,plain,(
% 1.82/0.60    sP0(sK5,sK5,sK3,sK4,sK4) | ~m1_pre_topc(sK4,sK4) | v2_struct_0(sK4) | sK5 = k2_tmap_1(sK4,sK3,sK5,sK4) | ~sP2(sK3,sK4,sK5,sK4)),
% 1.82/0.60    inference(subsumption_resolution,[],[f242,f102])).
% 1.82/0.60  fof(f242,plain,(
% 1.82/0.60    sP0(sK5,sK5,sK3,sK4,sK4) | ~m1_pre_topc(sK4,sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | sK5 = k2_tmap_1(sK4,sK3,sK5,sK4) | ~sP2(sK3,sK4,sK5,sK4)),
% 1.82/0.60    inference(subsumption_resolution,[],[f241,f96])).
% 1.82/0.60  fof(f241,plain,(
% 1.82/0.60    sP0(sK5,sK5,sK3,sK4,sK4) | ~m1_pre_topc(sK4,sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | sK5 = k2_tmap_1(sK4,sK3,sK5,sK4) | ~sP2(sK3,sK4,sK5,sK4)),
% 1.82/0.60    inference(subsumption_resolution,[],[f240,f62])).
% 1.82/0.60  fof(f240,plain,(
% 1.82/0.60    sP0(sK5,sK5,sK3,sK4,sK4) | ~v1_funct_1(sK5) | ~m1_pre_topc(sK4,sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | sK5 = k2_tmap_1(sK4,sK3,sK5,sK4) | ~sP2(sK3,sK4,sK5,sK4)),
% 1.82/0.60    inference(subsumption_resolution,[],[f235,f63])).
% 1.82/0.60  fof(f235,plain,(
% 1.82/0.60    sP0(sK5,sK5,sK3,sK4,sK4) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK5) | ~m1_pre_topc(sK4,sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | sK5 = k2_tmap_1(sK4,sK3,sK5,sK4) | ~sP2(sK3,sK4,sK5,sK4)),
% 1.82/0.60    inference(resolution,[],[f226,f64])).
% 1.82/0.60  fof(f226,plain,(
% 1.82/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) | sP0(sK5,X0,sK3,X1,sK4) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK4,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | sK5 = k2_tmap_1(X1,sK3,X0,sK4) | ~sP2(sK3,sK4,X0,X1)) )),
% 1.82/0.60    inference(subsumption_resolution,[],[f225,f57])).
% 1.82/0.60  fof(f225,plain,(
% 1.82/0.60    ( ! [X0,X1] : (sP0(sK5,X0,sK3,X1,sK4) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK4,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | v2_struct_0(sK3) | sK5 = k2_tmap_1(X1,sK3,X0,sK4) | ~sP2(sK3,sK4,X0,X1)) )),
% 1.82/0.60    inference(subsumption_resolution,[],[f224,f58])).
% 1.82/0.60  fof(f224,plain,(
% 1.82/0.60    ( ! [X0,X1] : (sP0(sK5,X0,sK3,X1,sK4) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK4,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | sK5 = k2_tmap_1(X1,sK3,X0,sK4) | ~sP2(sK3,sK4,X0,X1)) )),
% 1.82/0.60    inference(subsumption_resolution,[],[f223,f59])).
% 1.82/0.60  fof(f223,plain,(
% 1.82/0.60    ( ! [X0,X1] : (sP0(sK5,X0,sK3,X1,sK4) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK4,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | sK5 = k2_tmap_1(X1,sK3,X0,sK4) | ~sP2(sK3,sK4,X0,X1)) )),
% 1.82/0.60    inference(subsumption_resolution,[],[f222,f60])).
% 1.82/0.60  fof(f222,plain,(
% 1.82/0.60    ( ! [X0,X1] : (sP0(sK5,X0,sK3,X1,sK4) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK4,X1) | v2_struct_0(sK4) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | sK5 = k2_tmap_1(X1,sK3,X0,sK4) | ~sP2(sK3,sK4,X0,X1)) )),
% 1.82/0.60    inference(subsumption_resolution,[],[f221,f62])).
% 1.82/0.60  fof(f221,plain,(
% 1.82/0.60    ( ! [X0,X1] : (sP0(sK5,X0,sK3,X1,sK4) | ~v1_funct_1(sK5) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK4,X1) | v2_struct_0(sK4) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | sK5 = k2_tmap_1(X1,sK3,X0,sK4) | ~sP2(sK3,sK4,X0,X1)) )),
% 1.82/0.60    inference(subsumption_resolution,[],[f220,f63])).
% 1.82/0.60  fof(f220,plain,(
% 1.82/0.60    ( ! [X0,X1] : (sP0(sK5,X0,sK3,X1,sK4) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK5) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK4,X1) | v2_struct_0(sK4) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | sK5 = k2_tmap_1(X1,sK3,X0,sK4) | ~sP2(sK3,sK4,X0,X1)) )),
% 1.82/0.60    inference(subsumption_resolution,[],[f217,f64])).
% 1.82/0.60  fof(f217,plain,(
% 1.82/0.60    ( ! [X0,X1] : (sP0(sK5,X0,sK3,X1,sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK5) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK3)) | ~v1_funct_1(X0) | ~m1_pre_topc(sK4,X1) | v2_struct_0(sK4) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | sK5 = k2_tmap_1(X1,sK3,X0,sK4) | ~sP2(sK3,sK4,X0,X1)) )),
% 1.82/0.60    inference(resolution,[],[f74,f185])).
% 1.82/0.60  fof(f185,plain,(
% 1.82/0.60    ( ! [X0,X1] : (~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(X0,sK3,X1,sK4),sK5) | sK5 = k2_tmap_1(X0,sK3,X1,sK4) | ~sP2(sK3,sK4,X1,X0)) )),
% 1.82/0.60    inference(subsumption_resolution,[],[f184,f84])).
% 1.82/0.60  fof(f84,plain,(
% 1.82/0.60    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) | ~sP2(X0,X1,X2,X3)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f55])).
% 1.82/0.60  fof(f55,plain,(
% 1.82/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X3,X0,X2,X1))) | ~sP2(X0,X1,X2,X3))),
% 1.82/0.60    inference(rectify,[],[f54])).
% 1.82/0.60  fof(f54,plain,(
% 1.82/0.60    ! [X1,X3,X2,X0] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~sP2(X1,X3,X2,X0))),
% 1.82/0.60    inference(nnf_transformation,[],[f43])).
% 1.82/0.60  fof(f184,plain,(
% 1.82/0.60    ( ! [X0,X1] : (sK5 = k2_tmap_1(X0,sK3,X1,sK4) | ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(X0,sK3,X1,sK4),sK5) | ~v1_funct_1(k2_tmap_1(X0,sK3,X1,sK4)) | ~sP2(sK3,sK4,X1,X0)) )),
% 1.82/0.60    inference(subsumption_resolution,[],[f181,f85])).
% 1.82/0.60  fof(f85,plain,(
% 1.82/0.60    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~sP2(X0,X1,X2,X3)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f55])).
% 1.82/0.60  fof(f181,plain,(
% 1.82/0.60    ( ! [X0,X1] : (sK5 = k2_tmap_1(X0,sK3,X1,sK4) | ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(X0,sK3,X1,sK4),sK5) | ~v1_funct_2(k2_tmap_1(X0,sK3,X1,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(X0,sK3,X1,sK4)) | ~sP2(sK3,sK4,X1,X0)) )),
% 1.82/0.60    inference(resolution,[],[f180,f86])).
% 1.82/0.60  fof(f86,plain,(
% 1.82/0.60    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~sP2(X0,X1,X2,X3)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f55])).
% 1.82/0.60  fof(f180,plain,(
% 1.82/0.60    ( ! [X8] : (~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | sK5 = X8 | ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),X8,sK5) | ~v1_funct_2(X8,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(X8)) )),
% 1.82/0.60    inference(subsumption_resolution,[],[f179,f62])).
% 1.82/0.60  fof(f179,plain,(
% 1.82/0.60    ( ! [X8] : (~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),X8,sK5) | sK5 = X8 | ~v1_funct_1(sK5) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(X8,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(X8)) )),
% 1.82/0.60    inference(subsumption_resolution,[],[f174,f63])).
% 1.82/0.60  fof(f174,plain,(
% 1.82/0.60    ( ! [X8] : (~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),X8,sK5) | sK5 = X8 | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK5) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(X8,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(X8)) )),
% 1.82/0.60    inference(resolution,[],[f88,f64])).
% 1.82/0.60  fof(f158,plain,(
% 1.82/0.60    spl7_3 | spl7_4),
% 1.82/0.60    inference(avatar_split_clause,[],[f150,f156,f152])).
% 1.82/0.60  fof(f150,plain,(
% 1.82/0.60    ( ! [X8] : (~m1_subset_1(X8,u1_struct_0(sK4)) | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X8) = k1_funct_1(sK5,X8) | v1_xboole_0(u1_struct_0(sK4))) )),
% 1.82/0.60    inference(subsumption_resolution,[],[f149,f62])).
% 1.82/0.60  fof(f149,plain,(
% 1.82/0.60    ( ! [X8] : (~m1_subset_1(X8,u1_struct_0(sK4)) | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X8) = k1_funct_1(sK5,X8) | ~v1_funct_1(sK5) | v1_xboole_0(u1_struct_0(sK4))) )),
% 1.82/0.60    inference(subsumption_resolution,[],[f144,f63])).
% 1.82/0.60  fof(f144,plain,(
% 1.82/0.60    ( ! [X8] : (~m1_subset_1(X8,u1_struct_0(sK4)) | k3_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),sK5,X8) = k1_funct_1(sK5,X8) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(sK5) | v1_xboole_0(u1_struct_0(sK4))) )),
% 1.82/0.60    inference(resolution,[],[f83,f64])).
% 1.82/0.60  fof(f83,plain,(
% 1.82/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 1.82/0.60    inference(cnf_transformation,[],[f34])).
% 1.82/0.60  fof(f34,plain,(
% 1.82/0.60    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 1.82/0.60    inference(flattening,[],[f33])).
% 1.82/0.60  fof(f33,plain,(
% 1.82/0.60    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 1.82/0.60    inference(ennf_transformation,[],[f2])).
% 1.82/0.60  fof(f2,axiom,(
% 1.82/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 1.82/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 1.82/0.60  % SZS output end Proof for theBenchmark
% 1.82/0.60  % (15126)------------------------------
% 1.82/0.60  % (15126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.60  % (15126)Termination reason: Refutation
% 1.82/0.60  
% 1.82/0.60  % (15126)Memory used [KB]: 11385
% 1.82/0.60  % (15126)Time elapsed: 0.170 s
% 1.82/0.60  % (15126)------------------------------
% 1.82/0.60  % (15126)------------------------------
% 1.82/0.61  % (15095)Success in time 0.246 s
%------------------------------------------------------------------------------
