%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :  208 ( 565 expanded)
%              Number of leaves         :   54 ( 295 expanded)
%              Depth                    :    9
%              Number of atoms          :  913 (4640 expanded)
%              Number of equality atoms :   61 ( 313 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (22624)Refutation not found, incomplete strategy% (22624)------------------------------
% (22624)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (22624)Termination reason: Refutation not found, incomplete strategy

% (22624)Memory used [KB]: 10746
% (22624)Time elapsed: 0.143 s
% (22624)------------------------------
% (22624)------------------------------
fof(f779,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f96,f101,f106,f111,f116,f121,f126,f131,f136,f141,f146,f151,f156,f161,f168,f173,f179,f192,f209,f215,f282,f298,f320,f326,f348,f366,f389,f408,f433,f642,f711,f736,f774])).

fof(f774,plain,
    ( spl7_53
    | ~ spl7_52
    | ~ spl7_97
    | ~ spl7_102 ),
    inference(avatar_split_clause,[],[f773,f733,f708,f401,f405])).

fof(f405,plain,
    ( spl7_53
  <=> k1_funct_1(sK4,sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) = k1_funct_1(sK3,sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f401,plain,
    ( spl7_52
  <=> r2_hidden(sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f708,plain,
    ( spl7_97
  <=> m1_subset_1(sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_97])])).

fof(f733,plain,
    ( spl7_102
  <=> k1_funct_1(sK3,sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_102])])).

fof(f773,plain,
    ( k1_funct_1(sK4,sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) = k1_funct_1(sK3,sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4))
    | ~ spl7_52
    | ~ spl7_97
    | ~ spl7_102 ),
    inference(forward_demodulation,[],[f749,f735])).

fof(f735,plain,
    ( k1_funct_1(sK3,sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4))
    | ~ spl7_102 ),
    inference(avatar_component_clause,[],[f733])).

fof(f749,plain,
    ( k1_funct_1(sK4,sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4))
    | ~ spl7_52
    | ~ spl7_97 ),
    inference(unit_resulting_resolution,[],[f402,f710,f65])).

fof(f65,plain,(
    ! [X5] :
      ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5) = k1_funct_1(sK4,X5)
      | ~ r2_hidden(X5,u1_struct_0(sK2))
      | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)
    & ! [X5] :
        ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5) = k1_funct_1(sK4,X5)
        | ~ r2_hidden(X5,u1_struct_0(sK2))
        | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    & v1_funct_1(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f18,f45,f44,f43,f42,f41])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                        & ! [X5] :
                            ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5)
                            | ~ r2_hidden(X5,u1_struct_0(X2))
                            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                & m1_pre_topc(X2,X1)
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
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(X1,sK0,X3,X2),X4)
                      & ! [X5] :
                          ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(sK0),X3,X5)
                          | ~ r2_hidden(X5,u1_struct_0(X2))
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK0))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(X1,sK0,X3,X2),X4)
                    & ! [X5] :
                        ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(sK0),X3,X5)
                        | ~ r2_hidden(X5,u1_struct_0(X2))
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK0))
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0))
                & v1_funct_1(X3) )
            & m1_pre_topc(X2,X1)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X3,X2),X4)
                  & ! [X5] :
                      ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X3,X5)
                      | ~ r2_hidden(X5,u1_struct_0(X2))
                      | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
                  & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK0))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
              & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0))
              & v1_funct_1(X3) )
          & m1_pre_topc(X2,sK1)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X3,X2),X4)
                & ! [X5] :
                    ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X3,X5)
                    | ~ r2_hidden(X5,u1_struct_0(X2))
                    | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
                & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK0))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
            & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0))
            & v1_funct_1(X3) )
        & m1_pre_topc(X2,sK1)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X3,sK2),X4)
              & ! [X5] :
                  ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X3,X5)
                  | ~ r2_hidden(X5,u1_struct_0(sK2))
                  | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
              & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK0))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
          & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0))
          & v1_funct_1(X3) )
      & m1_pre_topc(sK2,sK1)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X3,sK2),X4)
            & ! [X5] :
                ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X3,X5)
                | ~ r2_hidden(X5,u1_struct_0(sK2))
                | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
            & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK0))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),X4)
          & ! [X5] :
              ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5)
              | ~ r2_hidden(X5,u1_struct_0(sK2))
              | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
          & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK0))
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X4] :
        ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),X4)
        & ! [X5] :
            ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5)
            | ~ r2_hidden(X5,u1_struct_0(sK2))
            | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
        & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK0))
        & v1_funct_1(X4) )
   => ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)
      & ! [X5] :
          ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5) = k1_funct_1(sK4,X5)
          | ~ r2_hidden(X5,u1_struct_0(sK2))
          | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
      & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & ! [X5] :
                          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5)
                          | ~ r2_hidden(X5,u1_struct_0(X2))
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & ! [X5] :
                          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5)
                          | ~ r2_hidden(X5,u1_struct_0(X2))
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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

fof(f710,plain,
    ( m1_subset_1(sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK1))
    | ~ spl7_97 ),
    inference(avatar_component_clause,[],[f708])).

fof(f402,plain,
    ( r2_hidden(sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2))
    | ~ spl7_52 ),
    inference(avatar_component_clause,[],[f401])).

fof(f736,plain,
    ( spl7_102
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | spl7_12
    | ~ spl7_17
    | ~ spl7_23
    | ~ spl7_52 ),
    inference(avatar_split_clause,[],[f700,f401,f206,f170,f143,f118,f113,f108,f733])).

fof(f108,plain,
    ( spl7_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f113,plain,
    ( spl7_6
  <=> v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f118,plain,
    ( spl7_7
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f143,plain,
    ( spl7_12
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f170,plain,
    ( spl7_17
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f206,plain,
    ( spl7_23
  <=> m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f700,plain,
    ( k1_funct_1(sK3,sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4))
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | spl7_12
    | ~ spl7_17
    | ~ spl7_23
    | ~ spl7_52 ),
    inference(unit_resulting_resolution,[],[f172,f120,f145,f115,f110,f208,f402,f409])).

fof(f409,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X4)
      | ~ v1_funct_2(X0,u1_struct_0(X1),X2)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,X3) = k3_funct_2(u1_struct_0(X1),X2,X0,X3)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),X2))) ) ),
    inference(resolution,[],[f218,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f218,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),X3)))
      | ~ v1_funct_2(X2,u1_struct_0(X1),X3)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = k3_funct_2(u1_struct_0(X1),X3,X2,X0)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f75,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f208,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f206])).

fof(f110,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f108])).

fof(f115,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f113])).

fof(f145,plain,
    ( ~ v2_struct_0(sK1)
    | spl7_12 ),
    inference(avatar_component_clause,[],[f143])).

fof(f120,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f118])).

fof(f172,plain,
    ( l1_struct_0(sK1)
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f170])).

fof(f711,plain,
    ( spl7_97
    | ~ spl7_23
    | ~ spl7_52 ),
    inference(avatar_split_clause,[],[f705,f401,f206,f708])).

fof(f705,plain,
    ( m1_subset_1(sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK1))
    | ~ spl7_23
    | ~ spl7_52 ),
    inference(unit_resulting_resolution,[],[f208,f402,f77])).

fof(f642,plain,
    ( spl7_56
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_37
    | spl7_38
    | ~ spl7_40
    | ~ spl7_44 ),
    inference(avatar_split_clause,[],[f633,f345,f323,f295,f290,f103,f98,f93,f429])).

fof(f429,plain,
    ( spl7_56
  <=> m1_subset_1(sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f93,plain,
    ( spl7_2
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f98,plain,
    ( spl7_3
  <=> v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f103,plain,
    ( spl7_4
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f290,plain,
    ( spl7_37
  <=> v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f295,plain,
    ( spl7_38
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f323,plain,
    ( spl7_40
  <=> m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f345,plain,
    ( spl7_44
  <=> v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f633,plain,
    ( m1_subset_1(sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_37
    | spl7_38
    | ~ spl7_40
    | ~ spl7_44 ),
    inference(unit_resulting_resolution,[],[f105,f291,f100,f95,f347,f297,f325,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK5(X0,X2,X3),X0)
      | r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ( k1_funct_1(X2,sK5(X0,X2,X3)) != k1_funct_1(X3,sK5(X0,X2,X3))
                & m1_subset_1(sK5(X0,X2,X3),X0) ) )
            & ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                  | ~ m1_subset_1(X5,X0) )
              | ~ r2_funct_2(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f48,f49])).

fof(f49,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & m1_subset_1(X4,X0) )
     => ( k1_funct_1(X2,sK5(X0,X2,X3)) != k1_funct_1(X3,sK5(X0,X2,X3))
        & m1_subset_1(sK5(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                  | ~ m1_subset_1(X5,X0) )
              | ~ r2_funct_2(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X4] :
                  ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                  | ~ m1_subset_1(X4,X0) )
              | ~ r2_funct_2(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_2)).

fof(f325,plain,
    ( m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ spl7_40 ),
    inference(avatar_component_clause,[],[f323])).

fof(f297,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)
    | spl7_38 ),
    inference(avatar_component_clause,[],[f295])).

fof(f347,plain,
    ( v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f345])).

fof(f95,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f100,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f98])).

fof(f291,plain,
    ( v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f290])).

fof(f105,plain,
    ( v1_funct_1(sK4)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f103])).

fof(f433,plain,
    ( ~ spl7_56
    | spl7_39
    | spl7_52 ),
    inference(avatar_split_clause,[],[f427,f401,f317,f429])).

fof(f317,plain,
    ( spl7_39
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f427,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2))
    | spl7_52 ),
    inference(resolution,[],[f403,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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

fof(f403,plain,
    ( ~ r2_hidden(sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2))
    | spl7_52 ),
    inference(avatar_component_clause,[],[f401])).

fof(f408,plain,
    ( ~ spl7_20
    | ~ spl7_7
    | ~ spl7_52
    | ~ spl7_53
    | spl7_51 ),
    inference(avatar_split_clause,[],[f399,f386,f405,f401,f118,f189])).

fof(f189,plain,
    ( spl7_20
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f386,plain,
    ( spl7_51
  <=> k1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) = k1_funct_1(sK4,sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).

fof(f399,plain,
    ( k1_funct_1(sK4,sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK3,sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4))
    | ~ r2_hidden(sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl7_51 ),
    inference(superposition,[],[f388,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,X1)
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_funct_1)).

fof(f388,plain,
    ( k1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4))
    | spl7_51 ),
    inference(avatar_component_clause,[],[f386])).

fof(f389,plain,
    ( ~ spl7_37
    | ~ spl7_44
    | ~ spl7_40
    | ~ spl7_4
    | ~ spl7_3
    | ~ spl7_2
    | ~ spl7_51
    | spl7_38 ),
    inference(avatar_split_clause,[],[f299,f295,f386,f93,f98,f103,f323,f345,f290])).

fof(f299,plain,
    ( k1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)))
    | spl7_38 ),
    inference(resolution,[],[f297,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | k1_funct_1(X2,sK5(X0,X2,X3)) != k1_funct_1(X3,sK5(X0,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f366,plain,
    ( spl7_37
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_24
    | ~ spl7_35 ),
    inference(avatar_split_clause,[],[f365,f279,f212,f170,f165,f118,f113,f108,f290])).

fof(f165,plain,
    ( spl7_16
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f212,plain,
    ( spl7_24
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f279,plain,
    ( spl7_35
  <=> k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f365,plain,
    ( v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_24
    | ~ spl7_35 ),
    inference(forward_demodulation,[],[f304,f281])).

fof(f281,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2))
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f279])).

fof(f304,plain,
    ( v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2))
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_24 ),
    inference(unit_resulting_resolution,[],[f172,f167,f120,f115,f110,f214,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(f214,plain,
    ( l1_struct_0(sK2)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f212])).

fof(f167,plain,
    ( l1_struct_0(sK0)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f165])).

fof(f348,plain,
    ( spl7_44
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_24
    | ~ spl7_35 ),
    inference(avatar_split_clause,[],[f343,f279,f212,f170,f165,f118,f113,f108,f345])).

fof(f343,plain,
    ( v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_24
    | ~ spl7_35 ),
    inference(forward_demodulation,[],[f309,f281])).

fof(f309,plain,
    ( v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_24 ),
    inference(unit_resulting_resolution,[],[f172,f167,f120,f115,f110,f214,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f326,plain,
    ( spl7_40
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_24
    | ~ spl7_35 ),
    inference(avatar_split_clause,[],[f321,f279,f212,f170,f165,f118,f113,f108,f323])).

fof(f321,plain,
    ( m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_24
    | ~ spl7_35 ),
    inference(forward_demodulation,[],[f314,f281])).

fof(f314,plain,
    ( m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_24 ),
    inference(unit_resulting_resolution,[],[f172,f167,f120,f115,f110,f214,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f320,plain,
    ( ~ spl7_39
    | spl7_9
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f315,f212,f128,f317])).

fof(f128,plain,
    ( spl7_9
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f315,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | spl7_9
    | ~ spl7_24 ),
    inference(unit_resulting_resolution,[],[f130,f214,f82])).

fof(f130,plain,
    ( ~ v2_struct_0(sK2)
    | spl7_9 ),
    inference(avatar_component_clause,[],[f128])).

fof(f298,plain,
    ( ~ spl7_38
    | spl7_1
    | ~ spl7_35 ),
    inference(avatar_split_clause,[],[f288,f279,f88,f295])).

fof(f88,plain,
    ( spl7_1
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f288,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)
    | spl7_1
    | ~ spl7_35 ),
    inference(backward_demodulation,[],[f90,f281])).

fof(f90,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f282,plain,
    ( spl7_35
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_11
    | spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | spl7_15 ),
    inference(avatar_split_clause,[],[f277,f158,f153,f148,f143,f138,f133,f123,f118,f113,f108,f279])).

fof(f123,plain,
    ( spl7_8
  <=> m1_pre_topc(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f133,plain,
    ( spl7_10
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f138,plain,
    ( spl7_11
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f148,plain,
    ( spl7_13
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f153,plain,
    ( spl7_14
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f158,plain,
    ( spl7_15
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f277,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2))
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_11
    | spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | spl7_15 ),
    inference(forward_demodulation,[],[f275,f217])).

fof(f217,plain,
    ( ! [X0] : k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0)
    | ~ spl7_5
    | ~ spl7_7 ),
    inference(unit_resulting_resolution,[],[f120,f110,f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f275,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_11
    | spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | spl7_15 ),
    inference(unit_resulting_resolution,[],[f145,f140,f135,f160,f155,f150,f120,f125,f115,f110,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_pre_topc(X3,X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f125,plain,
    ( m1_pre_topc(sK2,sK1)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f123])).

fof(f150,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f148])).

fof(f155,plain,
    ( v2_pre_topc(sK0)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f153])).

fof(f160,plain,
    ( ~ v2_struct_0(sK0)
    | spl7_15 ),
    inference(avatar_component_clause,[],[f158])).

fof(f135,plain,
    ( l1_pre_topc(sK1)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f133])).

fof(f140,plain,
    ( v2_pre_topc(sK1)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f138])).

fof(f215,plain,
    ( spl7_24
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f210,f176,f212])).

fof(f176,plain,
    ( spl7_18
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f210,plain,
    ( l1_struct_0(sK2)
    | ~ spl7_18 ),
    inference(unit_resulting_resolution,[],[f178,f84])).

fof(f84,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f178,plain,
    ( l1_pre_topc(sK2)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f176])).

fof(f209,plain,
    ( spl7_23
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f204,f133,f123,f206])).

fof(f204,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f135,f125,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f192,plain,
    ( spl7_20
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f187,f108,f189])).

fof(f187,plain,
    ( v1_relat_1(sK3)
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f81,f110,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f81,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f179,plain,
    ( spl7_18
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f174,f133,f123,f176])).

fof(f174,plain,
    ( l1_pre_topc(sK2)
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f135,f125,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f173,plain,
    ( spl7_17
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f162,f133,f170])).

fof(f162,plain,
    ( l1_struct_0(sK1)
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f135,f84])).

fof(f168,plain,
    ( spl7_16
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f163,f148,f165])).

fof(f163,plain,
    ( l1_struct_0(sK0)
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f150,f84])).

fof(f161,plain,(
    ~ spl7_15 ),
    inference(avatar_split_clause,[],[f51,f158])).

fof(f51,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f156,plain,(
    spl7_14 ),
    inference(avatar_split_clause,[],[f52,f153])).

fof(f52,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f151,plain,(
    spl7_13 ),
    inference(avatar_split_clause,[],[f53,f148])).

fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f146,plain,(
    ~ spl7_12 ),
    inference(avatar_split_clause,[],[f54,f143])).

fof(f54,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f141,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f55,f138])).

fof(f55,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f136,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f56,f133])).

fof(f56,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f131,plain,(
    ~ spl7_9 ),
    inference(avatar_split_clause,[],[f57,f128])).

fof(f57,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f126,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f58,f123])).

fof(f58,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f121,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f59,f118])).

fof(f59,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f116,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f60,f113])).

fof(f60,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f111,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f61,f108])).

fof(f61,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f46])).

fof(f106,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f62,f103])).

fof(f62,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f101,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f63,f98])).

fof(f63,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f96,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f64,f93])).

fof(f64,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f46])).

fof(f91,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f66,f88])).

fof(f66,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:31:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (22621)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.46  % (22613)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.49  % (22608)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (22623)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.49  % (22606)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.50  % (22615)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.50  % (22603)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.50  % (22604)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.50  % (22604)Refutation not found, incomplete strategy% (22604)------------------------------
% 0.20/0.50  % (22604)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (22604)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (22604)Memory used [KB]: 10746
% 0.20/0.50  % (22604)Time elapsed: 0.094 s
% 0.20/0.50  % (22604)------------------------------
% 0.20/0.50  % (22604)------------------------------
% 0.20/0.50  % (22622)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.50  % (22602)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.50  % (22607)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.51  % (22611)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.51  % (22601)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.51  % (22605)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.51  % (22618)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.51  % (22619)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.51  % (22610)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.51  % (22624)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.51  % (22620)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.52  % (22614)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.52  % (22609)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.52  % (22616)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.52  % (22609)Refutation not found, incomplete strategy% (22609)------------------------------
% 0.20/0.52  % (22609)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (22609)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (22609)Memory used [KB]: 10874
% 0.20/0.52  % (22609)Time elapsed: 0.120 s
% 0.20/0.52  % (22609)------------------------------
% 0.20/0.52  % (22609)------------------------------
% 0.20/0.52  % (22617)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.53  % (22612)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.54  % (22607)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  % (22624)Refutation not found, incomplete strategy% (22624)------------------------------
% 0.20/0.54  % (22624)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (22624)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (22624)Memory used [KB]: 10746
% 0.20/0.55  % (22624)Time elapsed: 0.143 s
% 0.20/0.55  % (22624)------------------------------
% 0.20/0.55  % (22624)------------------------------
% 1.60/0.56  fof(f779,plain,(
% 1.60/0.56    $false),
% 1.60/0.56    inference(avatar_sat_refutation,[],[f91,f96,f101,f106,f111,f116,f121,f126,f131,f136,f141,f146,f151,f156,f161,f168,f173,f179,f192,f209,f215,f282,f298,f320,f326,f348,f366,f389,f408,f433,f642,f711,f736,f774])).
% 1.60/0.56  fof(f774,plain,(
% 1.60/0.56    spl7_53 | ~spl7_52 | ~spl7_97 | ~spl7_102),
% 1.60/0.56    inference(avatar_split_clause,[],[f773,f733,f708,f401,f405])).
% 1.60/0.56  fof(f405,plain,(
% 1.60/0.56    spl7_53 <=> k1_funct_1(sK4,sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) = k1_funct_1(sK3,sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4))),
% 1.60/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).
% 1.60/0.56  fof(f401,plain,(
% 1.60/0.56    spl7_52 <=> r2_hidden(sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2))),
% 1.60/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).
% 1.60/0.56  fof(f708,plain,(
% 1.60/0.56    spl7_97 <=> m1_subset_1(sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK1))),
% 1.60/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_97])])).
% 1.60/0.56  fof(f733,plain,(
% 1.60/0.56    spl7_102 <=> k1_funct_1(sK3,sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4))),
% 1.60/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_102])])).
% 1.60/0.56  fof(f773,plain,(
% 1.60/0.56    k1_funct_1(sK4,sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) = k1_funct_1(sK3,sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) | (~spl7_52 | ~spl7_97 | ~spl7_102)),
% 1.60/0.56    inference(forward_demodulation,[],[f749,f735])).
% 1.60/0.56  fof(f735,plain,(
% 1.60/0.56    k1_funct_1(sK3,sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) | ~spl7_102),
% 1.60/0.56    inference(avatar_component_clause,[],[f733])).
% 1.60/0.56  fof(f749,plain,(
% 1.60/0.56    k1_funct_1(sK4,sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) | (~spl7_52 | ~spl7_97)),
% 1.60/0.56    inference(unit_resulting_resolution,[],[f402,f710,f65])).
% 1.60/0.56  fof(f65,plain,(
% 1.60/0.56    ( ! [X5] : (k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5) = k1_funct_1(sK4,X5) | ~r2_hidden(X5,u1_struct_0(sK2)) | ~m1_subset_1(X5,u1_struct_0(sK1))) )),
% 1.60/0.56    inference(cnf_transformation,[],[f46])).
% 1.60/0.56  fof(f46,plain,(
% 1.60/0.56    ((((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) & ! [X5] : (k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5) = k1_funct_1(sK4,X5) | ~r2_hidden(X5,u1_struct_0(sK2)) | ~m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0)) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.60/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f18,f45,f44,f43,f42,f41])).
% 1.60/0.56  fof(f41,plain,(
% 1.60/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & ! [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(X1,sK0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(sK0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.60/0.56    introduced(choice_axiom,[])).
% 1.60/0.56  fof(f42,plain,(
% 1.60/0.56    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(X1,sK0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(sK0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.60/0.56    introduced(choice_axiom,[])).
% 1.60/0.56  fof(f43,plain,(
% 1.60/0.56    ? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X3,sK2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X3,X5) | ~r2_hidden(X5,u1_struct_0(sK2)) | ~m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2))),
% 1.60/0.56    introduced(choice_axiom,[])).
% 1.60/0.56  fof(f44,plain,(
% 1.60/0.56    ? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X3,sK2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X3,X5) | ~r2_hidden(X5,u1_struct_0(sK2)) | ~m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X3)) => (? [X4] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5) | ~r2_hidden(X5,u1_struct_0(sK2)) | ~m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK3))),
% 1.60/0.56    introduced(choice_axiom,[])).
% 1.60/0.56  fof(f45,plain,(
% 1.60/0.56    ? [X4] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5) | ~r2_hidden(X5,u1_struct_0(sK2)) | ~m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK0)) & v1_funct_1(X4)) => (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) & ! [X5] : (k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5) = k1_funct_1(sK4,X5) | ~r2_hidden(X5,u1_struct_0(sK2)) | ~m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0)) & v1_funct_1(sK4))),
% 1.60/0.56    introduced(choice_axiom,[])).
% 1.60/0.56  fof(f18,plain,(
% 1.60/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & ! [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.60/0.56    inference(flattening,[],[f17])).
% 1.60/0.56  fof(f17,plain,(
% 1.60/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & ! [X5] : ((k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5) | ~r2_hidden(X5,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X1)))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.60/0.56    inference(ennf_transformation,[],[f16])).
% 1.60/0.56  fof(f16,negated_conjecture,(
% 1.60/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => (r2_hidden(X5,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 1.60/0.56    inference(negated_conjecture,[],[f15])).
% 1.60/0.56  fof(f15,conjecture,(
% 1.60/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => (r2_hidden(X5,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 1.60/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_tmap_1)).
% 1.60/0.56  fof(f710,plain,(
% 1.60/0.56    m1_subset_1(sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK1)) | ~spl7_97),
% 1.60/0.56    inference(avatar_component_clause,[],[f708])).
% 1.60/0.56  fof(f402,plain,(
% 1.60/0.56    r2_hidden(sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2)) | ~spl7_52),
% 1.60/0.56    inference(avatar_component_clause,[],[f401])).
% 1.60/0.56  fof(f736,plain,(
% 1.60/0.56    spl7_102 | ~spl7_5 | ~spl7_6 | ~spl7_7 | spl7_12 | ~spl7_17 | ~spl7_23 | ~spl7_52),
% 1.60/0.56    inference(avatar_split_clause,[],[f700,f401,f206,f170,f143,f118,f113,f108,f733])).
% 1.60/0.56  fof(f108,plain,(
% 1.60/0.56    spl7_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.60/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.60/0.56  fof(f113,plain,(
% 1.60/0.56    spl7_6 <=> v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.60/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.60/0.56  fof(f118,plain,(
% 1.60/0.56    spl7_7 <=> v1_funct_1(sK3)),
% 1.60/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.60/0.56  fof(f143,plain,(
% 1.60/0.56    spl7_12 <=> v2_struct_0(sK1)),
% 1.60/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 1.60/0.56  fof(f170,plain,(
% 1.60/0.56    spl7_17 <=> l1_struct_0(sK1)),
% 1.60/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 1.60/0.56  fof(f206,plain,(
% 1.60/0.56    spl7_23 <=> m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.60/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 1.60/0.56  fof(f700,plain,(
% 1.60/0.56    k1_funct_1(sK3,sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) | (~spl7_5 | ~spl7_6 | ~spl7_7 | spl7_12 | ~spl7_17 | ~spl7_23 | ~spl7_52)),
% 1.60/0.56    inference(unit_resulting_resolution,[],[f172,f120,f145,f115,f110,f208,f402,f409])).
% 1.60/0.56  fof(f409,plain,(
% 1.60/0.56    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X3,X4) | ~v1_funct_2(X0,u1_struct_0(X1),X2) | ~v1_funct_1(X0) | k1_funct_1(X0,X3) = k3_funct_2(u1_struct_0(X1),X2,X0,X3) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),X2)))) )),
% 1.60/0.56    inference(resolution,[],[f218,f77])).
% 1.60/0.56  fof(f77,plain,(
% 1.60/0.56    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.60/0.56    inference(cnf_transformation,[],[f32])).
% 1.60/0.56  fof(f32,plain,(
% 1.60/0.56    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.60/0.56    inference(flattening,[],[f31])).
% 1.60/0.56  fof(f31,plain,(
% 1.60/0.56    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.60/0.56    inference(ennf_transformation,[],[f2])).
% 1.60/0.56  fof(f2,axiom,(
% 1.60/0.56    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.60/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.60/0.56  fof(f218,plain,(
% 1.60/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),X3))) | ~v1_funct_2(X2,u1_struct_0(X1),X3) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = k3_funct_2(u1_struct_0(X1),X3,X2,X0) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 1.60/0.56    inference(resolution,[],[f75,f82])).
% 1.60/0.56  fof(f82,plain,(
% 1.60/0.56    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.60/0.56    inference(cnf_transformation,[],[f38])).
% 1.60/0.56  fof(f38,plain,(
% 1.60/0.56    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.60/0.56    inference(flattening,[],[f37])).
% 1.60/0.56  fof(f37,plain,(
% 1.60/0.56    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.60/0.56    inference(ennf_transformation,[],[f11])).
% 1.60/0.56  fof(f11,axiom,(
% 1.60/0.56    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.60/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.60/0.56  fof(f75,plain,(
% 1.60/0.56    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 1.60/0.56    inference(cnf_transformation,[],[f28])).
% 1.60/0.56  fof(f28,plain,(
% 1.60/0.56    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 1.60/0.56    inference(flattening,[],[f27])).
% 1.60/0.56  fof(f27,plain,(
% 1.60/0.56    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 1.60/0.56    inference(ennf_transformation,[],[f8])).
% 1.60/0.56  fof(f8,axiom,(
% 1.60/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 1.60/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 1.60/0.56  fof(f208,plain,(
% 1.60/0.56    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl7_23),
% 1.60/0.56    inference(avatar_component_clause,[],[f206])).
% 1.60/0.56  fof(f110,plain,(
% 1.60/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~spl7_5),
% 1.60/0.56    inference(avatar_component_clause,[],[f108])).
% 1.60/0.56  fof(f115,plain,(
% 1.60/0.56    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~spl7_6),
% 1.60/0.56    inference(avatar_component_clause,[],[f113])).
% 1.60/0.56  fof(f145,plain,(
% 1.60/0.56    ~v2_struct_0(sK1) | spl7_12),
% 1.60/0.56    inference(avatar_component_clause,[],[f143])).
% 1.60/0.56  fof(f120,plain,(
% 1.60/0.56    v1_funct_1(sK3) | ~spl7_7),
% 1.60/0.56    inference(avatar_component_clause,[],[f118])).
% 1.60/0.56  fof(f172,plain,(
% 1.60/0.56    l1_struct_0(sK1) | ~spl7_17),
% 1.60/0.56    inference(avatar_component_clause,[],[f170])).
% 1.60/0.56  fof(f711,plain,(
% 1.60/0.56    spl7_97 | ~spl7_23 | ~spl7_52),
% 1.60/0.56    inference(avatar_split_clause,[],[f705,f401,f206,f708])).
% 1.60/0.56  fof(f705,plain,(
% 1.60/0.56    m1_subset_1(sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK1)) | (~spl7_23 | ~spl7_52)),
% 1.60/0.56    inference(unit_resulting_resolution,[],[f208,f402,f77])).
% 1.60/0.56  fof(f642,plain,(
% 1.60/0.56    spl7_56 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_37 | spl7_38 | ~spl7_40 | ~spl7_44),
% 1.60/0.56    inference(avatar_split_clause,[],[f633,f345,f323,f295,f290,f103,f98,f93,f429])).
% 1.60/0.56  fof(f429,plain,(
% 1.60/0.56    spl7_56 <=> m1_subset_1(sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2))),
% 1.60/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).
% 1.60/0.56  fof(f93,plain,(
% 1.60/0.56    spl7_2 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))),
% 1.60/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.60/0.56  fof(f98,plain,(
% 1.60/0.56    spl7_3 <=> v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))),
% 1.60/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.60/0.56  fof(f103,plain,(
% 1.60/0.56    spl7_4 <=> v1_funct_1(sK4)),
% 1.60/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.60/0.56  fof(f290,plain,(
% 1.60/0.56    spl7_37 <=> v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)))),
% 1.60/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).
% 1.60/0.56  fof(f295,plain,(
% 1.60/0.56    spl7_38 <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)),
% 1.60/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).
% 1.60/0.56  fof(f323,plain,(
% 1.60/0.56    spl7_40 <=> m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))),
% 1.60/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).
% 1.60/0.56  fof(f345,plain,(
% 1.60/0.56    spl7_44 <=> v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0))),
% 1.60/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).
% 1.60/0.56  fof(f633,plain,(
% 1.60/0.56    m1_subset_1(sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2)) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_37 | spl7_38 | ~spl7_40 | ~spl7_44)),
% 1.60/0.56    inference(unit_resulting_resolution,[],[f105,f291,f100,f95,f347,f297,f325,f68])).
% 1.60/0.56  fof(f68,plain,(
% 1.60/0.56    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK5(X0,X2,X3),X0) | r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.60/0.56    inference(cnf_transformation,[],[f50])).
% 1.60/0.56  fof(f50,plain,(
% 1.60/0.56    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | (k1_funct_1(X2,sK5(X0,X2,X3)) != k1_funct_1(X3,sK5(X0,X2,X3)) & m1_subset_1(sK5(X0,X2,X3),X0))) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~m1_subset_1(X5,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.60/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f48,f49])).
% 1.60/0.56  fof(f49,plain,(
% 1.60/0.56    ! [X3,X2,X0] : (? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0)) => (k1_funct_1(X2,sK5(X0,X2,X3)) != k1_funct_1(X3,sK5(X0,X2,X3)) & m1_subset_1(sK5(X0,X2,X3),X0)))),
% 1.60/0.56    introduced(choice_axiom,[])).
% 1.60/0.56  fof(f48,plain,(
% 1.60/0.56    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0))) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~m1_subset_1(X5,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.60/0.56    inference(rectify,[],[f47])).
% 1.60/0.56  fof(f47,plain,(
% 1.60/0.56    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0))) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.60/0.56    inference(nnf_transformation,[],[f20])).
% 1.60/0.56  fof(f20,plain,(
% 1.60/0.56    ! [X0,X1,X2] : (! [X3] : ((r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.60/0.56    inference(flattening,[],[f19])).
% 1.60/0.56  fof(f19,plain,(
% 1.60/0.56    ! [X0,X1,X2] : (! [X3] : ((r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.60/0.56    inference(ennf_transformation,[],[f6])).
% 1.60/0.56  fof(f6,axiom,(
% 1.60/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)))))),
% 1.60/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_2)).
% 1.60/0.56  fof(f325,plain,(
% 1.60/0.56    m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~spl7_40),
% 1.60/0.56    inference(avatar_component_clause,[],[f323])).
% 1.60/0.56  fof(f297,plain,(
% 1.60/0.56    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) | spl7_38),
% 1.60/0.56    inference(avatar_component_clause,[],[f295])).
% 1.60/0.56  fof(f347,plain,(
% 1.60/0.56    v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) | ~spl7_44),
% 1.60/0.56    inference(avatar_component_clause,[],[f345])).
% 1.60/0.56  fof(f95,plain,(
% 1.60/0.56    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~spl7_2),
% 1.60/0.56    inference(avatar_component_clause,[],[f93])).
% 1.60/0.56  fof(f100,plain,(
% 1.60/0.56    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0)) | ~spl7_3),
% 1.60/0.56    inference(avatar_component_clause,[],[f98])).
% 1.60/0.56  fof(f291,plain,(
% 1.60/0.56    v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2))) | ~spl7_37),
% 1.60/0.56    inference(avatar_component_clause,[],[f290])).
% 1.60/0.56  fof(f105,plain,(
% 1.60/0.56    v1_funct_1(sK4) | ~spl7_4),
% 1.60/0.56    inference(avatar_component_clause,[],[f103])).
% 1.60/0.56  fof(f433,plain,(
% 1.60/0.56    ~spl7_56 | spl7_39 | spl7_52),
% 1.60/0.56    inference(avatar_split_clause,[],[f427,f401,f317,f429])).
% 1.60/0.56  fof(f317,plain,(
% 1.60/0.56    spl7_39 <=> v1_xboole_0(u1_struct_0(sK2))),
% 1.60/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).
% 1.60/0.56  fof(f427,plain,(
% 1.60/0.56    v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2)) | spl7_52),
% 1.60/0.56    inference(resolution,[],[f403,f78])).
% 1.60/0.56  fof(f78,plain,(
% 1.60/0.56    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.60/0.56    inference(cnf_transformation,[],[f34])).
% 1.60/0.56  fof(f34,plain,(
% 1.60/0.56    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.60/0.56    inference(flattening,[],[f33])).
% 1.60/0.56  fof(f33,plain,(
% 1.60/0.56    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.60/0.56    inference(ennf_transformation,[],[f1])).
% 1.60/0.56  fof(f1,axiom,(
% 1.60/0.56    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.60/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.60/0.56  fof(f403,plain,(
% 1.60/0.56    ~r2_hidden(sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2)) | spl7_52),
% 1.60/0.56    inference(avatar_component_clause,[],[f401])).
% 1.60/0.56  fof(f408,plain,(
% 1.60/0.56    ~spl7_20 | ~spl7_7 | ~spl7_52 | ~spl7_53 | spl7_51),
% 1.60/0.56    inference(avatar_split_clause,[],[f399,f386,f405,f401,f118,f189])).
% 1.60/0.56  fof(f189,plain,(
% 1.60/0.56    spl7_20 <=> v1_relat_1(sK3)),
% 1.60/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 1.60/0.56  fof(f386,plain,(
% 1.60/0.56    spl7_51 <=> k1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) = k1_funct_1(sK4,sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4))),
% 1.60/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).
% 1.60/0.56  fof(f399,plain,(
% 1.60/0.56    k1_funct_1(sK4,sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK3,sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) | ~r2_hidden(sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4),u1_struct_0(sK2)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl7_51),
% 1.60/0.56    inference(superposition,[],[f388,f76])).
% 1.60/0.56  fof(f76,plain,(
% 1.60/0.56    ( ! [X2,X0,X1] : (k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.60/0.56    inference(cnf_transformation,[],[f30])).
% 1.60/0.56  fof(f30,plain,(
% 1.60/0.56    ! [X0,X1,X2] : (k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.60/0.56    inference(flattening,[],[f29])).
% 1.60/0.56  fof(f29,plain,(
% 1.60/0.56    ! [X0,X1,X2] : ((k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.60/0.56    inference(ennf_transformation,[],[f5])).
% 1.60/0.56  fof(f5,axiom,(
% 1.60/0.56    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,X1) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 1.60/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_funct_1)).
% 1.60/0.56  fof(f388,plain,(
% 1.60/0.56    k1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) | spl7_51),
% 1.60/0.56    inference(avatar_component_clause,[],[f386])).
% 1.60/0.56  fof(f389,plain,(
% 1.60/0.56    ~spl7_37 | ~spl7_44 | ~spl7_40 | ~spl7_4 | ~spl7_3 | ~spl7_2 | ~spl7_51 | spl7_38),
% 1.60/0.56    inference(avatar_split_clause,[],[f299,f295,f386,f93,f98,f103,f323,f345,f290])).
% 1.60/0.56  fof(f299,plain,(
% 1.60/0.56    k1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) != k1_funct_1(sK4,sK5(u1_struct_0(sK2),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) | ~v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2))) | spl7_38),
% 1.60/0.56    inference(resolution,[],[f297,f69])).
% 1.60/0.56  fof(f69,plain,(
% 1.60/0.56    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | k1_funct_1(X2,sK5(X0,X2,X3)) != k1_funct_1(X3,sK5(X0,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.60/0.56    inference(cnf_transformation,[],[f50])).
% 1.60/0.56  fof(f366,plain,(
% 1.60/0.56    spl7_37 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_16 | ~spl7_17 | ~spl7_24 | ~spl7_35),
% 1.60/0.56    inference(avatar_split_clause,[],[f365,f279,f212,f170,f165,f118,f113,f108,f290])).
% 1.60/0.56  fof(f165,plain,(
% 1.60/0.56    spl7_16 <=> l1_struct_0(sK0)),
% 1.60/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 1.60/0.56  fof(f212,plain,(
% 1.60/0.56    spl7_24 <=> l1_struct_0(sK2)),
% 1.60/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 1.60/0.56  fof(f279,plain,(
% 1.60/0.56    spl7_35 <=> k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2))),
% 1.60/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 1.60/0.56  fof(f365,plain,(
% 1.60/0.56    v1_funct_1(k7_relat_1(sK3,u1_struct_0(sK2))) | (~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_16 | ~spl7_17 | ~spl7_24 | ~spl7_35)),
% 1.60/0.56    inference(forward_demodulation,[],[f304,f281])).
% 1.60/0.56  fof(f281,plain,(
% 1.60/0.56    k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) | ~spl7_35),
% 1.60/0.56    inference(avatar_component_clause,[],[f279])).
% 1.60/0.56  fof(f304,plain,(
% 1.60/0.56    v1_funct_1(k2_tmap_1(sK1,sK0,sK3,sK2)) | (~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_16 | ~spl7_17 | ~spl7_24)),
% 1.60/0.56    inference(unit_resulting_resolution,[],[f172,f167,f120,f115,f110,f214,f70])).
% 1.60/0.56  fof(f70,plain,(
% 1.60/0.56    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 1.60/0.56    inference(cnf_transformation,[],[f22])).
% 1.60/0.56  fof(f22,plain,(
% 1.60/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 1.60/0.56    inference(flattening,[],[f21])).
% 1.60/0.56  fof(f21,plain,(
% 1.60/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 1.60/0.56    inference(ennf_transformation,[],[f13])).
% 1.60/0.56  fof(f13,axiom,(
% 1.60/0.56    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 1.60/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tmap_1)).
% 1.60/0.56  fof(f214,plain,(
% 1.60/0.56    l1_struct_0(sK2) | ~spl7_24),
% 1.60/0.56    inference(avatar_component_clause,[],[f212])).
% 1.60/0.56  fof(f167,plain,(
% 1.60/0.56    l1_struct_0(sK0) | ~spl7_16),
% 1.60/0.56    inference(avatar_component_clause,[],[f165])).
% 1.60/0.56  fof(f348,plain,(
% 1.60/0.56    spl7_44 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_16 | ~spl7_17 | ~spl7_24 | ~spl7_35),
% 1.60/0.56    inference(avatar_split_clause,[],[f343,f279,f212,f170,f165,f118,f113,f108,f345])).
% 1.60/0.56  fof(f343,plain,(
% 1.60/0.56    v1_funct_2(k7_relat_1(sK3,u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK0)) | (~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_16 | ~spl7_17 | ~spl7_24 | ~spl7_35)),
% 1.60/0.56    inference(forward_demodulation,[],[f309,f281])).
% 1.60/0.56  fof(f309,plain,(
% 1.60/0.56    v1_funct_2(k2_tmap_1(sK1,sK0,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK0)) | (~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_16 | ~spl7_17 | ~spl7_24)),
% 1.60/0.56    inference(unit_resulting_resolution,[],[f172,f167,f120,f115,f110,f214,f71])).
% 1.60/0.56  fof(f71,plain,(
% 1.60/0.56    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 1.60/0.56    inference(cnf_transformation,[],[f22])).
% 1.60/0.56  fof(f326,plain,(
% 1.60/0.56    spl7_40 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_16 | ~spl7_17 | ~spl7_24 | ~spl7_35),
% 1.60/0.56    inference(avatar_split_clause,[],[f321,f279,f212,f170,f165,f118,f113,f108,f323])).
% 1.60/0.56  fof(f321,plain,(
% 1.60/0.56    m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | (~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_16 | ~spl7_17 | ~spl7_24 | ~spl7_35)),
% 1.60/0.56    inference(forward_demodulation,[],[f314,f281])).
% 1.60/0.56  fof(f314,plain,(
% 1.60/0.56    m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | (~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_16 | ~spl7_17 | ~spl7_24)),
% 1.60/0.56    inference(unit_resulting_resolution,[],[f172,f167,f120,f115,f110,f214,f72])).
% 1.60/0.56  fof(f72,plain,(
% 1.60/0.56    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 1.60/0.56    inference(cnf_transformation,[],[f22])).
% 1.60/0.56  fof(f320,plain,(
% 1.60/0.56    ~spl7_39 | spl7_9 | ~spl7_24),
% 1.60/0.56    inference(avatar_split_clause,[],[f315,f212,f128,f317])).
% 1.60/0.56  fof(f128,plain,(
% 1.60/0.56    spl7_9 <=> v2_struct_0(sK2)),
% 1.60/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.60/0.56  fof(f315,plain,(
% 1.60/0.56    ~v1_xboole_0(u1_struct_0(sK2)) | (spl7_9 | ~spl7_24)),
% 1.60/0.56    inference(unit_resulting_resolution,[],[f130,f214,f82])).
% 1.60/0.56  fof(f130,plain,(
% 1.60/0.56    ~v2_struct_0(sK2) | spl7_9),
% 1.60/0.56    inference(avatar_component_clause,[],[f128])).
% 1.60/0.56  fof(f298,plain,(
% 1.60/0.56    ~spl7_38 | spl7_1 | ~spl7_35),
% 1.60/0.56    inference(avatar_split_clause,[],[f288,f279,f88,f295])).
% 1.60/0.56  fof(f88,plain,(
% 1.60/0.56    spl7_1 <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)),
% 1.60/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.60/0.56  fof(f288,plain,(
% 1.60/0.56    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) | (spl7_1 | ~spl7_35)),
% 1.60/0.56    inference(backward_demodulation,[],[f90,f281])).
% 1.60/0.56  fof(f90,plain,(
% 1.60/0.56    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) | spl7_1),
% 1.60/0.56    inference(avatar_component_clause,[],[f88])).
% 1.60/0.56  fof(f282,plain,(
% 1.60/0.56    spl7_35 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_10 | ~spl7_11 | spl7_12 | ~spl7_13 | ~spl7_14 | spl7_15),
% 1.60/0.56    inference(avatar_split_clause,[],[f277,f158,f153,f148,f143,f138,f133,f123,f118,f113,f108,f279])).
% 1.60/0.56  fof(f123,plain,(
% 1.60/0.56    spl7_8 <=> m1_pre_topc(sK2,sK1)),
% 1.60/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.60/0.56  fof(f133,plain,(
% 1.60/0.56    spl7_10 <=> l1_pre_topc(sK1)),
% 1.60/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.60/0.56  fof(f138,plain,(
% 1.60/0.56    spl7_11 <=> v2_pre_topc(sK1)),
% 1.60/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 1.60/0.56  fof(f148,plain,(
% 1.60/0.56    spl7_13 <=> l1_pre_topc(sK0)),
% 1.60/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 1.60/0.56  fof(f153,plain,(
% 1.60/0.56    spl7_14 <=> v2_pre_topc(sK0)),
% 1.60/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 1.60/0.56  fof(f158,plain,(
% 1.60/0.56    spl7_15 <=> v2_struct_0(sK0)),
% 1.60/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 1.60/0.56  fof(f277,plain,(
% 1.60/0.56    k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) | (~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_10 | ~spl7_11 | spl7_12 | ~spl7_13 | ~spl7_14 | spl7_15)),
% 1.60/0.56    inference(forward_demodulation,[],[f275,f217])).
% 1.60/0.56  fof(f217,plain,(
% 1.60/0.56    ( ! [X0] : (k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0)) ) | (~spl7_5 | ~spl7_7)),
% 1.60/0.56    inference(unit_resulting_resolution,[],[f120,f110,f74])).
% 1.60/0.56  fof(f74,plain,(
% 1.60/0.56    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.60/0.56    inference(cnf_transformation,[],[f26])).
% 1.60/0.56  fof(f26,plain,(
% 1.60/0.56    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.60/0.56    inference(flattening,[],[f25])).
% 1.60/0.56  fof(f25,plain,(
% 1.60/0.56    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.60/0.56    inference(ennf_transformation,[],[f7])).
% 1.60/0.56  fof(f7,axiom,(
% 1.60/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.60/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.60/0.56  fof(f275,plain,(
% 1.60/0.56    k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) | (~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_10 | ~spl7_11 | spl7_12 | ~spl7_13 | ~spl7_14 | spl7_15)),
% 1.60/0.56    inference(unit_resulting_resolution,[],[f145,f140,f135,f160,f155,f150,f120,f125,f115,f110,f73])).
% 1.60/0.56  fof(f73,plain,(
% 1.60/0.56    ( ! [X2,X0,X3,X1] : (~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.60/0.56    inference(cnf_transformation,[],[f24])).
% 1.60/0.56  fof(f24,plain,(
% 1.60/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.60/0.56    inference(flattening,[],[f23])).
% 1.60/0.56  fof(f23,plain,(
% 1.60/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.60/0.56    inference(ennf_transformation,[],[f12])).
% 1.60/0.56  fof(f12,axiom,(
% 1.60/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 1.60/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 1.60/0.56  fof(f125,plain,(
% 1.60/0.56    m1_pre_topc(sK2,sK1) | ~spl7_8),
% 1.60/0.56    inference(avatar_component_clause,[],[f123])).
% 1.60/0.56  fof(f150,plain,(
% 1.60/0.56    l1_pre_topc(sK0) | ~spl7_13),
% 1.60/0.56    inference(avatar_component_clause,[],[f148])).
% 1.60/0.56  fof(f155,plain,(
% 1.60/0.56    v2_pre_topc(sK0) | ~spl7_14),
% 1.60/0.56    inference(avatar_component_clause,[],[f153])).
% 1.60/0.56  fof(f160,plain,(
% 1.60/0.56    ~v2_struct_0(sK0) | spl7_15),
% 1.60/0.56    inference(avatar_component_clause,[],[f158])).
% 1.60/0.56  fof(f135,plain,(
% 1.60/0.56    l1_pre_topc(sK1) | ~spl7_10),
% 1.60/0.56    inference(avatar_component_clause,[],[f133])).
% 1.60/0.56  fof(f140,plain,(
% 1.60/0.56    v2_pre_topc(sK1) | ~spl7_11),
% 1.60/0.56    inference(avatar_component_clause,[],[f138])).
% 1.60/0.56  fof(f215,plain,(
% 1.60/0.56    spl7_24 | ~spl7_18),
% 1.60/0.56    inference(avatar_split_clause,[],[f210,f176,f212])).
% 1.60/0.56  fof(f176,plain,(
% 1.60/0.56    spl7_18 <=> l1_pre_topc(sK2)),
% 1.60/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 1.60/0.56  fof(f210,plain,(
% 1.60/0.56    l1_struct_0(sK2) | ~spl7_18),
% 1.60/0.56    inference(unit_resulting_resolution,[],[f178,f84])).
% 1.60/0.56  fof(f84,plain,(
% 1.60/0.56    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.60/0.56    inference(cnf_transformation,[],[f40])).
% 1.60/0.56  fof(f40,plain,(
% 1.60/0.56    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.60/0.56    inference(ennf_transformation,[],[f9])).
% 1.60/0.56  fof(f9,axiom,(
% 1.60/0.56    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.60/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.60/0.56  fof(f178,plain,(
% 1.60/0.56    l1_pre_topc(sK2) | ~spl7_18),
% 1.60/0.56    inference(avatar_component_clause,[],[f176])).
% 1.60/0.56  fof(f209,plain,(
% 1.60/0.56    spl7_23 | ~spl7_8 | ~spl7_10),
% 1.60/0.56    inference(avatar_split_clause,[],[f204,f133,f123,f206])).
% 1.60/0.56  fof(f204,plain,(
% 1.60/0.56    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) | (~spl7_8 | ~spl7_10)),
% 1.60/0.56    inference(unit_resulting_resolution,[],[f135,f125,f79])).
% 1.60/0.56  fof(f79,plain,(
% 1.60/0.56    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.60/0.56    inference(cnf_transformation,[],[f35])).
% 1.60/0.56  fof(f35,plain,(
% 1.60/0.56    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.60/0.56    inference(ennf_transformation,[],[f14])).
% 1.60/0.56  fof(f14,axiom,(
% 1.60/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.60/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.60/0.56  fof(f192,plain,(
% 1.60/0.56    spl7_20 | ~spl7_5),
% 1.60/0.56    inference(avatar_split_clause,[],[f187,f108,f189])).
% 1.60/0.56  fof(f187,plain,(
% 1.60/0.56    v1_relat_1(sK3) | ~spl7_5),
% 1.60/0.56    inference(unit_resulting_resolution,[],[f81,f110,f80])).
% 1.60/0.56  fof(f80,plain,(
% 1.60/0.56    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.60/0.56    inference(cnf_transformation,[],[f36])).
% 1.60/0.56  fof(f36,plain,(
% 1.60/0.56    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.60/0.56    inference(ennf_transformation,[],[f3])).
% 1.60/0.56  fof(f3,axiom,(
% 1.60/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.60/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.60/0.56  fof(f81,plain,(
% 1.60/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.60/0.56    inference(cnf_transformation,[],[f4])).
% 1.60/0.56  fof(f4,axiom,(
% 1.60/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.60/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.60/0.56  fof(f179,plain,(
% 1.60/0.56    spl7_18 | ~spl7_8 | ~spl7_10),
% 1.60/0.56    inference(avatar_split_clause,[],[f174,f133,f123,f176])).
% 1.60/0.56  fof(f174,plain,(
% 1.60/0.56    l1_pre_topc(sK2) | (~spl7_8 | ~spl7_10)),
% 1.60/0.56    inference(unit_resulting_resolution,[],[f135,f125,f83])).
% 1.60/0.56  fof(f83,plain,(
% 1.60/0.56    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.60/0.56    inference(cnf_transformation,[],[f39])).
% 1.60/0.56  fof(f39,plain,(
% 1.60/0.56    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.60/0.56    inference(ennf_transformation,[],[f10])).
% 1.60/0.56  fof(f10,axiom,(
% 1.60/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.60/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.60/0.56  fof(f173,plain,(
% 1.60/0.56    spl7_17 | ~spl7_10),
% 1.60/0.56    inference(avatar_split_clause,[],[f162,f133,f170])).
% 1.60/0.56  fof(f162,plain,(
% 1.60/0.56    l1_struct_0(sK1) | ~spl7_10),
% 1.60/0.56    inference(unit_resulting_resolution,[],[f135,f84])).
% 1.60/0.56  fof(f168,plain,(
% 1.60/0.56    spl7_16 | ~spl7_13),
% 1.60/0.56    inference(avatar_split_clause,[],[f163,f148,f165])).
% 1.60/0.56  fof(f163,plain,(
% 1.60/0.56    l1_struct_0(sK0) | ~spl7_13),
% 1.60/0.56    inference(unit_resulting_resolution,[],[f150,f84])).
% 1.60/0.56  fof(f161,plain,(
% 1.60/0.56    ~spl7_15),
% 1.60/0.56    inference(avatar_split_clause,[],[f51,f158])).
% 1.60/0.56  fof(f51,plain,(
% 1.60/0.56    ~v2_struct_0(sK0)),
% 1.60/0.56    inference(cnf_transformation,[],[f46])).
% 1.60/0.56  fof(f156,plain,(
% 1.60/0.56    spl7_14),
% 1.60/0.56    inference(avatar_split_clause,[],[f52,f153])).
% 1.60/0.56  fof(f52,plain,(
% 1.60/0.56    v2_pre_topc(sK0)),
% 1.60/0.56    inference(cnf_transformation,[],[f46])).
% 1.60/0.56  fof(f151,plain,(
% 1.60/0.56    spl7_13),
% 1.60/0.56    inference(avatar_split_clause,[],[f53,f148])).
% 1.60/0.56  fof(f53,plain,(
% 1.60/0.56    l1_pre_topc(sK0)),
% 1.60/0.56    inference(cnf_transformation,[],[f46])).
% 1.60/0.56  fof(f146,plain,(
% 1.60/0.56    ~spl7_12),
% 1.60/0.56    inference(avatar_split_clause,[],[f54,f143])).
% 1.60/0.56  fof(f54,plain,(
% 1.60/0.56    ~v2_struct_0(sK1)),
% 1.60/0.56    inference(cnf_transformation,[],[f46])).
% 1.60/0.56  fof(f141,plain,(
% 1.60/0.56    spl7_11),
% 1.60/0.56    inference(avatar_split_clause,[],[f55,f138])).
% 1.60/0.56  fof(f55,plain,(
% 1.60/0.56    v2_pre_topc(sK1)),
% 1.60/0.56    inference(cnf_transformation,[],[f46])).
% 1.60/0.56  fof(f136,plain,(
% 1.60/0.56    spl7_10),
% 1.60/0.56    inference(avatar_split_clause,[],[f56,f133])).
% 1.60/0.56  fof(f56,plain,(
% 1.60/0.56    l1_pre_topc(sK1)),
% 1.60/0.56    inference(cnf_transformation,[],[f46])).
% 1.60/0.56  fof(f131,plain,(
% 1.60/0.56    ~spl7_9),
% 1.60/0.56    inference(avatar_split_clause,[],[f57,f128])).
% 1.60/0.56  fof(f57,plain,(
% 1.60/0.56    ~v2_struct_0(sK2)),
% 1.60/0.56    inference(cnf_transformation,[],[f46])).
% 1.60/0.56  fof(f126,plain,(
% 1.60/0.56    spl7_8),
% 1.60/0.56    inference(avatar_split_clause,[],[f58,f123])).
% 1.60/0.56  fof(f58,plain,(
% 1.60/0.56    m1_pre_topc(sK2,sK1)),
% 1.60/0.56    inference(cnf_transformation,[],[f46])).
% 1.60/0.56  fof(f121,plain,(
% 1.60/0.56    spl7_7),
% 1.60/0.56    inference(avatar_split_clause,[],[f59,f118])).
% 1.60/0.56  fof(f59,plain,(
% 1.60/0.56    v1_funct_1(sK3)),
% 1.60/0.56    inference(cnf_transformation,[],[f46])).
% 1.60/0.56  fof(f116,plain,(
% 1.60/0.56    spl7_6),
% 1.60/0.56    inference(avatar_split_clause,[],[f60,f113])).
% 1.60/0.56  fof(f60,plain,(
% 1.60/0.56    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.60/0.56    inference(cnf_transformation,[],[f46])).
% 1.60/0.56  fof(f111,plain,(
% 1.60/0.56    spl7_5),
% 1.60/0.56    inference(avatar_split_clause,[],[f61,f108])).
% 1.60/0.56  fof(f61,plain,(
% 1.60/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.60/0.56    inference(cnf_transformation,[],[f46])).
% 1.60/0.56  fof(f106,plain,(
% 1.60/0.56    spl7_4),
% 1.60/0.56    inference(avatar_split_clause,[],[f62,f103])).
% 1.60/0.56  fof(f62,plain,(
% 1.60/0.56    v1_funct_1(sK4)),
% 1.60/0.56    inference(cnf_transformation,[],[f46])).
% 1.60/0.56  fof(f101,plain,(
% 1.60/0.56    spl7_3),
% 1.60/0.56    inference(avatar_split_clause,[],[f63,f98])).
% 1.60/0.56  fof(f63,plain,(
% 1.60/0.56    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))),
% 1.60/0.56    inference(cnf_transformation,[],[f46])).
% 1.60/0.56  fof(f96,plain,(
% 1.60/0.56    spl7_2),
% 1.60/0.56    inference(avatar_split_clause,[],[f64,f93])).
% 1.60/0.56  fof(f64,plain,(
% 1.60/0.56    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))),
% 1.60/0.56    inference(cnf_transformation,[],[f46])).
% 1.60/0.56  fof(f91,plain,(
% 1.60/0.56    ~spl7_1),
% 1.60/0.56    inference(avatar_split_clause,[],[f66,f88])).
% 1.60/0.56  fof(f66,plain,(
% 1.60/0.56    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)),
% 1.60/0.56    inference(cnf_transformation,[],[f46])).
% 1.60/0.56  % SZS output end Proof for theBenchmark
% 1.60/0.56  % (22607)------------------------------
% 1.60/0.56  % (22607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.56  % (22607)Termination reason: Refutation
% 1.60/0.56  
% 1.60/0.56  % (22607)Memory used [KB]: 11897
% 1.60/0.56  % (22607)Time elapsed: 0.090 s
% 1.60/0.56  % (22607)------------------------------
% 1.60/0.56  % (22607)------------------------------
% 1.60/0.56  % (22600)Success in time 0.208 s
%------------------------------------------------------------------------------
