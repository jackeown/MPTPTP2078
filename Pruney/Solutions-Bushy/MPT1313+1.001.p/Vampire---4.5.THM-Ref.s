%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1313+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:43 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 633 expanded)
%              Number of leaves         :   21 ( 245 expanded)
%              Depth                    :   22
%              Number of atoms          :  592 (5979 expanded)
%              Number of equality atoms :   62 (1043 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f662,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f59,f64,f69,f191,f196,f499,f512,f514,f516,f518,f661])).

fof(f661,plain,
    ( ~ spl7_5
    | ~ spl7_14
    | ~ spl7_44 ),
    inference(avatar_contradiction_clause,[],[f660])).

fof(f660,plain,
    ( $false
    | ~ spl7_5
    | ~ spl7_14
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f659,f171])).

fof(f171,plain,
    ( r2_hidden(sK3,u1_pre_topc(sK0))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl7_14
  <=> r2_hidden(sK3,u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f659,plain,
    ( ~ r2_hidden(sK3,u1_pre_topc(sK0))
    | ~ spl7_5
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f658,f27])).

fof(f27,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ( ! [X3] :
          ( k9_subset_1(u1_struct_0(sK1),X3,k2_struct_0(sK1)) != sK2
          | ~ v3_pre_topc(X3,sK0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ v3_pre_topc(sK2,sK1) )
    & ( ( sK2 = k9_subset_1(u1_struct_0(sK1),sK3,k2_struct_0(sK1))
        & v3_pre_topc(sK3,sK0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | v3_pre_topc(sK2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_pre_topc(sK1,sK0)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f16,f15,f14,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v3_pre_topc(X2,X1) )
                & ( ? [X4] :
                      ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | v3_pre_topc(X2,X1) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                    | ~ v3_pre_topc(X3,sK0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
                | ~ v3_pre_topc(X2,X1) )
              & ( ? [X4] :
                    ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X4,sK0)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
                | v3_pre_topc(X2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X1,sK0) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                  | ~ v3_pre_topc(X3,sK0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              | ~ v3_pre_topc(X2,X1) )
            & ( ? [X4] :
                  ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                  & v3_pre_topc(X4,sK0)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
              | v3_pre_topc(X2,X1) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_pre_topc(X1,sK0) )
   => ( ? [X2] :
          ( ( ! [X3] :
                ( k9_subset_1(u1_struct_0(sK1),X3,k2_struct_0(sK1)) != X2
                | ~ v3_pre_topc(X3,sK0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            | ~ v3_pre_topc(X2,sK1) )
          & ( ? [X4] :
                ( k9_subset_1(u1_struct_0(sK1),X4,k2_struct_0(sK1)) = X2
                & v3_pre_topc(X4,sK0)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
            | v3_pre_topc(X2,sK1) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_pre_topc(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X2] :
        ( ( ! [X3] :
              ( k9_subset_1(u1_struct_0(sK1),X3,k2_struct_0(sK1)) != X2
              | ~ v3_pre_topc(X3,sK0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          | ~ v3_pre_topc(X2,sK1) )
        & ( ? [X4] :
              ( k9_subset_1(u1_struct_0(sK1),X4,k2_struct_0(sK1)) = X2
              & v3_pre_topc(X4,sK0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
          | v3_pre_topc(X2,sK1) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ( ! [X3] :
            ( k9_subset_1(u1_struct_0(sK1),X3,k2_struct_0(sK1)) != sK2
            | ~ v3_pre_topc(X3,sK0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        | ~ v3_pre_topc(sK2,sK1) )
      & ( ? [X4] :
            ( k9_subset_1(u1_struct_0(sK1),X4,k2_struct_0(sK1)) = sK2
            & v3_pre_topc(X4,sK0)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
        | v3_pre_topc(sK2,sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X4] :
        ( k9_subset_1(u1_struct_0(sK1),X4,k2_struct_0(sK1)) = sK2
        & v3_pre_topc(X4,sK0)
        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( sK2 = k9_subset_1(u1_struct_0(sK1),sK3,k2_struct_0(sK1))
      & v3_pre_topc(sK3,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ v3_pre_topc(X2,X1) )
              & ( ? [X4] :
                    ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X4,X0)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                | v3_pre_topc(X2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(rectify,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ v3_pre_topc(X2,X1) )
              & ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | v3_pre_topc(X2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ v3_pre_topc(X2,X1) )
              & ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | v3_pre_topc(X2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_pre_topc(X2,X1)
              <~> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
               => ( v3_pre_topc(X2,X1)
                <=> ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v3_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tops_2)).

fof(f658,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ r2_hidden(sK3,u1_pre_topc(sK0))
    | ~ spl7_5
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f657,f26])).

fof(f26,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f657,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ r2_hidden(sK3,u1_pre_topc(sK0))
    | ~ spl7_5
    | ~ spl7_44 ),
    inference(resolution,[],[f508,f68])).

fof(f68,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl7_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f508,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK1,X1)
        | ~ r2_hidden(sK3,u1_pre_topc(X1)) )
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f507])).

fof(f507,plain,
    ( spl7_44
  <=> ! [X1] :
        ( ~ r2_hidden(sK3,u1_pre_topc(X1))
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK1,X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f518,plain,
    ( ~ spl7_4
    | spl7_14
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f517,f66,f169,f61])).

fof(f61,plain,
    ( spl7_4
  <=> v3_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f517,plain,
    ( r2_hidden(sK3,u1_pre_topc(sK0))
    | ~ v3_pre_topc(sK3,sK0)
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f239,f26])).

fof(f239,plain,
    ( r2_hidden(sK3,u1_pre_topc(sK0))
    | ~ v3_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_5 ),
    inference(resolution,[],[f68,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f516,plain,
    ( ~ spl7_1
    | spl7_13 ),
    inference(avatar_split_clause,[],[f515,f162,f48])).

fof(f48,plain,
    ( spl7_1
  <=> v3_pre_topc(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f162,plain,
    ( spl7_13
  <=> r2_hidden(sK2,u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f515,plain,
    ( r2_hidden(sK2,u1_pre_topc(sK1))
    | ~ v3_pre_topc(sK2,sK1) ),
    inference(subsumption_resolution,[],[f184,f99])).

fof(f99,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f93,f26])).

fof(f93,plain,
    ( l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f27,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f184,plain,
    ( r2_hidden(sK2,u1_pre_topc(sK1))
    | ~ v3_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f28,f43])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f514,plain,
    ( ~ spl7_13
    | spl7_1 ),
    inference(avatar_split_clause,[],[f513,f48,f162])).

fof(f513,plain,
    ( v3_pre_topc(sK2,sK1)
    | ~ r2_hidden(sK2,u1_pre_topc(sK1)) ),
    inference(subsumption_resolution,[],[f185,f99])).

fof(f185,plain,
    ( v3_pre_topc(sK2,sK1)
    | ~ r2_hidden(sK2,u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f28,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f512,plain,
    ( spl7_44
    | spl7_13
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f511,f56,f162,f507])).

fof(f56,plain,
    ( spl7_3
  <=> sK2 = k9_subset_1(u1_struct_0(sK1),sK3,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f511,plain,
    ( ! [X0] :
        ( r2_hidden(sK2,u1_pre_topc(sK1))
        | ~ r2_hidden(sK3,u1_pre_topc(X0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f510,f99])).

fof(f510,plain,
    ( ! [X0] :
        ( r2_hidden(sK2,u1_pre_topc(sK1))
        | ~ r2_hidden(sK3,u1_pre_topc(X0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f242,f28])).

fof(f242,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | r2_hidden(sK2,u1_pre_topc(sK1))
        | ~ r2_hidden(sK3,u1_pre_topc(X0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_3 ),
    inference(superposition,[],[f46,f58])).

fof(f58,plain,
    ( sK2 = k9_subset_1(u1_struct_0(sK1),sK3,k2_struct_0(sK1))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f46,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)),u1_pre_topc(X1))
      | ~ r2_hidden(X6,u1_pre_topc(X0))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,u1_pre_topc(X1))
      | k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)) != X5
      | ~ r2_hidden(X6,u1_pre_topc(X0))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ( ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK4(X0,X1)
                      | ~ r2_hidden(X3,u1_pre_topc(X0))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(sK4(X0,X1),u1_pre_topc(X1)) )
                & ( ( sK4(X0,X1) = k9_subset_1(u1_struct_0(X1),sK5(X0,X1),k2_struct_0(X1))
                    & r2_hidden(sK5(X0,X1),u1_pre_topc(X0))
                    & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
                  | r2_hidden(sK4(X0,X1),u1_pre_topc(X1)) )
                & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X5] :
                    ( ( ( r2_hidden(X5,u1_pre_topc(X1))
                        | ! [X6] :
                            ( k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)) != X5
                            | ~ r2_hidden(X6,u1_pre_topc(X0))
                            | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ( k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X5),k2_struct_0(X1)) = X5
                          & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X0))
                          & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X5,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f20,f23,f22,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                | ~ r2_hidden(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X2,u1_pre_topc(X1)) )
          & ( ? [X4] :
                ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                & r2_hidden(X4,u1_pre_topc(X0))
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X2,u1_pre_topc(X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK4(X0,X1)
              | ~ r2_hidden(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ r2_hidden(sK4(X0,X1),u1_pre_topc(X1)) )
        & ( ? [X4] :
              ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = sK4(X0,X1)
              & r2_hidden(X4,u1_pre_topc(X0))
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | r2_hidden(sK4(X0,X1),u1_pre_topc(X1)) )
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = sK4(X0,X1)
          & r2_hidden(X4,u1_pre_topc(X0))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK4(X0,X1) = k9_subset_1(u1_struct_0(X1),sK5(X0,X1),k2_struct_0(X1))
        & r2_hidden(sK5(X0,X1),u1_pre_topc(X0))
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X1),X7,k2_struct_0(X1)) = X5
          & r2_hidden(X7,u1_pre_topc(X0))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X5),k2_struct_0(X1)) = X5
        & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X0))
        & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ? [X2] :
                  ( ( ! [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                        | ~ r2_hidden(X3,u1_pre_topc(X0))
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | ~ r2_hidden(X2,u1_pre_topc(X1)) )
                  & ( ? [X4] :
                        ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                        & r2_hidden(X4,u1_pre_topc(X0))
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    | r2_hidden(X2,u1_pre_topc(X1)) )
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X5] :
                    ( ( ( r2_hidden(X5,u1_pre_topc(X1))
                        | ! [X6] :
                            ( k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)) != X5
                            | ~ r2_hidden(X6,u1_pre_topc(X0))
                            | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ? [X7] :
                            ( k9_subset_1(u1_struct_0(X1),X7,k2_struct_0(X1)) = X5
                            & r2_hidden(X7,u1_pre_topc(X0))
                            & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X5,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ? [X2] :
                  ( ( ! [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                        | ~ r2_hidden(X3,u1_pre_topc(X0))
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | ~ r2_hidden(X2,u1_pre_topc(X1)) )
                  & ( ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | r2_hidden(X2,u1_pre_topc(X1)) )
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X2] :
                    ( ( ( r2_hidden(X2,u1_pre_topc(X1))
                        | ! [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                            | ~ r2_hidden(X3,u1_pre_topc(X0))
                            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ? [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                            & r2_hidden(X3,u1_pre_topc(X0))
                            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X2,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ? [X2] :
                  ( ( ! [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                        | ~ r2_hidden(X3,u1_pre_topc(X0))
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | ~ r2_hidden(X2,u1_pre_topc(X1)) )
                  & ( ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | r2_hidden(X2,u1_pre_topc(X1)) )
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X2] :
                    ( ( ( r2_hidden(X2,u1_pre_topc(X1))
                        | ! [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                            | ~ r2_hidden(X3,u1_pre_topc(X0))
                            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ? [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                            & r2_hidden(X3,u1_pre_topc(X0))
                            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X2,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).

fof(f499,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(avatar_contradiction_clause,[],[f498])).

fof(f498,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f497,f26])).

fof(f497,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f496,f99])).

fof(f496,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f495,f27])).

fof(f495,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f494,f28])).

fof(f494,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f493,f208])).

fof(f208,plain,
    ( r2_hidden(sK2,u1_pre_topc(sK1))
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f207,f99])).

fof(f207,plain,
    ( r2_hidden(sK2,u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f184,f49])).

fof(f49,plain,
    ( v3_pre_topc(sK2,sK1)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f493,plain,
    ( ~ r2_hidden(sK2,u1_pre_topc(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_2
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(trivial_inequality_removal,[],[f492])).

fof(f492,plain,
    ( sK2 != sK2
    | ~ r2_hidden(sK2,u1_pre_topc(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_2
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(superposition,[],[f481,f36])).

fof(f36,plain,(
    ! [X0,X5,X1] :
      ( k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X5),k2_struct_0(X1)) = X5
      | ~ r2_hidden(X5,u1_pre_topc(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f481,plain,
    ( sK2 != k9_subset_1(u1_struct_0(sK1),sK6(sK0,sK1,sK2),k2_struct_0(sK1))
    | ~ spl7_2
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f479,f455])).

fof(f455,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f453,f27])).

fof(f453,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl7_15 ),
    inference(resolution,[],[f190,f26])).

fof(f190,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | m1_subset_1(sK6(X0,sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(sK1,X0) )
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f189])).

% (24916)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f189,plain,
    ( spl7_15
  <=> ! [X0] :
        ( m1_subset_1(sK6(X0,sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f479,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK2 != k9_subset_1(u1_struct_0(sK1),sK6(sK0,sK1,sK2),k2_struct_0(sK1))
    | ~ spl7_2
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(resolution,[],[f464,f53])).

fof(f53,plain,
    ( ! [X3] :
        ( ~ v3_pre_topc(X3,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK1),X3,k2_struct_0(sK1)) != sK2 )
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl7_2
  <=> ! [X3] :
        ( k9_subset_1(u1_struct_0(sK1),X3,k2_struct_0(sK1)) != sK2
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f464,plain,
    ( v3_pre_topc(sK6(sK0,sK1,sK2),sK0)
    | ~ spl7_15
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f456,f351])).

fof(f351,plain,
    ( r2_hidden(sK6(sK0,sK1,sK2),u1_pre_topc(sK0))
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f349,f27])).

fof(f349,plain,
    ( r2_hidden(sK6(sK0,sK1,sK2),u1_pre_topc(sK0))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl7_16 ),
    inference(resolution,[],[f195,f26])).

fof(f195,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(X1)
        | r2_hidden(sK6(X1,sK1,sK2),u1_pre_topc(X1))
        | ~ m1_pre_topc(sK1,X1) )
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl7_16
  <=> ! [X1] :
        ( r2_hidden(sK6(X1,sK1,sK2),u1_pre_topc(X1))
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f456,plain,
    ( ~ r2_hidden(sK6(sK0,sK1,sK2),u1_pre_topc(sK0))
    | v3_pre_topc(sK6(sK0,sK1,sK2),sK0)
    | ~ spl7_15 ),
    inference(resolution,[],[f455,f89])).

fof(f89,plain,(
    ! [X27] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X27,u1_pre_topc(sK0))
      | v3_pre_topc(X27,sK0) ) ),
    inference(resolution,[],[f26,f44])).

fof(f196,plain,
    ( ~ spl7_13
    | spl7_16 ),
    inference(avatar_split_clause,[],[f192,f194,f162])).

fof(f192,plain,(
    ! [X1] :
      ( r2_hidden(sK6(X1,sK1,sK2),u1_pre_topc(X1))
      | ~ r2_hidden(sK2,u1_pre_topc(sK1))
      | ~ m1_pre_topc(sK1,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f181,f99])).

fof(f181,plain,(
    ! [X1] :
      ( r2_hidden(sK6(X1,sK1,sK2),u1_pre_topc(X1))
      | ~ r2_hidden(sK2,u1_pre_topc(sK1))
      | ~ m1_pre_topc(sK1,X1)
      | ~ l1_pre_topc(sK1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f28,f35])).

fof(f35,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X0))
      | ~ r2_hidden(X5,u1_pre_topc(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f191,plain,
    ( ~ spl7_13
    | spl7_15 ),
    inference(avatar_split_clause,[],[f187,f189,f162])).

fof(f187,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(X0,sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(sK2,u1_pre_topc(sK1))
      | ~ m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f180,f99])).

fof(f180,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(X0,sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(sK2,u1_pre_topc(sK1))
      | ~ m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(sK1)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f28,f34])).

fof(f34,plain,(
    ! [X0,X5,X1] :
      ( m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X5,u1_pre_topc(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f69,plain,
    ( spl7_1
    | spl7_5 ),
    inference(avatar_split_clause,[],[f29,f66,f48])).

fof(f29,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f64,plain,
    ( spl7_1
    | spl7_4 ),
    inference(avatar_split_clause,[],[f30,f61,f48])).

fof(f30,plain,
    ( v3_pre_topc(sK3,sK0)
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,
    ( spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f31,f56,f48])).

fof(f31,plain,
    ( sK2 = k9_subset_1(u1_struct_0(sK1),sK3,k2_struct_0(sK1))
    | v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f54,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f32,f52,f48])).

fof(f32,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK1),X3,k2_struct_0(sK1)) != sK2
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(sK2,sK1) ) ),
    inference(cnf_transformation,[],[f17])).

%------------------------------------------------------------------------------
