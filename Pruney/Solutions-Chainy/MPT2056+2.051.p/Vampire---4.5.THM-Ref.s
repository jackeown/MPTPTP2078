%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:30 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 151 expanded)
%              Number of leaves         :   21 (  68 expanded)
%              Depth                    :    7
%              Number of atoms          :  264 ( 798 expanded)
%              Number of equality atoms :   32 ( 100 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f114,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f50,f55,f60,f65,f70,f75,f80,f88,f96,f103,f106,f113])).

fof(f113,plain,
    ( spl2_8
    | ~ spl2_7
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f112,f90,f72,f77])).

fof(f77,plain,
    ( spl2_8
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f72,plain,
    ( spl2_7
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f90,plain,
    ( spl2_10
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f112,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_10 ),
    inference(resolution,[],[f92,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f92,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f90])).

fof(f106,plain,
    ( spl2_1
    | ~ spl2_2
    | ~ spl2_9
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f105,f100,f85,f47,f42])).

fof(f42,plain,
    ( spl2_1
  <=> sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f47,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f85,plain,
    ( spl2_9
  <=> k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f100,plain,
    ( spl2_12
  <=> sK1 = k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f105,plain,
    ( sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl2_2
    | ~ spl2_9
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f104,f102])).

fof(f102,plain,
    ( sK1 = k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f100])).

fof(f104,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f87,f83])).

fof(f83,plain,
    ( ! [X1] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,X1) = k4_xboole_0(sK1,X1)
    | ~ spl2_2 ),
    inference(resolution,[],[f49,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f49,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f87,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(k1_xboole_0))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f85])).

fof(f103,plain,
    ( spl2_12
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f98,f94,f100])).

fof(f94,plain,
    ( spl2_11
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f98,plain,
    ( sK1 = k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | ~ spl2_11 ),
    inference(resolution,[],[f97,f32])).

fof(f32,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f97,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK1 = k4_xboole_0(sK1,k1_tarski(X0)) )
    | ~ spl2_11 ),
    inference(resolution,[],[f95,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f95,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ v1_xboole_0(X0) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f94])).

fof(f96,plain,
    ( spl2_10
    | spl2_6
    | ~ spl2_5
    | ~ spl2_4
    | ~ spl2_3
    | spl2_11
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f82,f47,f94,f52,f57,f62,f67,f90])).

fof(f67,plain,
    ( spl2_6
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f62,plain,
    ( spl2_5
  <=> v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f57,plain,
    ( spl2_4
  <=> v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f52,plain,
    ( spl2_3
  <=> v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f82,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ v1_xboole_0(X0)
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | v1_xboole_0(sK1)
        | v1_xboole_0(k2_struct_0(sK0)) )
    | ~ spl2_2 ),
    inference(resolution,[],[f49,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ r2_hidden(X2,X1)
      | ~ v1_xboole_0(X2)
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ v1_xboole_0(X2)
              | ~ r2_hidden(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          | ~ v13_waybel_0(X1,k3_yellow_1(X0))
          | ~ v2_waybel_0(X1,k3_yellow_1(X0))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ v1_xboole_0(X2)
              | ~ r2_hidden(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          | ~ v13_waybel_0(X1,k3_yellow_1(X0))
          | ~ v2_waybel_0(X1,k3_yellow_1(X0))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
            & v13_waybel_0(X1,k3_yellow_1(X0))
            & v2_waybel_0(X1,k3_yellow_1(X0))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ~ ( v1_xboole_0(X2)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).

fof(f88,plain,
    ( spl2_8
    | ~ spl2_7
    | spl2_6
    | ~ spl2_4
    | ~ spl2_3
    | spl2_9
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f81,f47,f85,f52,f57,f67,f72,f77])).

fof(f81,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(k1_xboole_0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_2 ),
    inference(resolution,[],[f49,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow19)).

fof(f80,plain,(
    ~ spl2_8 ),
    inference(avatar_split_clause,[],[f24,f77])).

fof(f24,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    & ~ v1_xboole_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        & ~ v1_xboole_0(X1) )
   => ( sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
           => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).

fof(f75,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f25,f72])).

fof(f25,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f70,plain,(
    ~ spl2_6 ),
    inference(avatar_split_clause,[],[f26,f67])).

fof(f26,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f65,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f27,f62])).

fof(f27,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f22])).

fof(f60,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f28,f57])).

fof(f28,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f55,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f29,f52])).

fof(f29,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f50,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f30,f47])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f22])).

fof(f45,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f31,f42])).

fof(f31,plain,(
    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:53:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.40  % (25657)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.13/0.41  % (25657)Refutation found. Thanks to Tanya!
% 0.13/0.41  % SZS status Theorem for theBenchmark
% 0.13/0.41  % SZS output start Proof for theBenchmark
% 0.13/0.41  fof(f114,plain,(
% 0.13/0.41    $false),
% 0.13/0.41    inference(avatar_sat_refutation,[],[f45,f50,f55,f60,f65,f70,f75,f80,f88,f96,f103,f106,f113])).
% 0.13/0.41  fof(f113,plain,(
% 0.13/0.41    spl2_8 | ~spl2_7 | ~spl2_10),
% 0.13/0.41    inference(avatar_split_clause,[],[f112,f90,f72,f77])).
% 0.13/0.41  fof(f77,plain,(
% 0.13/0.41    spl2_8 <=> v2_struct_0(sK0)),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.13/0.41  fof(f72,plain,(
% 0.13/0.41    spl2_7 <=> l1_struct_0(sK0)),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.13/0.41  fof(f90,plain,(
% 0.13/0.41    spl2_10 <=> v1_xboole_0(k2_struct_0(sK0))),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.13/0.41  fof(f112,plain,(
% 0.13/0.41    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl2_10),
% 0.13/0.41    inference(resolution,[],[f92,f35])).
% 0.13/0.41  fof(f35,plain,(
% 0.13/0.41    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f16])).
% 0.13/0.41  fof(f16,plain,(
% 0.13/0.41    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.13/0.41    inference(flattening,[],[f15])).
% 0.13/0.41  fof(f15,plain,(
% 0.13/0.41    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.13/0.41    inference(ennf_transformation,[],[f5])).
% 0.13/0.41  fof(f5,axiom,(
% 0.13/0.41    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.13/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.13/0.41  fof(f92,plain,(
% 0.13/0.41    v1_xboole_0(k2_struct_0(sK0)) | ~spl2_10),
% 0.13/0.41    inference(avatar_component_clause,[],[f90])).
% 0.13/0.41  fof(f106,plain,(
% 0.13/0.41    spl2_1 | ~spl2_2 | ~spl2_9 | ~spl2_12),
% 0.13/0.41    inference(avatar_split_clause,[],[f105,f100,f85,f47,f42])).
% 0.13/0.41  fof(f42,plain,(
% 0.13/0.41    spl2_1 <=> sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.13/0.41  fof(f47,plain,(
% 0.13/0.41    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.13/0.41  fof(f85,plain,(
% 0.13/0.41    spl2_9 <=> k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(k1_xboole_0))),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.13/0.41  fof(f100,plain,(
% 0.13/0.41    spl2_12 <=> sK1 = k4_xboole_0(sK1,k1_tarski(k1_xboole_0))),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.13/0.41  fof(f105,plain,(
% 0.13/0.41    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | (~spl2_2 | ~spl2_9 | ~spl2_12)),
% 0.13/0.41    inference(forward_demodulation,[],[f104,f102])).
% 0.13/0.41  fof(f102,plain,(
% 0.13/0.41    sK1 = k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | ~spl2_12),
% 0.13/0.41    inference(avatar_component_clause,[],[f100])).
% 0.13/0.41  fof(f104,plain,(
% 0.13/0.41    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | (~spl2_2 | ~spl2_9)),
% 0.13/0.41    inference(forward_demodulation,[],[f87,f83])).
% 0.13/0.41  fof(f83,plain,(
% 0.13/0.41    ( ! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,X1) = k4_xboole_0(sK1,X1)) ) | ~spl2_2),
% 0.13/0.41    inference(resolution,[],[f49,f40])).
% 0.13/0.41  fof(f40,plain,(
% 0.13/0.41    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f19])).
% 0.13/0.41  fof(f19,plain,(
% 0.13/0.41    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.13/0.41    inference(ennf_transformation,[],[f4])).
% 0.13/0.41  fof(f4,axiom,(
% 0.13/0.41    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.13/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.13/0.41  fof(f49,plain,(
% 0.13/0.41    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~spl2_2),
% 0.13/0.41    inference(avatar_component_clause,[],[f47])).
% 0.13/0.41  fof(f87,plain,(
% 0.13/0.41    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(k1_xboole_0)) | ~spl2_9),
% 0.13/0.41    inference(avatar_component_clause,[],[f85])).
% 0.13/0.41  fof(f103,plain,(
% 0.13/0.41    spl2_12 | ~spl2_11),
% 0.13/0.41    inference(avatar_split_clause,[],[f98,f94,f100])).
% 0.13/0.41  fof(f94,plain,(
% 0.13/0.41    spl2_11 <=> ! [X0] : (~r2_hidden(X0,sK1) | ~v1_xboole_0(X0))),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.13/0.41  fof(f98,plain,(
% 0.13/0.41    sK1 = k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | ~spl2_11),
% 0.13/0.41    inference(resolution,[],[f97,f32])).
% 0.13/0.41  fof(f32,plain,(
% 0.13/0.41    v1_xboole_0(k1_xboole_0)),
% 0.13/0.41    inference(cnf_transformation,[],[f1])).
% 0.13/0.41  fof(f1,axiom,(
% 0.13/0.41    v1_xboole_0(k1_xboole_0)),
% 0.13/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.13/0.41  fof(f97,plain,(
% 0.13/0.41    ( ! [X0] : (~v1_xboole_0(X0) | sK1 = k4_xboole_0(sK1,k1_tarski(X0))) ) | ~spl2_11),
% 0.13/0.41    inference(resolution,[],[f95,f39])).
% 0.13/0.41  fof(f39,plain,(
% 0.13/0.41    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0) )),
% 0.13/0.41    inference(cnf_transformation,[],[f23])).
% 0.13/0.41  fof(f23,plain,(
% 0.13/0.41    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.13/0.41    inference(nnf_transformation,[],[f3])).
% 0.13/0.41  fof(f3,axiom,(
% 0.13/0.41    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.13/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.13/0.41  fof(f95,plain,(
% 0.13/0.41    ( ! [X0] : (~r2_hidden(X0,sK1) | ~v1_xboole_0(X0)) ) | ~spl2_11),
% 0.13/0.41    inference(avatar_component_clause,[],[f94])).
% 0.13/0.41  fof(f96,plain,(
% 0.13/0.41    spl2_10 | spl2_6 | ~spl2_5 | ~spl2_4 | ~spl2_3 | spl2_11 | ~spl2_2),
% 0.13/0.41    inference(avatar_split_clause,[],[f82,f47,f94,f52,f57,f62,f67,f90])).
% 0.13/0.41  fof(f67,plain,(
% 0.13/0.41    spl2_6 <=> v1_xboole_0(sK1)),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.13/0.41  fof(f62,plain,(
% 0.13/0.41    spl2_5 <=> v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.13/0.41  fof(f57,plain,(
% 0.13/0.41    spl2_4 <=> v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.13/0.41  fof(f52,plain,(
% 0.13/0.41    spl2_3 <=> v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.13/0.41  fof(f82,plain,(
% 0.13/0.41    ( ! [X0] : (~r2_hidden(X0,sK1) | ~v1_xboole_0(X0) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | v1_xboole_0(k2_struct_0(sK0))) ) | ~spl2_2),
% 0.13/0.41    inference(resolution,[],[f49,f34])).
% 0.13/0.41  fof(f34,plain,(
% 0.13/0.41    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~r2_hidden(X2,X1) | ~v1_xboole_0(X2) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f14])).
% 0.13/0.41  fof(f14,plain,(
% 0.13/0.41    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.13/0.41    inference(flattening,[],[f13])).
% 0.13/0.41  fof(f13,plain,(
% 0.13/0.41    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.13/0.41    inference(ennf_transformation,[],[f8])).
% 0.13/0.41  fof(f8,axiom,(
% 0.13/0.41    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 0.13/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).
% 0.13/0.41  fof(f88,plain,(
% 0.13/0.41    spl2_8 | ~spl2_7 | spl2_6 | ~spl2_4 | ~spl2_3 | spl2_9 | ~spl2_2),
% 0.13/0.41    inference(avatar_split_clause,[],[f81,f47,f85,f52,f57,f67,f72,f77])).
% 0.13/0.41  fof(f81,plain,(
% 0.13/0.41    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(k1_xboole_0)) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl2_2),
% 0.13/0.41    inference(resolution,[],[f49,f36])).
% 0.13/0.41  fof(f36,plain,(
% 0.13/0.41    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f18])).
% 0.13/0.41  fof(f18,plain,(
% 0.13/0.41    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.13/0.41    inference(flattening,[],[f17])).
% 0.13/0.41  fof(f17,plain,(
% 0.13/0.41    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.13/0.41    inference(ennf_transformation,[],[f7])).
% 0.13/0.41  fof(f7,axiom,(
% 0.13/0.41    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X1)) => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))),
% 0.13/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow19)).
% 0.13/0.41  fof(f80,plain,(
% 0.13/0.41    ~spl2_8),
% 0.13/0.41    inference(avatar_split_clause,[],[f24,f77])).
% 0.13/0.41  fof(f24,plain,(
% 0.13/0.41    ~v2_struct_0(sK0)),
% 0.13/0.41    inference(cnf_transformation,[],[f22])).
% 0.13/0.41  fof(f22,plain,(
% 0.13/0.41    (sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.13/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f21,f20])).
% 0.13/0.41  fof(f20,plain,(
% 0.13/0.41    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.13/0.41    introduced(choice_axiom,[])).
% 0.13/0.41  fof(f21,plain,(
% 0.13/0.41    ? [X1] : (k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) => (sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1))),
% 0.13/0.41    introduced(choice_axiom,[])).
% 0.13/0.41  fof(f12,plain,(
% 0.13/0.41    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.13/0.41    inference(flattening,[],[f11])).
% 0.13/0.41  fof(f11,plain,(
% 0.13/0.41    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.13/0.41    inference(ennf_transformation,[],[f10])).
% 0.13/0.41  fof(f10,negated_conjecture,(
% 0.13/0.41    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 0.13/0.41    inference(negated_conjecture,[],[f9])).
% 0.13/0.41  fof(f9,conjecture,(
% 0.13/0.41    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 0.13/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).
% 0.13/0.41  fof(f75,plain,(
% 0.13/0.41    spl2_7),
% 0.13/0.41    inference(avatar_split_clause,[],[f25,f72])).
% 0.13/0.41  fof(f25,plain,(
% 0.13/0.41    l1_struct_0(sK0)),
% 0.13/0.41    inference(cnf_transformation,[],[f22])).
% 0.13/0.41  fof(f70,plain,(
% 0.13/0.41    ~spl2_6),
% 0.13/0.41    inference(avatar_split_clause,[],[f26,f67])).
% 0.13/0.41  fof(f26,plain,(
% 0.13/0.41    ~v1_xboole_0(sK1)),
% 0.13/0.41    inference(cnf_transformation,[],[f22])).
% 0.13/0.41  fof(f65,plain,(
% 0.13/0.41    spl2_5),
% 0.13/0.41    inference(avatar_split_clause,[],[f27,f62])).
% 0.13/0.41  fof(f27,plain,(
% 0.13/0.41    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 0.13/0.41    inference(cnf_transformation,[],[f22])).
% 0.13/0.41  fof(f60,plain,(
% 0.13/0.41    spl2_4),
% 0.13/0.41    inference(avatar_split_clause,[],[f28,f57])).
% 0.13/0.41  fof(f28,plain,(
% 0.13/0.41    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.13/0.41    inference(cnf_transformation,[],[f22])).
% 0.13/0.41  fof(f55,plain,(
% 0.13/0.41    spl2_3),
% 0.13/0.41    inference(avatar_split_clause,[],[f29,f52])).
% 0.13/0.41  fof(f29,plain,(
% 0.13/0.41    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.13/0.41    inference(cnf_transformation,[],[f22])).
% 0.13/0.41  fof(f50,plain,(
% 0.13/0.41    spl2_2),
% 0.13/0.41    inference(avatar_split_clause,[],[f30,f47])).
% 0.13/0.41  fof(f30,plain,(
% 0.13/0.41    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.13/0.41    inference(cnf_transformation,[],[f22])).
% 0.13/0.41  fof(f45,plain,(
% 0.13/0.41    ~spl2_1),
% 0.13/0.41    inference(avatar_split_clause,[],[f31,f42])).
% 0.13/0.41  fof(f31,plain,(
% 0.13/0.41    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.13/0.41    inference(cnf_transformation,[],[f22])).
% 0.13/0.41  % SZS output end Proof for theBenchmark
% 0.13/0.41  % (25657)------------------------------
% 0.13/0.41  % (25657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.41  % (25657)Termination reason: Refutation
% 0.13/0.41  
% 0.13/0.41  % (25657)Memory used [KB]: 10618
% 0.13/0.41  % (25657)Time elapsed: 0.006 s
% 0.13/0.41  % (25657)------------------------------
% 0.13/0.41  % (25657)------------------------------
% 0.13/0.41  % (25645)Success in time 0.059 s
%------------------------------------------------------------------------------
