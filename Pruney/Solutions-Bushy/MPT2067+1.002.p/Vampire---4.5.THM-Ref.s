%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2067+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:07 EST 2020

% Result     : Theorem 1.75s
% Output     : Refutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :  209 (2941 expanded)
%              Number of leaves         :   42 (1086 expanded)
%              Depth                    :   17
%              Number of atoms          : 1222 (50211 expanded)
%              Number of equality atoms :    5 (  10 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f584,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f119,f124,f129,f134,f139,f144,f149,f154,f236,f238,f240,f290,f328,f333,f439,f441,f443,f445,f447,f449,f451,f454,f551,f583])).

fof(f583,plain,
    ( spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | spl5_9
    | spl5_12
    | ~ spl5_21
    | ~ spl5_22
    | ~ spl5_41 ),
    inference(avatar_contradiction_clause,[],[f582])).

fof(f582,plain,
    ( $false
    | spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | spl5_9
    | spl5_12
    | ~ spl5_21
    | ~ spl5_22
    | ~ spl5_41 ),
    inference(subsumption_resolution,[],[f123,f581])).

fof(f581,plain,
    ( ~ r1_waybel_7(sK0,sK3,sK2)
    | spl5_1
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | spl5_9
    | spl5_12
    | ~ spl5_21
    | ~ spl5_22
    | ~ spl5_41 ),
    inference(forward_demodulation,[],[f580,f458])).

fof(f458,plain,
    ( sK3 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3))
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | spl5_9 ),
    inference(unit_resulting_resolution,[],[f65,f155,f153,f138,f143,f148,f133,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).

fof(f133,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl5_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f148,plain,
    ( v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl5_8
  <=> v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f143,plain,
    ( v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl5_7
  <=> v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f138,plain,
    ( v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl5_6
  <=> v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f153,plain,
    ( ~ v1_xboole_0(sK3)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl5_9
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f155,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f67,f78])).

fof(f78,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f67,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,
    ( ( ! [X3] :
          ( ~ r1_waybel_7(sK0,X3,sK2)
          | ~ r2_hidden(sK1,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
          | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
          | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
          | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
          | v1_xboole_0(X3) )
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) )
    & ( ( r1_waybel_7(sK0,sK3,sK2)
        & r2_hidden(sK1,sK3)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        & v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK0)))
        & v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK0)))
        & v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        & ~ v1_xboole_0(sK3) )
      | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f52,f56,f55,f54,f53])).

fof(f53,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ! [X3] :
                      ( ~ r1_waybel_7(X0,X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                      | v1_xboole_0(X3) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
                & ( ? [X4] :
                      ( r1_waybel_7(X0,X4,X2)
                      & r2_hidden(X1,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                      & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                      & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                      & ~ v1_xboole_0(X4) )
                  | r2_hidden(X2,k2_pre_topc(X0,X1)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r1_waybel_7(sK0,X3,X2)
                    | ~ r2_hidden(X1,X3)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
                    | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
                    | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
                    | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
                    | v1_xboole_0(X3) )
                | ~ r2_hidden(X2,k2_pre_topc(sK0,X1)) )
              & ( ? [X4] :
                    ( r1_waybel_7(sK0,X4,X2)
                    & r2_hidden(X1,X4)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
                    & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
                    & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
                    & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
                    & ~ v1_xboole_0(X4) )
                | r2_hidden(X2,k2_pre_topc(sK0,X1)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ! [X3] :
                  ( ~ r1_waybel_7(sK0,X3,X2)
                  | ~ r2_hidden(X1,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
                  | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
                  | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
                  | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
                  | v1_xboole_0(X3) )
              | ~ r2_hidden(X2,k2_pre_topc(sK0,X1)) )
            & ( ? [X4] :
                  ( r1_waybel_7(sK0,X4,X2)
                  & r2_hidden(X1,X4)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
                  & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
                  & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
                  & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
                  & ~ v1_xboole_0(X4) )
              | r2_hidden(X2,k2_pre_topc(sK0,X1)) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r1_waybel_7(sK0,X3,X2)
                | ~ r2_hidden(sK1,X3)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
                | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
                | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
                | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
                | v1_xboole_0(X3) )
            | ~ r2_hidden(X2,k2_pre_topc(sK0,sK1)) )
          & ( ? [X4] :
                ( r1_waybel_7(sK0,X4,X2)
                & r2_hidden(sK1,X4)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
                & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
                & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
                & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
                & ~ v1_xboole_0(X4) )
            | r2_hidden(X2,k2_pre_topc(sK0,sK1)) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ? [X2] :
        ( ( ! [X3] :
              ( ~ r1_waybel_7(sK0,X3,X2)
              | ~ r2_hidden(sK1,X3)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
              | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
              | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
              | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
              | v1_xboole_0(X3) )
          | ~ r2_hidden(X2,k2_pre_topc(sK0,sK1)) )
        & ( ? [X4] :
              ( r1_waybel_7(sK0,X4,X2)
              & r2_hidden(sK1,X4)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
              & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
              & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
              & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
              & ~ v1_xboole_0(X4) )
          | r2_hidden(X2,k2_pre_topc(sK0,sK1)) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ! [X3] :
            ( ~ r1_waybel_7(sK0,X3,sK2)
            | ~ r2_hidden(sK1,X3)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
            | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
            | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
            | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
            | v1_xboole_0(X3) )
        | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) )
      & ( ? [X4] :
            ( r1_waybel_7(sK0,X4,sK2)
            & r2_hidden(sK1,X4)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
            & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
            & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
            & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
            & ~ v1_xboole_0(X4) )
        | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X4] :
        ( r1_waybel_7(sK0,X4,sK2)
        & r2_hidden(sK1,X4)
        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
        & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK0)))
        & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        & ~ v1_xboole_0(X4) )
   => ( r1_waybel_7(sK0,sK3,sK2)
      & r2_hidden(sK1,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      & v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK0)))
      & v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK0)))
      & v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r1_waybel_7(X0,X3,X2)
                    | ~ r2_hidden(X1,X3)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    | v1_xboole_0(X3) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ? [X4] :
                    ( r1_waybel_7(X0,X4,X2)
                    & r2_hidden(X1,X4)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X4) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r1_waybel_7(X0,X3,X2)
                    | ~ r2_hidden(X1,X3)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    | v1_xboole_0(X3) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ? [X3] :
                    ( r1_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X3) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r1_waybel_7(X0,X3,X2)
                    | ~ r2_hidden(X1,X3)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    | v1_xboole_0(X3) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ? [X3] :
                    ( r1_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X3) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <~> ? [X3] :
                    ( r1_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X3) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <~> ? [X3] :
                    ( r1_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X3) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k2_pre_topc(X0,X1))
                <=> ? [X3] :
                      ( r1_waybel_7(X0,X3,X2)
                      & r2_hidden(X1,X3)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                      & ~ v1_xboole_0(X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r1_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow19)).

fof(f65,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f580,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3)),sK2)
    | spl5_1
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | spl5_9
    | spl5_12
    | ~ spl5_21
    | ~ spl5_22
    | ~ spl5_41 ),
    inference(unit_resulting_resolution,[],[f65,f66,f67,f69,f229,f332,f464,f322,f574,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | r3_waybel_9(X0,X1,X2)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_waybel_9(X0,X1,X2)
                  | ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
                & ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
                  | ~ r3_waybel_9(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
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
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_yellow19)).

fof(f574,plain,
    ( ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3),sK2)
    | spl5_1
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | spl5_9
    | spl5_12
    | ~ spl5_21
    | ~ spl5_22
    | ~ spl5_41 ),
    inference(unit_resulting_resolution,[],[f65,f66,f67,f69,f115,f68,f229,f332,f464,f322,f570,f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v7_waybel_0(X3)
      | ~ r3_waybel_9(X0,X3,X2)
      | ~ r1_waybel_0(X0,X3,X1)
      | ~ l1_waybel_0(X3,X0)
      | r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r3_waybel_9(X0,X3,X2)
                      | ~ r1_waybel_0(X0,X3,X1)
                      | ~ l1_waybel_0(X3,X0)
                      | ~ v7_waybel_0(X3)
                      | ~ v4_orders_2(X3)
                      | v2_struct_0(X3) ) )
                & ( ( r3_waybel_9(X0,sK4(X0,X1,X2),X2)
                    & r1_waybel_0(X0,sK4(X0,X1,X2),X1)
                    & l1_waybel_0(sK4(X0,X1,X2),X0)
                    & v7_waybel_0(sK4(X0,X1,X2))
                    & v4_orders_2(sK4(X0,X1,X2))
                    & ~ v2_struct_0(sK4(X0,X1,X2)) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f59,f60])).

fof(f60,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_waybel_9(X0,X4,X2)
          & r1_waybel_0(X0,X4,X1)
          & l1_waybel_0(X4,X0)
          & v7_waybel_0(X4)
          & v4_orders_2(X4)
          & ~ v2_struct_0(X4) )
     => ( r3_waybel_9(X0,sK4(X0,X1,X2),X2)
        & r1_waybel_0(X0,sK4(X0,X1,X2),X1)
        & l1_waybel_0(sK4(X0,X1,X2),X0)
        & v7_waybel_0(sK4(X0,X1,X2))
        & v4_orders_2(sK4(X0,X1,X2))
        & ~ v2_struct_0(sK4(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r3_waybel_9(X0,X3,X2)
                      | ~ r1_waybel_0(X0,X3,X1)
                      | ~ l1_waybel_0(X3,X0)
                      | ~ v7_waybel_0(X3)
                      | ~ v4_orders_2(X3)
                      | v2_struct_0(X3) ) )
                & ( ? [X4] :
                      ( r3_waybel_9(X0,X4,X2)
                      & r1_waybel_0(X0,X4,X1)
                      & l1_waybel_0(X4,X0)
                      & v7_waybel_0(X4)
                      & v4_orders_2(X4)
                      & ~ v2_struct_0(X4) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r3_waybel_9(X0,X3,X2)
                      | ~ r1_waybel_0(X0,X3,X1)
                      | ~ l1_waybel_0(X3,X0)
                      | ~ v7_waybel_0(X3)
                      | ~ v4_orders_2(X3)
                      | v2_struct_0(X3) ) )
                & ( ? [X3] :
                      ( r3_waybel_9(X0,X3,X2)
                      & r1_waybel_0(X0,X3,X1)
                      & l1_waybel_0(X3,X0)
                      & v7_waybel_0(X3)
                      & v4_orders_2(X3)
                      & ~ v2_struct_0(X3) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r3_waybel_9(X0,X3,X2)
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r3_waybel_9(X0,X3,X2)
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r3_waybel_9(X0,X3,X2)
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow19)).

fof(f570,plain,
    ( r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3),sK1)
    | ~ spl5_4
    | ~ spl5_41 ),
    inference(unit_resulting_resolution,[],[f128,f550])).

fof(f550,plain,
    ( ! [X0] :
        ( r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3),X0)
        | ~ r2_hidden(X0,sK3) )
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f549])).

fof(f549,plain,
    ( spl5_41
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f128,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl5_4
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f68,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f57])).

fof(f115,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl5_1
  <=> r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f322,plain,
    ( l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3),sK0)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f321])).

fof(f321,plain,
    ( spl5_21
  <=> l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f464,plain,
    ( v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3))
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | spl5_9 ),
    inference(unit_resulting_resolution,[],[f65,f153,f155,f157,f158,f143,f138,f148,f133,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | v7_waybel_0(k3_yellow19(X0,X1,X2))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow19)).

fof(f158,plain,(
    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f155,f79])).

fof(f79,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f157,plain,(
    ~ v1_xboole_0(k2_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f65,f155,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f332,plain,
    ( v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK3))
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f330])).

fof(f330,plain,
    ( spl5_22
  <=> v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f229,plain,
    ( ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl5_12
  <=> v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f69,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f57])).

fof(f66,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f123,plain,
    ( r1_waybel_7(sK0,sK3,sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl5_3
  <=> r1_waybel_7(sK0,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f551,plain,
    ( spl5_10
    | ~ spl5_11
    | spl5_12
    | ~ spl5_21
    | spl5_41
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | spl5_9 ),
    inference(avatar_split_clause,[],[f539,f151,f146,f141,f136,f131,f549,f321,f228,f224,f220])).

fof(f220,plain,
    ( spl5_10
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f224,plain,
    ( spl5_11
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f539,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | r1_waybel_0(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK3),X0)
        | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3),sK0)
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3))
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | spl5_9 ),
    inference(superposition,[],[f91,f458])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_yellow19(X0,X1))
      | r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_yellow19(X0,X1))
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ r1_waybel_0(X0,X1,X2) )
              & ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & r1_waybel_0(X0,X1,X2) )
                | ~ r2_hidden(X2,k2_yellow19(X0,X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_yellow19(X0,X1))
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ r1_waybel_0(X0,X1,X2) )
              & ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & r1_waybel_0(X0,X1,X2) )
                | ~ r2_hidden(X2,k2_yellow19(X0,X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_yellow19)).

fof(f454,plain,
    ( ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_9
    | spl5_21 ),
    inference(avatar_contradiction_clause,[],[f453])).

fof(f453,plain,
    ( $false
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_9
    | spl5_21 ),
    inference(subsumption_resolution,[],[f399,f133])).

fof(f399,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ spl5_6
    | ~ spl5_7
    | spl5_9
    | spl5_21 ),
    inference(unit_resulting_resolution,[],[f65,f155,f153,f157,f138,f143,f158,f323,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow19)).

fof(f323,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3),sK0)
    | spl5_21 ),
    inference(avatar_component_clause,[],[f321])).

fof(f451,plain,
    ( ~ spl5_1
    | ~ spl5_35 ),
    inference(avatar_contradiction_clause,[],[f450])).

fof(f450,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_35 ),
    inference(subsumption_resolution,[],[f381,f438])).

fof(f438,plain,
    ( v1_xboole_0(k2_yellow19(sK0,sK4(sK0,sK1,sK2)))
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f436])).

fof(f436,plain,
    ( spl5_35
  <=> v1_xboole_0(k2_yellow19(sK0,sK4(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f381,plain,
    ( ~ v1_xboole_0(k2_yellow19(sK0,sK4(sK0,sK1,sK2)))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f65,f155,f344,f341,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_yellow19(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(k2_yellow19(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(k2_yellow19(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(k2_yellow19(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_yellow19)).

fof(f341,plain,
    ( l1_waybel_0(sK4(sK0,sK1,sK2),sK0)
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f65,f66,f67,f69,f68,f114,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | l1_waybel_0(sK4(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f114,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f113])).

fof(f344,plain,
    ( ~ v2_struct_0(sK4(sK0,sK1,sK2))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f65,f66,f67,f69,f68,f114,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(sK4(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f449,plain,
    ( ~ spl5_1
    | spl5_30 ),
    inference(avatar_contradiction_clause,[],[f448])).

fof(f448,plain,
    ( $false
    | ~ spl5_1
    | spl5_30 ),
    inference(subsumption_resolution,[],[f398,f418])).

fof(f418,plain,
    ( ~ r2_hidden(sK1,k2_yellow19(sK0,sK4(sK0,sK1,sK2)))
    | spl5_30 ),
    inference(avatar_component_clause,[],[f416])).

fof(f416,plain,
    ( spl5_30
  <=> r2_hidden(sK1,k2_yellow19(sK0,sK4(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f398,plain,
    ( r2_hidden(sK1,k2_yellow19(sK0,sK4(sK0,sK1,sK2)))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f65,f155,f344,f68,f341,f340,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_waybel_0(X0,X1,X2)
      | r2_hidden(X2,k2_yellow19(X0,X1))
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f340,plain,
    ( r1_waybel_0(sK0,sK4(sK0,sK1,sK2),sK1)
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f65,f66,f67,f69,f68,f114,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | r1_waybel_0(X0,sK4(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f447,plain,
    ( ~ spl5_1
    | spl5_31 ),
    inference(avatar_contradiction_clause,[],[f446])).

fof(f446,plain,
    ( $false
    | ~ spl5_1
    | spl5_31 ),
    inference(subsumption_resolution,[],[f380,f422])).

fof(f422,plain,
    ( ~ m1_subset_1(k2_yellow19(sK0,sK4(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | spl5_31 ),
    inference(avatar_component_clause,[],[f420])).

fof(f420,plain,
    ( spl5_31
  <=> m1_subset_1(k2_yellow19(sK0,sK4(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f380,plain,
    ( m1_subset_1(k2_yellow19(sK0,sK4(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f65,f155,f344,f341,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow19)).

fof(f445,plain,
    ( ~ spl5_1
    | spl5_32 ),
    inference(avatar_contradiction_clause,[],[f444])).

fof(f444,plain,
    ( $false
    | ~ spl5_1
    | spl5_32 ),
    inference(subsumption_resolution,[],[f382,f426])).

fof(f426,plain,
    ( ~ v13_waybel_0(k2_yellow19(sK0,sK4(sK0,sK1,sK2)),k3_yellow_1(k2_struct_0(sK0)))
    | spl5_32 ),
    inference(avatar_component_clause,[],[f424])).

fof(f424,plain,
    ( spl5_32
  <=> v13_waybel_0(k2_yellow19(sK0,sK4(sK0,sK1,sK2)),k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f382,plain,
    ( v13_waybel_0(k2_yellow19(sK0,sK4(sK0,sK1,sK2)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f65,f155,f344,f341,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f443,plain,
    ( ~ spl5_1
    | spl5_33 ),
    inference(avatar_contradiction_clause,[],[f442])).

fof(f442,plain,
    ( $false
    | ~ spl5_1
    | spl5_33 ),
    inference(subsumption_resolution,[],[f379,f430])).

fof(f430,plain,
    ( ~ v2_waybel_0(k2_yellow19(sK0,sK4(sK0,sK1,sK2)),k3_yellow_1(k2_struct_0(sK0)))
    | spl5_33 ),
    inference(avatar_component_clause,[],[f428])).

fof(f428,plain,
    ( spl5_33
  <=> v2_waybel_0(k2_yellow19(sK0,sK4(sK0,sK1,sK2)),k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f379,plain,
    ( v2_waybel_0(k2_yellow19(sK0,sK4(sK0,sK1,sK2)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f65,f155,f344,f343,f342,f341,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_yellow19)).

fof(f342,plain,
    ( v7_waybel_0(sK4(sK0,sK1,sK2))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f65,f66,f67,f69,f68,f114,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | v7_waybel_0(sK4(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f343,plain,
    ( v4_orders_2(sK4(sK0,sK1,sK2))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f65,f66,f67,f69,f68,f114,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | v4_orders_2(sK4(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f441,plain,
    ( ~ spl5_1
    | spl5_34 ),
    inference(avatar_contradiction_clause,[],[f440])).

fof(f440,plain,
    ( $false
    | ~ spl5_1
    | spl5_34 ),
    inference(subsumption_resolution,[],[f378,f434])).

fof(f434,plain,
    ( ~ v1_subset_1(k2_yellow19(sK0,sK4(sK0,sK1,sK2)),u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | spl5_34 ),
    inference(avatar_component_clause,[],[f432])).

fof(f432,plain,
    ( spl5_34
  <=> v1_subset_1(k2_yellow19(sK0,sK4(sK0,sK1,sK2)),u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f378,plain,
    ( v1_subset_1(k2_yellow19(sK0,sK4(sK0,sK1,sK2)),u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f65,f155,f344,f343,f342,f341,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f439,plain,
    ( ~ spl5_30
    | ~ spl5_31
    | ~ spl5_32
    | ~ spl5_33
    | ~ spl5_34
    | spl5_35
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f414,f117,f113,f436,f432,f428,f424,f420,f416])).

fof(f117,plain,
    ( spl5_2
  <=> ! [X3] :
        ( ~ r1_waybel_7(sK0,X3,sK2)
        | v1_xboole_0(X3)
        | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        | ~ r2_hidden(sK1,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f414,plain,
    ( v1_xboole_0(k2_yellow19(sK0,sK4(sK0,sK1,sK2)))
    | ~ v1_subset_1(k2_yellow19(sK0,sK4(sK0,sK1,sK2)),u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v2_waybel_0(k2_yellow19(sK0,sK4(sK0,sK1,sK2)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(k2_yellow19(sK0,sK4(sK0,sK1,sK2)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(k2_yellow19(sK0,sK4(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ r2_hidden(sK1,k2_yellow19(sK0,sK4(sK0,sK1,sK2)))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f396,f118])).

fof(f118,plain,
    ( ! [X3] :
        ( ~ r1_waybel_7(sK0,X3,sK2)
        | v1_xboole_0(X3)
        | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        | ~ r2_hidden(sK1,X3) )
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f117])).

fof(f396,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,sK4(sK0,sK1,sK2)),sK2)
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f65,f66,f67,f69,f344,f343,f342,f341,f339,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f339,plain,
    ( r3_waybel_9(sK0,sK4(sK0,sK1,sK2),sK2)
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f65,f66,f67,f69,f68,f114,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | r3_waybel_9(X0,sK4(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f333,plain,
    ( spl5_22
    | spl5_15
    | ~ spl5_16
    | spl5_9
    | ~ spl5_7
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f205,f136,f131,f141,f151,f266,f262,f330])).

fof(f262,plain,
    ( spl5_15
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f266,plain,
    ( spl5_16
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f205,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK0)))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK3))
    | ~ spl5_6 ),
    inference(resolution,[],[f202,f138])).

fof(f202,plain,(
    ! [X4,X3] :
      ( ~ v13_waybel_0(X3,k3_yellow_1(X4))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X4))))
      | ~ v2_waybel_0(X3,k3_yellow_1(X4))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X4)
      | v4_orders_2(k3_yellow19(sK0,X4,X3)) ) ),
    inference(global_subsumption,[],[f65,f201])).

fof(f201,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X4))))
      | ~ v13_waybel_0(X3,k3_yellow_1(X4))
      | ~ v2_waybel_0(X3,k3_yellow_1(X4))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X4)
      | v4_orders_2(k3_yellow19(sK0,X4,X3))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f103,f155])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | v4_orders_2(k3_yellow19(X0,X1,X2))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_yellow19)).

fof(f328,plain,(
    ~ spl5_15 ),
    inference(avatar_contradiction_clause,[],[f327])).

fof(f327,plain,
    ( $false
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f157,f264])).

fof(f264,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f262])).

fof(f290,plain,(
    spl5_16 ),
    inference(avatar_contradiction_clause,[],[f289])).

fof(f289,plain,
    ( $false
    | spl5_16 ),
    inference(subsumption_resolution,[],[f158,f268])).

fof(f268,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_16 ),
    inference(avatar_component_clause,[],[f266])).

fof(f240,plain,
    ( ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_9
    | ~ spl5_12 ),
    inference(avatar_contradiction_clause,[],[f239])).

fof(f239,plain,
    ( $false
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_9
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f190,f230])).

fof(f230,plain,
    ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f228])).

fof(f190,plain,
    ( ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK3))
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_9 ),
    inference(unit_resulting_resolution,[],[f65,f155,f153,f157,f158,f143,f138,f133,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f238,plain,(
    ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f237])).

fof(f237,plain,
    ( $false
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f65,f222])).

fof(f222,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f220])).

fof(f236,plain,(
    spl5_11 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | spl5_11 ),
    inference(subsumption_resolution,[],[f155,f226])).

fof(f226,plain,
    ( ~ l1_struct_0(sK0)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f224])).

fof(f154,plain,
    ( spl5_1
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f70,f151,f113])).

fof(f70,plain,
    ( ~ v1_xboole_0(sK3)
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f57])).

fof(f149,plain,
    ( spl5_1
    | spl5_8 ),
    inference(avatar_split_clause,[],[f71,f146,f113])).

fof(f71,plain,
    ( v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f57])).

fof(f144,plain,
    ( spl5_1
    | spl5_7 ),
    inference(avatar_split_clause,[],[f72,f141,f113])).

fof(f72,plain,
    ( v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK0)))
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f57])).

fof(f139,plain,
    ( spl5_1
    | spl5_6 ),
    inference(avatar_split_clause,[],[f73,f136,f113])).

fof(f73,plain,
    ( v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK0)))
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f57])).

fof(f134,plain,
    ( spl5_1
    | spl5_5 ),
    inference(avatar_split_clause,[],[f74,f131,f113])).

fof(f74,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f57])).

fof(f129,plain,
    ( spl5_1
    | spl5_4 ),
    inference(avatar_split_clause,[],[f75,f126,f113])).

fof(f75,plain,
    ( r2_hidden(sK1,sK3)
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f57])).

fof(f124,plain,
    ( spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f76,f121,f113])).

fof(f76,plain,
    ( r1_waybel_7(sK0,sK3,sK2)
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f57])).

fof(f119,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f77,f117,f113])).

fof(f77,plain,(
    ! [X3] :
      ( ~ r1_waybel_7(sK0,X3,sK2)
      | ~ r2_hidden(sK1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      | v1_xboole_0(X3)
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ) ),
    inference(cnf_transformation,[],[f57])).

%------------------------------------------------------------------------------
