%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 217 expanded)
%              Number of leaves         :   24 (  69 expanded)
%              Depth                    :   15
%              Number of atoms          :  536 (2057 expanded)
%              Number of equality atoms :   37 ( 156 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f199,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f139,f182,f189,f193,f198])).

fof(f198,plain,
    ( ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f118,f196])).

fof(f196,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f195,f120])).

fof(f120,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f87,f92])).

fof(f92,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f87,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f195,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | r2_hidden(u1_struct_0(sK2),k1_xboole_0)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f194,f110])).

fof(f110,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK2)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl8_2
  <=> v3_pre_topc(u1_struct_0(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f194,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | ~ v3_pre_topc(u1_struct_0(sK2),sK2)
    | r2_hidden(u1_struct_0(sK2),k1_xboole_0)
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f122,f114])).

fof(f114,plain,
    ( v4_pre_topc(u1_struct_0(sK2),sK2)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl8_3
  <=> v4_pre_topc(u1_struct_0(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f122,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | ~ v4_pre_topc(u1_struct_0(sK2),sK2)
    | ~ v3_pre_topc(u1_struct_0(sK2),sK2)
    | r2_hidden(u1_struct_0(sK2),k1_xboole_0) ),
    inference(resolution,[],[f94,f99])).

fof(f99,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f59,f58])).

fof(f58,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f94,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK3,X3)
      | ~ v4_pre_topc(X3,sK2)
      | ~ v3_pre_topc(X3,sK2)
      | r2_hidden(X3,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f56,f57])).

fof(f57,plain,(
    k1_xboole_0 = sK4 ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( k1_xboole_0 = sK4
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK4)
            | ~ r2_hidden(sK3,X3)
            | ~ v4_pre_topc(X3,sK2)
            | ~ v3_pre_topc(X3,sK2) )
          & ( ( r2_hidden(sK3,X3)
              & v4_pre_topc(X3,sK2)
              & v3_pre_topc(X3,sK2) )
            | ~ r2_hidden(X3,sK4) ) )
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f32,f35,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_xboole_0 = X2
                & ! [X3] :
                    ( ( ( r2_hidden(X3,X2)
                        | ~ r2_hidden(X1,X3)
                        | ~ v4_pre_topc(X3,X0)
                        | ~ v3_pre_topc(X3,X0) )
                      & ( ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) )
                        | ~ r2_hidden(X3,X2) ) )
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,sK2)
                      | ~ v3_pre_topc(X3,sK2) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,sK2)
                        & v3_pre_topc(X3,sK2) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k1_xboole_0 = X2
            & ! [X3] :
                ( ( ( r2_hidden(X3,X2)
                    | ~ r2_hidden(X1,X3)
                    | ~ v4_pre_topc(X3,sK2)
                    | ~ v3_pre_topc(X3,sK2) )
                  & ( ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,sK2)
                      & v3_pre_topc(X3,sK2) )
                    | ~ r2_hidden(X3,X2) ) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
        & m1_subset_1(X1,u1_struct_0(sK2)) )
   => ( ? [X2] :
          ( k1_xboole_0 = X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(sK3,X3)
                  | ~ v4_pre_topc(X3,sK2)
                  | ~ v3_pre_topc(X3,sK2) )
                & ( ( r2_hidden(sK3,X3)
                    & v4_pre_topc(X3,sK2)
                    & v3_pre_topc(X3,sK2) )
                  | ~ r2_hidden(X3,X2) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
      & m1_subset_1(sK3,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2] :
        ( k1_xboole_0 = X2
        & ! [X3] :
            ( ( ( r2_hidden(X3,X2)
                | ~ r2_hidden(sK3,X3)
                | ~ v4_pre_topc(X3,sK2)
                | ~ v3_pre_topc(X3,sK2) )
              & ( ( r2_hidden(sK3,X3)
                  & v4_pre_topc(X3,sK2)
                  & v3_pre_topc(X3,sK2) )
                | ~ r2_hidden(X3,X2) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
   => ( k1_xboole_0 = sK4
      & ! [X3] :
          ( ( ( r2_hidden(X3,sK4)
              | ~ r2_hidden(sK3,X3)
              | ~ v4_pre_topc(X3,sK2)
              | ~ v3_pre_topc(X3,sK2) )
            & ( ( r2_hidden(sK3,X3)
                & v4_pre_topc(X3,sK2)
                & v3_pre_topc(X3,sK2) )
              | ~ r2_hidden(X3,sK4) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
      & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
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
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ~ ( k1_xboole_0 = X2
                    & ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X3,X2)
                        <=> ( r2_hidden(X1,X3)
                            & v4_pre_topc(X3,X0)
                            & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ~ ( k1_xboole_0 = X2
                  & ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( r2_hidden(X3,X2)
                      <=> ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).

fof(f56,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK4)
      | ~ r2_hidden(sK3,X3)
      | ~ v4_pre_topc(X3,sK2)
      | ~ v3_pre_topc(X3,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f118,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl8_4
  <=> r2_hidden(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f193,plain,(
    ~ spl8_5 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f191,f48])).

fof(f48,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f191,plain,
    ( v2_struct_0(sK2)
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f190,f100])).

fof(f100,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f61,f50])).

fof(f50,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f190,plain,
    ( ~ l1_struct_0(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_5 ),
    inference(resolution,[],[f138,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f138,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl8_5
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f189,plain,(
    spl8_3 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | spl8_3 ),
    inference(subsumption_resolution,[],[f187,f49])).

fof(f49,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f187,plain,
    ( ~ v2_pre_topc(sK2)
    | spl8_3 ),
    inference(subsumption_resolution,[],[f186,f50])).

fof(f186,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl8_3 ),
    inference(resolution,[],[f125,f132])).

fof(f132,plain,(
    ! [X0] :
      ( v4_pre_topc(u1_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f131,f61])).

fof(f131,plain,(
    ! [X0] :
      ( v4_pre_topc(u1_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(superposition,[],[f86,f60])).

fof(f60,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f86,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

fof(f125,plain,
    ( ~ v4_pre_topc(u1_struct_0(sK2),sK2)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f113])).

fof(f182,plain,(
    spl8_2 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | spl8_2 ),
    inference(subsumption_resolution,[],[f180,f129])).

fof(f129,plain,(
    sP0(sK2) ),
    inference(subsumption_resolution,[],[f128,f49])).

fof(f128,plain,
    ( ~ v2_pre_topc(sK2)
    | sP0(sK2) ),
    inference(resolution,[],[f62,f101])).

fof(f101,plain,(
    sP1(sK2) ),
    inference(resolution,[],[f82,f50])).

fof(f82,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | sP1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f20,f29,f28])).

fof(f28,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ( ! [X1] :
            ( ! [X2] :
                ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                | ~ r2_hidden(X2,u1_pre_topc(X0))
                | ~ r2_hidden(X1,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & ! [X3] :
            ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            | ~ r1_tarski(X3,u1_pre_topc(X0))
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f29,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f20,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

% (10891)Refutation not found, incomplete strategy% (10891)------------------------------
% (10891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f14,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f6])).

% (10891)Termination reason: Refutation not found, incomplete strategy

% (10891)Memory used [KB]: 6140
% (10891)Time elapsed: 0.052 s
% (10891)------------------------------
% (10891)------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

fof(f62,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ v2_pre_topc(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v2_pre_topc(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f180,plain,
    ( ~ sP0(sK2)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f179,f50])).

fof(f179,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ sP0(sK2)
    | spl8_2 ),
    inference(resolution,[],[f175,f124])).

fof(f124,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK2),sK2)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f109])).

fof(f175,plain,(
    ! [X1] :
      ( v3_pre_topc(u1_struct_0(X1),X1)
      | ~ l1_pre_topc(X1)
      | ~ sP0(X1) ) ),
    inference(resolution,[],[f150,f64])).

fof(f64,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK5(X0),sK6(X0)),u1_pre_topc(X0))
          & r2_hidden(sK6(X0),u1_pre_topc(X0))
          & r2_hidden(sK5(X0),u1_pre_topc(X0))
          & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0)))
          & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) )
        | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK7(X0)),u1_pre_topc(X0))
          & r1_tarski(sK7(X0),u1_pre_topc(X0))
          & m1_subset_1(sK7(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( ! [X4] :
              ( ! [X5] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0))
                  | ~ r2_hidden(X5,u1_pre_topc(X0))
                  | ~ r2_hidden(X4,u1_pre_topc(X0))
                  | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X6] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0))
              | ~ r1_tarski(X6,u1_pre_topc(X0))
              | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f40,f43,f42,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              & r2_hidden(X2,u1_pre_topc(X0))
              & r2_hidden(X1,u1_pre_topc(X0))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK5(X0),X2),u1_pre_topc(X0))
            & r2_hidden(X2,u1_pre_topc(X0))
            & r2_hidden(sK5(X0),u1_pre_topc(X0))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK5(X0),X2),u1_pre_topc(X0))
          & r2_hidden(X2,u1_pre_topc(X0))
          & r2_hidden(sK5(X0),u1_pre_topc(X0))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK5(X0),sK6(X0)),u1_pre_topc(X0))
        & r2_hidden(sK6(X0),u1_pre_topc(X0))
        & r2_hidden(sK5(X0),u1_pre_topc(X0))
        & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
          & r1_tarski(X3,u1_pre_topc(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK7(X0)),u1_pre_topc(X0))
        & r1_tarski(sK7(X0),u1_pre_topc(X0))
        & m1_subset_1(sK7(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                & r2_hidden(X2,u1_pre_topc(X0))
                & r2_hidden(X1,u1_pre_topc(X0))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        | ? [X3] :
            ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            & r1_tarski(X3,u1_pre_topc(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( ! [X4] :
              ( ! [X5] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0))
                  | ~ r2_hidden(X5,u1_pre_topc(X0))
                  | ~ r2_hidden(X4,u1_pre_topc(X0))
                  | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X6] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0))
              | ~ r1_tarski(X6,u1_pre_topc(X0))
              | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                & r2_hidden(X2,u1_pre_topc(X0))
                & r2_hidden(X1,u1_pre_topc(X0))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        | ? [X3] :
            ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            & r1_tarski(X3,u1_pre_topc(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                & r2_hidden(X2,u1_pre_topc(X0))
                & r2_hidden(X1,u1_pre_topc(X0))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        | ? [X3] :
            ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            & r1_tarski(X3,u1_pre_topc(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f150,plain,(
    ! [X0] :
      ( ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | v3_pre_topc(u1_struct_0(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f84,f99])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f139,plain,
    ( spl8_4
    | spl8_5 ),
    inference(avatar_split_clause,[],[f133,f137,f117])).

fof(f133,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | r2_hidden(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f88,f51])).

fof(f51,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f36])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:26:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (10876)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.47  % (10881)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (10889)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.48  % (10876)Refutation not found, incomplete strategy% (10876)------------------------------
% 0.22/0.48  % (10876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (10889)Refutation not found, incomplete strategy% (10889)------------------------------
% 0.22/0.48  % (10889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (10889)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (10889)Memory used [KB]: 1663
% 0.22/0.48  % (10889)Time elapsed: 0.061 s
% 0.22/0.48  % (10889)------------------------------
% 0.22/0.48  % (10889)------------------------------
% 0.22/0.48  % (10884)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.49  % (10876)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (10876)Memory used [KB]: 6140
% 0.22/0.49  % (10876)Time elapsed: 0.062 s
% 0.22/0.49  % (10876)------------------------------
% 0.22/0.49  % (10876)------------------------------
% 0.22/0.49  % (10877)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (10880)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (10878)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.50  % (10882)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (10891)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (10878)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f199,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f139,f182,f189,f193,f198])).
% 0.22/0.50  fof(f198,plain,(
% 0.22/0.50    ~spl8_2 | ~spl8_3 | ~spl8_4),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f197])).
% 0.22/0.50  fof(f197,plain,(
% 0.22/0.50    $false | (~spl8_2 | ~spl8_3 | ~spl8_4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f118,f196])).
% 0.22/0.50  fof(f196,plain,(
% 0.22/0.50    ~r2_hidden(sK3,u1_struct_0(sK2)) | (~spl8_2 | ~spl8_3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f195,f120])).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.50    inference(superposition,[],[f87,f92])).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.50    inference(equality_resolution,[],[f91])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f47])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.22/0.50    inference(flattening,[],[f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.22/0.50    inference(nnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.22/0.50  fof(f195,plain,(
% 0.22/0.50    ~r2_hidden(sK3,u1_struct_0(sK2)) | r2_hidden(u1_struct_0(sK2),k1_xboole_0) | (~spl8_2 | ~spl8_3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f194,f110])).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    v3_pre_topc(u1_struct_0(sK2),sK2) | ~spl8_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f109])).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    spl8_2 <=> v3_pre_topc(u1_struct_0(sK2),sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.50  fof(f194,plain,(
% 0.22/0.50    ~r2_hidden(sK3,u1_struct_0(sK2)) | ~v3_pre_topc(u1_struct_0(sK2),sK2) | r2_hidden(u1_struct_0(sK2),k1_xboole_0) | ~spl8_3),
% 0.22/0.50    inference(subsumption_resolution,[],[f122,f114])).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    v4_pre_topc(u1_struct_0(sK2),sK2) | ~spl8_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f113])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    spl8_3 <=> v4_pre_topc(u1_struct_0(sK2),sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.22/0.50  fof(f122,plain,(
% 0.22/0.50    ~r2_hidden(sK3,u1_struct_0(sK2)) | ~v4_pre_topc(u1_struct_0(sK2),sK2) | ~v3_pre_topc(u1_struct_0(sK2),sK2) | r2_hidden(u1_struct_0(sK2),k1_xboole_0)),
% 0.22/0.50    inference(resolution,[],[f94,f99])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.22/0.50    inference(forward_demodulation,[],[f59,f58])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) | ~r2_hidden(sK3,X3) | ~v4_pre_topc(X3,sK2) | ~v3_pre_topc(X3,sK2) | r2_hidden(X3,k1_xboole_0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f56,f57])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    k1_xboole_0 = sK4),
% 0.22/0.50    inference(cnf_transformation,[],[f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ((k1_xboole_0 = sK4 & ! [X3] : (((r2_hidden(X3,sK4) | ~r2_hidden(sK3,X3) | ~v4_pre_topc(X3,sK2) | ~v3_pre_topc(X3,sK2)) & ((r2_hidden(sK3,X3) & v4_pre_topc(X3,sK2) & v3_pre_topc(X3,sK2)) | ~r2_hidden(X3,sK4))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f32,f35,f34,f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK2) | ~v3_pre_topc(X3,sK2)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK2) & v3_pre_topc(X3,sK2)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK2) | ~v3_pre_topc(X3,sK2)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK2) & v3_pre_topc(X3,sK2)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & m1_subset_1(X1,u1_struct_0(sK2))) => (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK3,X3) | ~v4_pre_topc(X3,sK2) | ~v3_pre_topc(X3,sK2)) & ((r2_hidden(sK3,X3) & v4_pre_topc(X3,sK2) & v3_pre_topc(X3,sK2)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & m1_subset_1(sK3,u1_struct_0(sK2)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK3,X3) | ~v4_pre_topc(X3,sK2) | ~v3_pre_topc(X3,sK2)) & ((r2_hidden(sK3,X3) & v4_pre_topc(X3,sK2) & v3_pre_topc(X3,sK2)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) => (k1_xboole_0 = sK4 & ! [X3] : (((r2_hidden(X3,sK4) | ~r2_hidden(sK3,X3) | ~v4_pre_topc(X3,sK2) | ~v3_pre_topc(X3,sK2)) & ((r2_hidden(sK3,X3) & v4_pre_topc(X3,sK2) & v3_pre_topc(X3,sK2)) | ~r2_hidden(X3,sK4))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | (~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0))) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,negated_conjecture,(
% 0.22/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.22/0.50    inference(negated_conjecture,[],[f12])).
% 0.22/0.50  fof(f12,conjecture,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    ( ! [X3] : (r2_hidden(X3,sK4) | ~r2_hidden(sK3,X3) | ~v4_pre_topc(X3,sK2) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f36])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    r2_hidden(sK3,u1_struct_0(sK2)) | ~spl8_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f117])).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    spl8_4 <=> r2_hidden(sK3,u1_struct_0(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.22/0.50  fof(f193,plain,(
% 0.22/0.50    ~spl8_5),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f192])).
% 0.22/0.50  fof(f192,plain,(
% 0.22/0.50    $false | ~spl8_5),
% 0.22/0.50    inference(subsumption_resolution,[],[f191,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ~v2_struct_0(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f36])).
% 0.22/0.50  fof(f191,plain,(
% 0.22/0.50    v2_struct_0(sK2) | ~spl8_5),
% 0.22/0.50    inference(subsumption_resolution,[],[f190,f100])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    l1_struct_0(sK2)),
% 0.22/0.50    inference(resolution,[],[f61,f50])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    l1_pre_topc(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f36])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.50  fof(f190,plain,(
% 0.22/0.50    ~l1_struct_0(sK2) | v2_struct_0(sK2) | ~spl8_5),
% 0.22/0.50    inference(resolution,[],[f138,f85])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    v1_xboole_0(u1_struct_0(sK2)) | ~spl8_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f137])).
% 0.22/0.50  fof(f137,plain,(
% 0.22/0.50    spl8_5 <=> v1_xboole_0(u1_struct_0(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.22/0.50  fof(f189,plain,(
% 0.22/0.50    spl8_3),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f188])).
% 0.22/0.50  fof(f188,plain,(
% 0.22/0.50    $false | spl8_3),
% 0.22/0.50    inference(subsumption_resolution,[],[f187,f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    v2_pre_topc(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f36])).
% 0.22/0.50  fof(f187,plain,(
% 0.22/0.50    ~v2_pre_topc(sK2) | spl8_3),
% 0.22/0.50    inference(subsumption_resolution,[],[f186,f50])).
% 0.22/0.50  fof(f186,plain,(
% 0.22/0.50    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | spl8_3),
% 0.22/0.50    inference(resolution,[],[f125,f132])).
% 0.22/0.50  fof(f132,plain,(
% 0.22/0.50    ( ! [X0] : (v4_pre_topc(u1_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f131,f61])).
% 0.22/0.50  fof(f131,plain,(
% 0.22/0.50    ( ! [X0] : (v4_pre_topc(u1_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~l1_struct_0(X0)) )),
% 0.22/0.50    inference(superposition,[],[f86,f60])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    ~v4_pre_topc(u1_struct_0(sK2),sK2) | spl8_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f113])).
% 0.22/0.50  fof(f182,plain,(
% 0.22/0.50    spl8_2),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f181])).
% 0.22/0.50  fof(f181,plain,(
% 0.22/0.50    $false | spl8_2),
% 0.22/0.50    inference(subsumption_resolution,[],[f180,f129])).
% 0.22/0.50  fof(f129,plain,(
% 0.22/0.50    sP0(sK2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f128,f49])).
% 0.22/0.50  fof(f128,plain,(
% 0.22/0.50    ~v2_pre_topc(sK2) | sP0(sK2)),
% 0.22/0.50    inference(resolution,[],[f62,f101])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    sP1(sK2)),
% 0.22/0.50    inference(resolution,[],[f82,f50])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_pre_topc(X0) | sP1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0] : (sP1(X0) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(definition_folding,[],[f20,f29,f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0] : (sP0(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))))),
% 0.22/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0] : ((v2_pre_topc(X0) <=> sP0(X0)) | ~sP1(X0))),
% 0.22/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f14])).
% 0.22/0.50  % (10891)Refutation not found, incomplete strategy% (10891)------------------------------
% 0.22/0.50  % (10891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.22/0.50    inference(rectify,[],[f6])).
% 0.22/0.50  % (10891)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (10891)Memory used [KB]: 6140
% 0.22/0.50  % (10891)Time elapsed: 0.052 s
% 0.22/0.50  % (10891)------------------------------
% 0.22/0.50  % (10891)------------------------------
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    ( ! [X0] : (~sP1(X0) | ~v2_pre_topc(X0) | sP0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0)) & (sP0(X0) | ~v2_pre_topc(X0))) | ~sP1(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f29])).
% 0.22/0.50  fof(f180,plain,(
% 0.22/0.50    ~sP0(sK2) | spl8_2),
% 0.22/0.50    inference(subsumption_resolution,[],[f179,f50])).
% 0.22/0.50  fof(f179,plain,(
% 0.22/0.50    ~l1_pre_topc(sK2) | ~sP0(sK2) | spl8_2),
% 0.22/0.50    inference(resolution,[],[f175,f124])).
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    ~v3_pre_topc(u1_struct_0(sK2),sK2) | spl8_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f109])).
% 0.22/0.50  fof(f175,plain,(
% 0.22/0.50    ( ! [X1] : (v3_pre_topc(u1_struct_0(X1),X1) | ~l1_pre_topc(X1) | ~sP0(X1)) )),
% 0.22/0.50    inference(resolution,[],[f150,f64])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~sP0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ! [X0] : ((sP0(X0) | ((~r2_hidden(k9_subset_1(u1_struct_0(X0),sK5(X0),sK6(X0)),u1_pre_topc(X0)) & r2_hidden(sK6(X0),u1_pre_topc(X0)) & r2_hidden(sK5(X0),u1_pre_topc(X0)) & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK7(X0)),u1_pre_topc(X0)) & r1_tarski(sK7(X0),u1_pre_topc(X0)) & m1_subset_1(sK7(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((! [X4] : (! [X5] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0)) | ~r2_hidden(X5,u1_pre_topc(X0)) | ~r2_hidden(X4,u1_pre_topc(X0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X6] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0)) | ~r1_tarski(X6,u1_pre_topc(X0)) | ~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP0(X0)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f40,f43,f42,f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ! [X0] : (? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK5(X0),X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(sK5(X0),u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ! [X0] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK5(X0),X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(sK5(X0),u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK5(X0),sK6(X0)),u1_pre_topc(X0)) & r2_hidden(sK6(X0),u1_pre_topc(X0)) & r2_hidden(sK5(X0),u1_pre_topc(X0)) & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ! [X0] : (? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK7(X0)),u1_pre_topc(X0)) & r1_tarski(sK7(X0),u1_pre_topc(X0)) & m1_subset_1(sK7(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((! [X4] : (! [X5] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0)) | ~r2_hidden(X5,u1_pre_topc(X0)) | ~r2_hidden(X4,u1_pre_topc(X0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X6] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0)) | ~r1_tarski(X6,u1_pre_topc(X0)) | ~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP0(X0)))),
% 0.22/0.50    inference(rectify,[],[f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP0(X0)))),
% 0.22/0.50    inference(flattening,[],[f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ! [X0] : ((sP0(X0) | (? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP0(X0)))),
% 0.22/0.50    inference(nnf_transformation,[],[f28])).
% 0.22/0.50  fof(f150,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | v3_pre_topc(u1_struct_0(X0),X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(resolution,[],[f84,f99])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,u1_pre_topc(X0)) | v3_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.22/0.50  fof(f139,plain,(
% 0.22/0.50    spl8_4 | spl8_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f133,f137,f117])).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    v1_xboole_0(u1_struct_0(sK2)) | r2_hidden(sK3,u1_struct_0(sK2))),
% 0.22/0.50    inference(resolution,[],[f88,f51])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.22/0.50    inference(cnf_transformation,[],[f36])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.50    inference(flattening,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (10883)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.51  % (10896)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (10895)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.51  % (10879)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (10894)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  % (10888)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (10877)Refutation not found, incomplete strategy% (10877)------------------------------
% 0.22/0.51  % (10877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (10877)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (10877)Memory used [KB]: 10618
% 0.22/0.51  % (10877)Time elapsed: 0.094 s
% 0.22/0.51  % (10877)------------------------------
% 0.22/0.51  % (10877)------------------------------
% 0.22/0.51  % (10888)Refutation not found, incomplete strategy% (10888)------------------------------
% 0.22/0.51  % (10888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (10888)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (10888)Memory used [KB]: 6140
% 0.22/0.51  % (10888)Time elapsed: 0.096 s
% 0.22/0.51  % (10888)------------------------------
% 0.22/0.51  % (10888)------------------------------
% 0.22/0.51  % (10879)Refutation not found, incomplete strategy% (10879)------------------------------
% 0.22/0.51  % (10879)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (10879)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (10879)Memory used [KB]: 10618
% 0.22/0.51  % (10879)Time elapsed: 0.075 s
% 0.22/0.51  % (10879)------------------------------
% 0.22/0.51  % (10879)------------------------------
% 0.22/0.51  % (10890)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.51  % (10885)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.51  % (10886)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % (10892)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.52  % (10880)Refutation not found, incomplete strategy% (10880)------------------------------
% 0.22/0.52  % (10880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (10880)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (10880)Memory used [KB]: 1791
% 0.22/0.52  % (10880)Time elapsed: 0.089 s
% 0.22/0.52  % (10880)------------------------------
% 0.22/0.52  % (10880)------------------------------
% 0.22/0.52  % (10896)Refutation not found, incomplete strategy% (10896)------------------------------
% 0.22/0.52  % (10896)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (10896)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (10896)Memory used [KB]: 10618
% 0.22/0.52  % (10896)Time elapsed: 0.113 s
% 0.22/0.52  % (10896)------------------------------
% 0.22/0.52  % (10896)------------------------------
% 0.22/0.52  % (10886)Refutation not found, incomplete strategy% (10886)------------------------------
% 0.22/0.52  % (10886)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (10886)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (10886)Memory used [KB]: 6268
% 0.22/0.52  % (10886)Time elapsed: 0.111 s
% 0.22/0.52  % (10886)------------------------------
% 0.22/0.52  % (10886)------------------------------
% 0.22/0.52  % (10878)------------------------------
% 0.22/0.52  % (10878)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (10878)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (10878)Memory used [KB]: 10746
% 0.22/0.52  % (10878)Time elapsed: 0.088 s
% 0.22/0.52  % (10878)------------------------------
% 0.22/0.52  % (10878)------------------------------
% 0.22/0.52  % (10893)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.52  % (10875)Success in time 0.156 s
%------------------------------------------------------------------------------
