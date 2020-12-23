%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 627 expanded)
%              Number of leaves         :   25 ( 200 expanded)
%              Depth                    :   20
%              Number of atoms          :  502 (6060 expanded)
%              Number of equality atoms :   27 ( 534 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f189,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f145,f150,f158,f174,f178,f188])).

fof(f188,plain,(
    ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f185,f79])).

fof(f79,plain,(
    ! [X0] : r1_tarski(sK2,X0) ),
    inference(definition_unfolding,[],[f56,f55])).

fof(f55,plain,(
    k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( k1_xboole_0 = sK2
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK2)
            | ~ r2_hidden(sK1,X3)
            | ~ v4_pre_topc(X3,sK0)
            | ~ v3_pre_topc(X3,sK0) )
          & ( ( r2_hidden(sK1,X3)
              & v4_pre_topc(X3,sK0)
              & v3_pre_topc(X3,sK0) )
            | ~ r2_hidden(X3,sK2) ) )
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f38,f37,f36])).

% (9655)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
fof(f36,plain,
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
                      | ~ v4_pre_topc(X3,sK0)
                      | ~ v3_pre_topc(X3,sK0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,sK0)
                        & v3_pre_topc(X3,sK0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k1_xboole_0 = X2
            & ! [X3] :
                ( ( ( r2_hidden(X3,X2)
                    | ~ r2_hidden(X1,X3)
                    | ~ v4_pre_topc(X3,sK0)
                    | ~ v3_pre_topc(X3,sK0) )
                  & ( ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,sK0)
                      & v3_pre_topc(X3,sK0) )
                    | ~ r2_hidden(X3,X2) ) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( k1_xboole_0 = X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(sK1,X3)
                  | ~ v4_pre_topc(X3,sK0)
                  | ~ v3_pre_topc(X3,sK0) )
                & ( ( r2_hidden(sK1,X3)
                    & v4_pre_topc(X3,sK0)
                    & v3_pre_topc(X3,sK0) )
                  | ~ r2_hidden(X3,X2) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X2] :
        ( k1_xboole_0 = X2
        & ! [X3] :
            ( ( ( r2_hidden(X3,X2)
                | ~ r2_hidden(sK1,X3)
                | ~ v4_pre_topc(X3,sK0)
                | ~ v3_pre_topc(X3,sK0) )
              & ( ( r2_hidden(sK1,X3)
                  & v4_pre_topc(X3,sK0)
                  & v3_pre_topc(X3,sK0) )
                | ~ r2_hidden(X3,X2) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( k1_xboole_0 = sK2
      & ! [X3] :
          ( ( ( r2_hidden(X3,sK2)
              | ~ r2_hidden(sK1,X3)
              | ~ v4_pre_topc(X3,sK0)
              | ~ v3_pre_topc(X3,sK0) )
            & ( ( r2_hidden(sK1,X3)
                & v4_pre_topc(X3,sK0)
                & v3_pre_topc(X3,sK0) )
              | ~ r2_hidden(X3,sK2) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f185,plain,
    ( ~ r1_tarski(sK2,k2_struct_0(sK0))
    | ~ spl5_7 ),
    inference(resolution,[],[f173,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f173,plain,
    ( r2_hidden(k2_struct_0(sK0),sK2)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl5_7
  <=> r2_hidden(k2_struct_0(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f178,plain,(
    spl5_6 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | spl5_6 ),
    inference(subsumption_resolution,[],[f176,f86])).

fof(f86,plain,(
    m1_subset_1(sK1,k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f49,f85])).

fof(f85,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f62,f84])).

fof(f84,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f63,f48])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f63,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f62,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f49,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f176,plain,
    ( ~ m1_subset_1(sK1,k2_struct_0(sK0))
    | spl5_6 ),
    inference(subsumption_resolution,[],[f175,f93])).

fof(f93,plain,(
    ~ v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f92,f46])).

fof(f46,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f92,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f91,f84])).

fof(f91,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f72,f85])).

fof(f72,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f175,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(sK1,k2_struct_0(sK0))
    | spl5_6 ),
    inference(resolution,[],[f169,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f169,plain,
    ( ~ r2_hidden(sK1,k2_struct_0(sK0))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl5_6
  <=> r2_hidden(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f174,plain,
    ( ~ spl5_6
    | spl5_7
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f164,f131,f171,f167])).

fof(f131,plain,
    ( spl5_4
  <=> v4_pre_topc(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f164,plain,
    ( r2_hidden(k2_struct_0(sK0),sK2)
    | ~ r2_hidden(sK1,k2_struct_0(sK0))
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f163,f123])).

fof(f123,plain,(
    v3_pre_topc(k2_struct_0(sK0),sK0) ),
    inference(subsumption_resolution,[],[f121,f83])).

fof(f83,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f82,f80])).

fof(f80,plain,(
    ! [X0] : k3_subset_1(X0,sK2) = X0 ),
    inference(definition_unfolding,[],[f58,f78])).

fof(f78,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,sK2) ),
    inference(definition_unfolding,[],[f61,f77])).

fof(f77,plain,(
    ! [X0] : k1_subset_1(X0) = sK2 ),
    inference(definition_unfolding,[],[f57,f55])).

fof(f57,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f61,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(f58,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f82,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,sK2),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f60,f78])).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f121,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v3_pre_topc(k2_struct_0(sK0),sK0) ),
    inference(resolution,[],[f120,f116])).

fof(f116,plain,(
    v4_pre_topc(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK0) ),
    inference(subsumption_resolution,[],[f115,f47])).

fof(f47,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f115,plain,
    ( v4_pre_topc(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f114,f48])).

fof(f114,plain,
    ( v4_pre_topc(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f113,f83])).

fof(f113,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v4_pre_topc(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f112,f73])).

fof(f73,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f112,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v4_pre_topc(k3_subset_1(k2_struct_0(sK0),X0),sK0) ) ),
    inference(forward_demodulation,[],[f111,f85])).

fof(f111,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0)
      | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) ) ),
    inference(forward_demodulation,[],[f110,f85])).

fof(f110,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) ) ),
    inference(resolution,[],[f64,f48])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).

fof(f120,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(k3_subset_1(k2_struct_0(sK0),X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v3_pre_topc(X0,sK0) ) ),
    inference(forward_demodulation,[],[f119,f85])).

fof(f119,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(k3_subset_1(k2_struct_0(sK0),X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(X0,sK0) ) ),
    inference(forward_demodulation,[],[f118,f85])).

fof(f118,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f65,f48])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f163,plain,
    ( r2_hidden(k2_struct_0(sK0),sK2)
    | ~ r2_hidden(sK1,k2_struct_0(sK0))
    | ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f162,f83])).

fof(f162,plain,
    ( r2_hidden(k2_struct_0(sK0),sK2)
    | ~ r2_hidden(sK1,k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f132,f90])).

fof(f90,plain,(
    ! [X3] :
      ( ~ v4_pre_topc(X3,sK0)
      | r2_hidden(X3,sK2)
      | ~ r2_hidden(sK1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_pre_topc(X3,sK0) ) ),
    inference(backward_demodulation,[],[f54,f85])).

fof(f54,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK2)
      | ~ r2_hidden(sK1,X3)
      | ~ v4_pre_topc(X3,sK0)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f132,plain,
    ( v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f131])).

fof(f158,plain,(
    ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f155,f79])).

fof(f155,plain,
    ( ~ r1_tarski(sK2,sK3(sK0,sK2))
    | ~ spl5_5 ),
    inference(resolution,[],[f144,f75])).

fof(f144,plain,
    ( r2_hidden(sK3(sK0,sK2),sK2)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl5_5
  <=> r2_hidden(sK3(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f150,plain,
    ( ~ spl5_3
    | spl5_4 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | ~ spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f148,f133])).

fof(f133,plain,
    ( ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f131])).

fof(f148,plain,
    ( v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f147,f80])).

fof(f147,plain,
    ( v4_pre_topc(k3_subset_1(k2_struct_0(sK0),sK2),sK0)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f146,f81])).

fof(f81,plain,(
    ! [X0] : m1_subset_1(sK2,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f59,f55])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f146,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | v4_pre_topc(k3_subset_1(k2_struct_0(sK0),sK2),sK0)
    | ~ spl5_3 ),
    inference(resolution,[],[f129,f112])).

fof(f129,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl5_3
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f145,plain,
    ( spl5_3
    | spl5_5 ),
    inference(avatar_split_clause,[],[f140,f142,f127])).

fof(f140,plain,
    ( r2_hidden(sK3(sK0,sK2),sK2)
    | v3_pre_topc(sK2,sK0) ),
    inference(resolution,[],[f138,f81])).

fof(f138,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | r2_hidden(sK3(sK0,X0),X0)
      | v3_pre_topc(X0,sK0) ) ),
    inference(forward_demodulation,[],[f137,f85])).

fof(f137,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK0,X0),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f136,f46])).

fof(f136,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK0,X0),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(X0,sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f135,f48])).

fof(f135,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK0,X0),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | v3_pre_topc(X0,sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f70,f47])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | r2_hidden(sK3(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ( ! [X3] :
                    ( ~ r1_tarski(X3,X1)
                    | ~ m1_connsp_2(X3,X0,sK3(X0,X1))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(sK3(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ( r1_tarski(sK4(X0,X1,X4),X1)
                    & m1_connsp_2(sK4(X0,X1,X4),X0,X4)
                    & m1_subset_1(sK4(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f42,f44,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X3,X1)
              | ~ m1_connsp_2(X3,X0,X2)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( ~ r1_tarski(X3,X1)
            | ~ m1_connsp_2(X3,X0,sK3(X0,X1))
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(X5,X1)
          & m1_connsp_2(X5,X0,X4)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_tarski(sK4(X0,X1,X4),X1)
        & m1_connsp_2(sK4(X0,X1,X4),X0,X4)
        & m1_subset_1(sK4(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( ~ r1_tarski(X3,X1)
                      | ~ m1_connsp_2(X3,X0,X2)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( r1_tarski(X5,X1)
                      & m1_connsp_2(X5,X0,X4)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( ~ r1_tarski(X3,X1)
                      | ~ m1_connsp_2(X3,X0,X2)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( r1_tarski(X3,X1)
                      & m1_connsp_2(X3,X0,X2)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( r1_tarski(X3,X1)
                            & m1_connsp_2(X3,X0,X2) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_connsp_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:56:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.43  % (9662)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.43  % (9662)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f189,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f145,f150,f158,f174,f178,f188])).
% 0.21/0.43  fof(f188,plain,(
% 0.21/0.43    ~spl5_7),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f187])).
% 0.21/0.43  fof(f187,plain,(
% 0.21/0.43    $false | ~spl5_7),
% 0.21/0.43    inference(subsumption_resolution,[],[f185,f79])).
% 0.21/0.43  fof(f79,plain,(
% 0.21/0.43    ( ! [X0] : (r1_tarski(sK2,X0)) )),
% 0.21/0.43    inference(definition_unfolding,[],[f56,f55])).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    k1_xboole_0 = sK2),
% 0.21/0.43    inference(cnf_transformation,[],[f39])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    ((k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f38,f37,f36])).
% 0.21/0.43  % (9655)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    ? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    ? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.43    inference(flattening,[],[f34])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | (~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0))) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.43    inference(nnf_transformation,[],[f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.43    inference(flattening,[],[f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f17])).
% 0.21/0.43  fof(f17,negated_conjecture,(
% 0.21/0.43    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.21/0.43    inference(negated_conjecture,[],[f16])).
% 0.21/0.43  fof(f16,conjecture,(
% 0.21/0.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).
% 0.21/0.43  fof(f56,plain,(
% 0.21/0.43    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.43  fof(f185,plain,(
% 0.21/0.43    ~r1_tarski(sK2,k2_struct_0(sK0)) | ~spl5_7),
% 0.21/0.43    inference(resolution,[],[f173,f75])).
% 0.21/0.43  fof(f75,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f31])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,axiom,(
% 0.21/0.43    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.43  fof(f173,plain,(
% 0.21/0.43    r2_hidden(k2_struct_0(sK0),sK2) | ~spl5_7),
% 0.21/0.43    inference(avatar_component_clause,[],[f171])).
% 0.21/0.43  fof(f171,plain,(
% 0.21/0.43    spl5_7 <=> r2_hidden(k2_struct_0(sK0),sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.43  fof(f178,plain,(
% 0.21/0.43    spl5_6),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f177])).
% 0.21/0.43  fof(f177,plain,(
% 0.21/0.43    $false | spl5_6),
% 0.21/0.43    inference(subsumption_resolution,[],[f176,f86])).
% 0.21/0.43  fof(f86,plain,(
% 0.21/0.43    m1_subset_1(sK1,k2_struct_0(sK0))),
% 0.21/0.43    inference(backward_demodulation,[],[f49,f85])).
% 0.21/0.43  fof(f85,plain,(
% 0.21/0.43    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.43    inference(resolution,[],[f62,f84])).
% 0.21/0.43  fof(f84,plain,(
% 0.21/0.43    l1_struct_0(sK0)),
% 0.21/0.43    inference(resolution,[],[f63,f48])).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    l1_pre_topc(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f39])).
% 0.21/0.43  fof(f63,plain,(
% 0.21/0.43    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,axiom,(
% 0.21/0.43    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.43  fof(f62,plain,(
% 0.21/0.43    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,axiom,(
% 0.21/0.43    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.43    inference(cnf_transformation,[],[f39])).
% 0.21/0.43  fof(f176,plain,(
% 0.21/0.43    ~m1_subset_1(sK1,k2_struct_0(sK0)) | spl5_6),
% 0.21/0.43    inference(subsumption_resolution,[],[f175,f93])).
% 0.21/0.43  fof(f93,plain,(
% 0.21/0.43    ~v1_xboole_0(k2_struct_0(sK0))),
% 0.21/0.43    inference(subsumption_resolution,[],[f92,f46])).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    ~v2_struct_0(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f39])).
% 0.21/0.43  fof(f92,plain,(
% 0.21/0.43    ~v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f91,f84])).
% 0.21/0.43  fof(f91,plain,(
% 0.21/0.43    ~v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.43    inference(superposition,[],[f72,f85])).
% 0.21/0.43  fof(f72,plain,(
% 0.21/0.43    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f26])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.43    inference(flattening,[],[f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,axiom,(
% 0.21/0.43    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.43  fof(f175,plain,(
% 0.21/0.43    v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(sK1,k2_struct_0(sK0)) | spl5_6),
% 0.21/0.43    inference(resolution,[],[f169,f74])).
% 0.21/0.43  fof(f74,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f30])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.43    inference(flattening,[],[f29])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,axiom,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.43  fof(f169,plain,(
% 0.21/0.43    ~r2_hidden(sK1,k2_struct_0(sK0)) | spl5_6),
% 0.21/0.43    inference(avatar_component_clause,[],[f167])).
% 0.21/0.43  fof(f167,plain,(
% 0.21/0.43    spl5_6 <=> r2_hidden(sK1,k2_struct_0(sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.43  fof(f174,plain,(
% 0.21/0.43    ~spl5_6 | spl5_7 | ~spl5_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f164,f131,f171,f167])).
% 0.21/0.43  fof(f131,plain,(
% 0.21/0.43    spl5_4 <=> v4_pre_topc(k2_struct_0(sK0),sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.43  fof(f164,plain,(
% 0.21/0.43    r2_hidden(k2_struct_0(sK0),sK2) | ~r2_hidden(sK1,k2_struct_0(sK0)) | ~spl5_4),
% 0.21/0.43    inference(subsumption_resolution,[],[f163,f123])).
% 0.21/0.43  fof(f123,plain,(
% 0.21/0.43    v3_pre_topc(k2_struct_0(sK0),sK0)),
% 0.21/0.43    inference(subsumption_resolution,[],[f121,f83])).
% 0.21/0.43  fof(f83,plain,(
% 0.21/0.43    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.43    inference(forward_demodulation,[],[f82,f80])).
% 0.21/0.44  fof(f80,plain,(
% 0.21/0.44    ( ! [X0] : (k3_subset_1(X0,sK2) = X0) )),
% 0.21/0.44    inference(definition_unfolding,[],[f58,f78])).
% 0.21/0.44  fof(f78,plain,(
% 0.21/0.44    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,sK2)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f61,f77])).
% 0.21/0.44  fof(f77,plain,(
% 0.21/0.44    ( ! [X0] : (k1_subset_1(X0) = sK2) )),
% 0.21/0.44    inference(definition_unfolding,[],[f57,f55])).
% 0.21/0.44  fof(f57,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 0.21/0.44  fof(f61,plain,(
% 0.21/0.44    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).
% 0.21/0.44  fof(f58,plain,(
% 0.21/0.44    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.44  fof(f82,plain,(
% 0.21/0.44    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,sK2),k1_zfmisc_1(X0))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f60,f78])).
% 0.21/0.44  fof(f60,plain,(
% 0.21/0.44    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.44  fof(f121,plain,(
% 0.21/0.44    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(k2_struct_0(sK0),sK0)),
% 0.21/0.44    inference(resolution,[],[f120,f116])).
% 0.21/0.44  fof(f116,plain,(
% 0.21/0.44    v4_pre_topc(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK0)),
% 0.21/0.44    inference(subsumption_resolution,[],[f115,f47])).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    v2_pre_topc(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f39])).
% 0.21/0.44  fof(f115,plain,(
% 0.21/0.44    v4_pre_topc(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.44    inference(subsumption_resolution,[],[f114,f48])).
% 0.21/0.44  fof(f114,plain,(
% 0.21/0.44    v4_pre_topc(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.44    inference(subsumption_resolution,[],[f113,f83])).
% 0.21/0.44  fof(f113,plain,(
% 0.21/0.44    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.44    inference(resolution,[],[f112,f73])).
% 0.21/0.44  fof(f73,plain,(
% 0.21/0.44    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f28])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.44    inference(flattening,[],[f27])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,axiom,(
% 0.21/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).
% 0.21/0.44  fof(f112,plain,(
% 0.21/0.44    ( ! [X0] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(k3_subset_1(k2_struct_0(sK0),X0),sK0)) )),
% 0.21/0.44    inference(forward_demodulation,[],[f111,f85])).
% 0.21/0.44  fof(f111,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)) )),
% 0.21/0.44    inference(forward_demodulation,[],[f110,f85])).
% 0.21/0.44  fof(f110,plain,(
% 0.21/0.44    ( ! [X0] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)) )),
% 0.21/0.44    inference(resolution,[],[f64,f48])).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f40])).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.44    inference(nnf_transformation,[],[f22])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,axiom,(
% 0.21/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).
% 0.21/0.44  fof(f120,plain,(
% 0.21/0.44    ( ! [X0] : (~v4_pre_topc(k3_subset_1(k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(X0,sK0)) )),
% 0.21/0.44    inference(forward_demodulation,[],[f119,f85])).
% 0.21/0.44  fof(f119,plain,(
% 0.21/0.44    ( ! [X0] : (~v4_pre_topc(k3_subset_1(k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0)) )),
% 0.21/0.44    inference(forward_demodulation,[],[f118,f85])).
% 0.21/0.44  fof(f118,plain,(
% 0.21/0.44    ( ! [X0] : (~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0)) )),
% 0.21/0.44    inference(resolution,[],[f65,f48])).
% 0.21/0.44  fof(f65,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X1,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f40])).
% 0.21/0.44  fof(f163,plain,(
% 0.21/0.44    r2_hidden(k2_struct_0(sK0),sK2) | ~r2_hidden(sK1,k2_struct_0(sK0)) | ~v3_pre_topc(k2_struct_0(sK0),sK0) | ~spl5_4),
% 0.21/0.44    inference(subsumption_resolution,[],[f162,f83])).
% 0.21/0.44  fof(f162,plain,(
% 0.21/0.44    r2_hidden(k2_struct_0(sK0),sK2) | ~r2_hidden(sK1,k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(k2_struct_0(sK0),sK0) | ~spl5_4),
% 0.21/0.44    inference(resolution,[],[f132,f90])).
% 0.21/0.44  fof(f90,plain,(
% 0.21/0.44    ( ! [X3] : (~v4_pre_topc(X3,sK0) | r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X3,sK0)) )),
% 0.21/0.44    inference(backward_demodulation,[],[f54,f85])).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    ( ! [X3] : (r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f39])).
% 0.21/0.44  fof(f132,plain,(
% 0.21/0.44    v4_pre_topc(k2_struct_0(sK0),sK0) | ~spl5_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f131])).
% 0.21/0.44  fof(f158,plain,(
% 0.21/0.44    ~spl5_5),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f157])).
% 0.21/0.44  fof(f157,plain,(
% 0.21/0.44    $false | ~spl5_5),
% 0.21/0.44    inference(subsumption_resolution,[],[f155,f79])).
% 0.21/0.44  fof(f155,plain,(
% 0.21/0.44    ~r1_tarski(sK2,sK3(sK0,sK2)) | ~spl5_5),
% 0.21/0.44    inference(resolution,[],[f144,f75])).
% 0.21/0.44  fof(f144,plain,(
% 0.21/0.44    r2_hidden(sK3(sK0,sK2),sK2) | ~spl5_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f142])).
% 0.21/0.44  fof(f142,plain,(
% 0.21/0.44    spl5_5 <=> r2_hidden(sK3(sK0,sK2),sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.44  fof(f150,plain,(
% 0.21/0.44    ~spl5_3 | spl5_4),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f149])).
% 0.21/0.44  fof(f149,plain,(
% 0.21/0.44    $false | (~spl5_3 | spl5_4)),
% 0.21/0.44    inference(subsumption_resolution,[],[f148,f133])).
% 0.21/0.44  fof(f133,plain,(
% 0.21/0.44    ~v4_pre_topc(k2_struct_0(sK0),sK0) | spl5_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f131])).
% 0.21/0.44  fof(f148,plain,(
% 0.21/0.44    v4_pre_topc(k2_struct_0(sK0),sK0) | ~spl5_3),
% 0.21/0.44    inference(forward_demodulation,[],[f147,f80])).
% 0.21/0.44  fof(f147,plain,(
% 0.21/0.44    v4_pre_topc(k3_subset_1(k2_struct_0(sK0),sK2),sK0) | ~spl5_3),
% 0.21/0.44    inference(subsumption_resolution,[],[f146,f81])).
% 0.21/0.44  fof(f81,plain,(
% 0.21/0.44    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(X0))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f59,f55])).
% 0.21/0.44  fof(f59,plain,(
% 0.21/0.44    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.44  fof(f146,plain,(
% 0.21/0.44    ~m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(k3_subset_1(k2_struct_0(sK0),sK2),sK0) | ~spl5_3),
% 0.21/0.44    inference(resolution,[],[f129,f112])).
% 0.21/0.44  fof(f129,plain,(
% 0.21/0.44    v3_pre_topc(sK2,sK0) | ~spl5_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f127])).
% 0.21/0.44  fof(f127,plain,(
% 0.21/0.44    spl5_3 <=> v3_pre_topc(sK2,sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.44  fof(f145,plain,(
% 0.21/0.44    spl5_3 | spl5_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f140,f142,f127])).
% 0.21/0.44  fof(f140,plain,(
% 0.21/0.44    r2_hidden(sK3(sK0,sK2),sK2) | v3_pre_topc(sK2,sK0)),
% 0.21/0.44    inference(resolution,[],[f138,f81])).
% 0.21/0.44  fof(f138,plain,(
% 0.21/0.44    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(sK3(sK0,X0),X0) | v3_pre_topc(X0,sK0)) )),
% 0.21/0.44    inference(forward_demodulation,[],[f137,f85])).
% 0.21/0.44  fof(f137,plain,(
% 0.21/0.44    ( ! [X0] : (r2_hidden(sK3(sK0,X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f136,f46])).
% 0.21/0.44  fof(f136,plain,(
% 0.21/0.44    ( ! [X0] : (r2_hidden(sK3(sK0,X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0) | v2_struct_0(sK0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f135,f48])).
% 0.21/0.44  fof(f135,plain,(
% 0.21/0.44    ( ! [X0] : (r2_hidden(sK3(sK0,X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v3_pre_topc(X0,sK0) | v2_struct_0(sK0)) )),
% 0.21/0.44    inference(resolution,[],[f70,f47])).
% 0.21/0.44  fof(f70,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v2_pre_topc(X0) | r2_hidden(sK3(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v3_pre_topc(X1,X0) | v2_struct_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f45])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,sK3(X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)))) & (! [X4] : ((r1_tarski(sK4(X0,X1,X4),X1) & m1_connsp_2(sK4(X0,X1,X4),X0,X4) & m1_subset_1(sK4(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f42,f44,f43])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    ! [X1,X0] : (? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,sK3(X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    ! [X4,X1,X0] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(sK4(X0,X1,X4),X1) & m1_connsp_2(sK4(X0,X1,X4),X0,X4) & m1_subset_1(sK4(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.44    inference(rectify,[],[f41])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.44    inference(nnf_transformation,[],[f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.44    inference(flattening,[],[f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f15])).
% 0.21/0.44  fof(f15,axiom,(
% 0.21/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_connsp_2)).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (9662)------------------------------
% 0.21/0.44  % (9662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (9662)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (9662)Memory used [KB]: 6268
% 0.21/0.44  % (9662)Time elapsed: 0.013 s
% 0.21/0.44  % (9662)------------------------------
% 0.21/0.44  % (9662)------------------------------
% 0.21/0.44  % (9645)Success in time 0.084 s
%------------------------------------------------------------------------------
