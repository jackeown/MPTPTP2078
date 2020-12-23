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
% DateTime   : Thu Dec  3 13:15:15 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 243 expanded)
%              Number of leaves         :   28 (  78 expanded)
%              Depth                    :   15
%              Number of atoms          :  600 (2317 expanded)
%              Number of equality atoms :   19 ( 151 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f301,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f160,f268,f272,f295,f300])).

fof(f300,plain,
    ( ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4 ),
    inference(avatar_contradiction_clause,[],[f299])).

fof(f299,plain,
    ( $false
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f135,f298])).

fof(f298,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | ~ spl11_2
    | ~ spl11_3 ),
    inference(subsumption_resolution,[],[f297,f147])).

fof(f147,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f109,f70])).

fof(f70,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f297,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | r2_hidden(u1_struct_0(sK2),k1_xboole_0)
    | ~ spl11_2
    | ~ spl11_3 ),
    inference(subsumption_resolution,[],[f296,f127])).

fof(f127,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK2)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl11_2
  <=> v3_pre_topc(u1_struct_0(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f296,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | ~ v3_pre_topc(u1_struct_0(sK2),sK2)
    | r2_hidden(u1_struct_0(sK2),k1_xboole_0)
    | ~ spl11_3 ),
    inference(subsumption_resolution,[],[f137,f131])).

fof(f131,plain,
    ( v4_pre_topc(u1_struct_0(sK2),sK2)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl11_3
  <=> v4_pre_topc(u1_struct_0(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f137,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | ~ v4_pre_topc(u1_struct_0(sK2),sK2)
    | ~ v3_pre_topc(u1_struct_0(sK2),sK2)
    | r2_hidden(u1_struct_0(sK2),k1_xboole_0) ),
    inference(resolution,[],[f111,f116])).

fof(f116,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f72,f71])).

fof(f71,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f72,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f111,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK3,X3)
      | ~ v4_pre_topc(X3,sK2)
      | ~ v3_pre_topc(X3,sK2)
      | r2_hidden(X3,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f68,f69])).

fof(f69,plain,(
    k1_xboole_0 = sK4 ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f38,f41,f40,f39])).

fof(f39,plain,
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

fof(f40,plain,
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

fof(f41,plain,
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

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).

fof(f68,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK4)
      | ~ r2_hidden(sK3,X3)
      | ~ v4_pre_topc(X3,sK2)
      | ~ v3_pre_topc(X3,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f135,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl11_4
  <=> r2_hidden(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f295,plain,(
    ~ spl11_5 ),
    inference(avatar_contradiction_clause,[],[f294])).

fof(f294,plain,
    ( $false
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f293,f62])).

fof(f62,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f293,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f292,f61])).

fof(f61,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f292,plain,
    ( ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f291,f60])).

fof(f60,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f291,plain,
    ( v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ spl11_5 ),
    inference(resolution,[],[f279,f159])).

fof(f159,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl11_5
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f279,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f277,f99])).

fof(f99,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK8(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( v4_pre_topc(sK8(X0),X0)
        & v3_pre_topc(sK8(X0),X0)
        & ~ v1_xboole_0(sK8(X0))
        & m1_subset_1(sK8(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f26,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v4_pre_topc(sK8(X0),X0)
        & v3_pre_topc(sK8(X0),X0)
        & ~ v1_xboole_0(sK8(X0))
        & m1_subset_1(sK8(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_tops_1)).

fof(f277,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(sK8(X0)) ) ),
    inference(resolution,[],[f176,f104])).

fof(f104,plain,(
    ! [X0] :
      ( r2_hidden(sK9(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK9(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f55,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK9(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f176,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK8(X0))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f98,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f98,plain,(
    ! [X0] :
      ( m1_subset_1(sK8(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f272,plain,(
    spl11_3 ),
    inference(avatar_contradiction_clause,[],[f271])).

fof(f271,plain,
    ( $false
    | spl11_3 ),
    inference(subsumption_resolution,[],[f270,f61])).

fof(f270,plain,
    ( ~ v2_pre_topc(sK2)
    | spl11_3 ),
    inference(subsumption_resolution,[],[f269,f62])).

fof(f269,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl11_3 ),
    inference(resolution,[],[f140,f153])).

fof(f153,plain,(
    ! [X0] :
      ( v4_pre_topc(u1_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f152,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f152,plain,(
    ! [X0] :
      ( v4_pre_topc(u1_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(superposition,[],[f102,f73])).

fof(f73,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f102,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

fof(f140,plain,
    ( ~ v4_pre_topc(u1_struct_0(sK2),sK2)
    | spl11_3 ),
    inference(avatar_component_clause,[],[f130])).

fof(f268,plain,(
    spl11_2 ),
    inference(avatar_contradiction_clause,[],[f267])).

fof(f267,plain,
    ( $false
    | spl11_2 ),
    inference(subsumption_resolution,[],[f266,f144])).

fof(f144,plain,(
    sP0(sK2) ),
    inference(subsumption_resolution,[],[f143,f61])).

fof(f143,plain,
    ( ~ v2_pre_topc(sK2)
    | sP0(sK2) ),
    inference(resolution,[],[f75,f118])).

fof(f118,plain,(
    sP1(sK2) ),
    inference(resolution,[],[f95,f62])).

fof(f95,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | sP1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f23,f35,f34])).

fof(f34,plain,(
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

fof(f35,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(rectify,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

fof(f75,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ v2_pre_topc(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v2_pre_topc(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f266,plain,
    ( ~ sP0(sK2)
    | spl11_2 ),
    inference(subsumption_resolution,[],[f265,f62])).

fof(f265,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ sP0(sK2)
    | spl11_2 ),
    inference(resolution,[],[f263,f139])).

fof(f139,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK2),sK2)
    | spl11_2 ),
    inference(avatar_component_clause,[],[f126])).

fof(f263,plain,(
    ! [X1] :
      ( v3_pre_topc(u1_struct_0(X1),X1)
      | ~ l1_pre_topc(X1)
      | ~ sP0(X1) ) ),
    inference(resolution,[],[f206,f77])).

fof(f77,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f46,f49,f48,f47])).

fof(f47,plain,(
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

fof(f48,plain,(
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

fof(f49,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
          & r1_tarski(X3,u1_pre_topc(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK7(X0)),u1_pre_topc(X0))
        & r1_tarski(sK7(X0),u1_pre_topc(X0))
        & m1_subset_1(sK7(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f206,plain,(
    ! [X0] :
      ( ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | v3_pre_topc(u1_struct_0(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f97,f116])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f160,plain,
    ( spl11_4
    | spl11_5 ),
    inference(avatar_split_clause,[],[f154,f158,f134])).

fof(f154,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | r2_hidden(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f108,f63])).

fof(f63,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f42])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:41:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (24556)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.43  % (24556)Refutation not found, incomplete strategy% (24556)------------------------------
% 0.22/0.43  % (24556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (24556)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.43  
% 0.22/0.43  % (24556)Memory used [KB]: 1791
% 0.22/0.43  % (24556)Time elapsed: 0.008 s
% 0.22/0.43  % (24556)------------------------------
% 0.22/0.43  % (24556)------------------------------
% 0.22/0.46  % (24557)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.47  % (24551)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.51  % (24545)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % (24547)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  % (24546)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (24543)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (24546)Refutation not found, incomplete strategy% (24546)------------------------------
% 0.22/0.51  % (24546)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (24546)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (24546)Memory used [KB]: 10618
% 0.22/0.51  % (24546)Time elapsed: 0.080 s
% 0.22/0.51  % (24546)------------------------------
% 0.22/0.51  % (24546)------------------------------
% 0.22/0.51  % (24552)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.52  % (24548)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.22/0.52  % (24560)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.22/0.52  % (24558)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 1.22/0.52  % (24554)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 1.22/0.52  % (24553)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 1.22/0.53  % (24555)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.22/0.53  % (24553)Refutation not found, incomplete strategy% (24553)------------------------------
% 1.22/0.53  % (24553)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.53  % (24553)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.53  
% 1.22/0.53  % (24553)Memory used [KB]: 6140
% 1.22/0.53  % (24553)Time elapsed: 0.102 s
% 1.22/0.53  % (24553)------------------------------
% 1.22/0.53  % (24553)------------------------------
% 1.22/0.53  % (24563)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 1.22/0.53  % (24562)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 1.22/0.53  % (24544)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.22/0.53  % (24563)Refutation not found, incomplete strategy% (24563)------------------------------
% 1.22/0.53  % (24563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.53  % (24563)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.53  
% 1.22/0.53  % (24563)Memory used [KB]: 10618
% 1.22/0.53  % (24563)Time elapsed: 0.100 s
% 1.22/0.53  % (24563)------------------------------
% 1.22/0.53  % (24563)------------------------------
% 1.22/0.53  % (24545)Refutation found. Thanks to Tanya!
% 1.22/0.53  % SZS status Theorem for theBenchmark
% 1.22/0.53  % SZS output start Proof for theBenchmark
% 1.22/0.53  fof(f301,plain,(
% 1.22/0.53    $false),
% 1.22/0.53    inference(avatar_sat_refutation,[],[f160,f268,f272,f295,f300])).
% 1.22/0.53  fof(f300,plain,(
% 1.22/0.53    ~spl11_2 | ~spl11_3 | ~spl11_4),
% 1.22/0.53    inference(avatar_contradiction_clause,[],[f299])).
% 1.22/0.53  fof(f299,plain,(
% 1.22/0.53    $false | (~spl11_2 | ~spl11_3 | ~spl11_4)),
% 1.22/0.53    inference(subsumption_resolution,[],[f135,f298])).
% 1.22/0.53  fof(f298,plain,(
% 1.22/0.53    ~r2_hidden(sK3,u1_struct_0(sK2)) | (~spl11_2 | ~spl11_3)),
% 1.22/0.53    inference(subsumption_resolution,[],[f297,f147])).
% 1.22/0.53  fof(f147,plain,(
% 1.22/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.22/0.53    inference(resolution,[],[f109,f70])).
% 1.22/0.53  fof(f70,plain,(
% 1.22/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.22/0.53    inference(cnf_transformation,[],[f2])).
% 1.22/0.53  fof(f2,axiom,(
% 1.22/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.22/0.53  fof(f109,plain,(
% 1.22/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.22/0.53    inference(cnf_transformation,[],[f32])).
% 1.22/0.53  fof(f32,plain,(
% 1.22/0.53    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.22/0.53    inference(ennf_transformation,[],[f7])).
% 1.22/0.53  fof(f7,axiom,(
% 1.22/0.53    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.22/0.53  fof(f297,plain,(
% 1.22/0.53    ~r2_hidden(sK3,u1_struct_0(sK2)) | r2_hidden(u1_struct_0(sK2),k1_xboole_0) | (~spl11_2 | ~spl11_3)),
% 1.22/0.53    inference(subsumption_resolution,[],[f296,f127])).
% 1.22/0.53  fof(f127,plain,(
% 1.22/0.53    v3_pre_topc(u1_struct_0(sK2),sK2) | ~spl11_2),
% 1.22/0.53    inference(avatar_component_clause,[],[f126])).
% 1.22/0.53  fof(f126,plain,(
% 1.22/0.53    spl11_2 <=> v3_pre_topc(u1_struct_0(sK2),sK2)),
% 1.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 1.22/0.53  fof(f296,plain,(
% 1.22/0.53    ~r2_hidden(sK3,u1_struct_0(sK2)) | ~v3_pre_topc(u1_struct_0(sK2),sK2) | r2_hidden(u1_struct_0(sK2),k1_xboole_0) | ~spl11_3),
% 1.22/0.53    inference(subsumption_resolution,[],[f137,f131])).
% 1.22/0.53  fof(f131,plain,(
% 1.22/0.53    v4_pre_topc(u1_struct_0(sK2),sK2) | ~spl11_3),
% 1.22/0.53    inference(avatar_component_clause,[],[f130])).
% 1.22/0.53  fof(f130,plain,(
% 1.22/0.53    spl11_3 <=> v4_pre_topc(u1_struct_0(sK2),sK2)),
% 1.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 1.22/0.53  fof(f137,plain,(
% 1.22/0.53    ~r2_hidden(sK3,u1_struct_0(sK2)) | ~v4_pre_topc(u1_struct_0(sK2),sK2) | ~v3_pre_topc(u1_struct_0(sK2),sK2) | r2_hidden(u1_struct_0(sK2),k1_xboole_0)),
% 1.22/0.53    inference(resolution,[],[f111,f116])).
% 1.22/0.53  fof(f116,plain,(
% 1.22/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.22/0.53    inference(forward_demodulation,[],[f72,f71])).
% 1.22/0.53  fof(f71,plain,(
% 1.22/0.53    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.22/0.53    inference(cnf_transformation,[],[f3])).
% 1.22/0.53  fof(f3,axiom,(
% 1.22/0.53    ! [X0] : k2_subset_1(X0) = X0),
% 1.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.22/0.53  fof(f72,plain,(
% 1.22/0.53    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.22/0.53    inference(cnf_transformation,[],[f4])).
% 1.22/0.53  fof(f4,axiom,(
% 1.22/0.53    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.22/0.53  fof(f111,plain,(
% 1.22/0.53    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) | ~r2_hidden(sK3,X3) | ~v4_pre_topc(X3,sK2) | ~v3_pre_topc(X3,sK2) | r2_hidden(X3,k1_xboole_0)) )),
% 1.22/0.53    inference(forward_demodulation,[],[f68,f69])).
% 1.22/0.53  fof(f69,plain,(
% 1.22/0.53    k1_xboole_0 = sK4),
% 1.22/0.53    inference(cnf_transformation,[],[f42])).
% 1.22/0.53  fof(f42,plain,(
% 1.22/0.53    ((k1_xboole_0 = sK4 & ! [X3] : (((r2_hidden(X3,sK4) | ~r2_hidden(sK3,X3) | ~v4_pre_topc(X3,sK2) | ~v3_pre_topc(X3,sK2)) & ((r2_hidden(sK3,X3) & v4_pre_topc(X3,sK2) & v3_pre_topc(X3,sK2)) | ~r2_hidden(X3,sK4))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 1.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f38,f41,f40,f39])).
% 1.22/0.53  fof(f39,plain,(
% 1.22/0.53    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK2) | ~v3_pre_topc(X3,sK2)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK2) & v3_pre_topc(X3,sK2)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 1.22/0.53    introduced(choice_axiom,[])).
% 1.22/0.53  fof(f40,plain,(
% 1.22/0.53    ? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK2) | ~v3_pre_topc(X3,sK2)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK2) & v3_pre_topc(X3,sK2)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & m1_subset_1(X1,u1_struct_0(sK2))) => (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK3,X3) | ~v4_pre_topc(X3,sK2) | ~v3_pre_topc(X3,sK2)) & ((r2_hidden(sK3,X3) & v4_pre_topc(X3,sK2) & v3_pre_topc(X3,sK2)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & m1_subset_1(sK3,u1_struct_0(sK2)))),
% 1.22/0.53    introduced(choice_axiom,[])).
% 1.22/0.53  fof(f41,plain,(
% 1.22/0.53    ? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK3,X3) | ~v4_pre_topc(X3,sK2) | ~v3_pre_topc(X3,sK2)) & ((r2_hidden(sK3,X3) & v4_pre_topc(X3,sK2) & v3_pre_topc(X3,sK2)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) => (k1_xboole_0 = sK4 & ! [X3] : (((r2_hidden(X3,sK4) | ~r2_hidden(sK3,X3) | ~v4_pre_topc(X3,sK2) | ~v3_pre_topc(X3,sK2)) & ((r2_hidden(sK3,X3) & v4_pre_topc(X3,sK2) & v3_pre_topc(X3,sK2)) | ~r2_hidden(X3,sK4))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))))),
% 1.22/0.53    introduced(choice_axiom,[])).
% 1.22/0.53  fof(f38,plain,(
% 1.22/0.53    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.22/0.53    inference(flattening,[],[f37])).
% 1.22/0.53  fof(f37,plain,(
% 1.22/0.53    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | (~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0))) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.22/0.53    inference(nnf_transformation,[],[f19])).
% 1.22/0.53  fof(f19,plain,(
% 1.22/0.53    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.22/0.53    inference(flattening,[],[f18])).
% 1.22/0.53  fof(f18,plain,(
% 1.22/0.53    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.22/0.53    inference(ennf_transformation,[],[f16])).
% 1.22/0.53  fof(f16,negated_conjecture,(
% 1.22/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 1.22/0.53    inference(negated_conjecture,[],[f15])).
% 1.22/0.53  fof(f15,conjecture,(
% 1.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 1.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).
% 1.22/0.53  fof(f68,plain,(
% 1.22/0.53    ( ! [X3] : (r2_hidden(X3,sK4) | ~r2_hidden(sK3,X3) | ~v4_pre_topc(X3,sK2) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.22/0.53    inference(cnf_transformation,[],[f42])).
% 1.22/0.53  fof(f135,plain,(
% 1.22/0.53    r2_hidden(sK3,u1_struct_0(sK2)) | ~spl11_4),
% 1.22/0.53    inference(avatar_component_clause,[],[f134])).
% 1.22/0.53  fof(f134,plain,(
% 1.22/0.53    spl11_4 <=> r2_hidden(sK3,u1_struct_0(sK2))),
% 1.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 1.22/0.53  fof(f295,plain,(
% 1.22/0.53    ~spl11_5),
% 1.22/0.53    inference(avatar_contradiction_clause,[],[f294])).
% 1.22/0.53  fof(f294,plain,(
% 1.22/0.53    $false | ~spl11_5),
% 1.22/0.53    inference(subsumption_resolution,[],[f293,f62])).
% 1.22/0.53  fof(f62,plain,(
% 1.22/0.53    l1_pre_topc(sK2)),
% 1.22/0.53    inference(cnf_transformation,[],[f42])).
% 1.22/0.53  fof(f293,plain,(
% 1.22/0.53    ~l1_pre_topc(sK2) | ~spl11_5),
% 1.22/0.53    inference(subsumption_resolution,[],[f292,f61])).
% 1.22/0.53  fof(f61,plain,(
% 1.22/0.53    v2_pre_topc(sK2)),
% 1.22/0.53    inference(cnf_transformation,[],[f42])).
% 1.22/0.53  fof(f292,plain,(
% 1.22/0.53    ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | ~spl11_5),
% 1.22/0.53    inference(subsumption_resolution,[],[f291,f60])).
% 1.22/0.53  fof(f60,plain,(
% 1.22/0.53    ~v2_struct_0(sK2)),
% 1.22/0.53    inference(cnf_transformation,[],[f42])).
% 1.22/0.53  fof(f291,plain,(
% 1.22/0.53    v2_struct_0(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | ~spl11_5),
% 1.22/0.53    inference(resolution,[],[f279,f159])).
% 1.22/0.53  fof(f159,plain,(
% 1.22/0.53    v1_xboole_0(u1_struct_0(sK2)) | ~spl11_5),
% 1.22/0.53    inference(avatar_component_clause,[],[f158])).
% 1.22/0.53  fof(f158,plain,(
% 1.22/0.53    spl11_5 <=> v1_xboole_0(u1_struct_0(sK2))),
% 1.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 1.22/0.53  fof(f279,plain,(
% 1.22/0.53    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 1.22/0.53    inference(subsumption_resolution,[],[f277,f99])).
% 1.22/0.53  fof(f99,plain,(
% 1.22/0.53    ( ! [X0] : (~v1_xboole_0(sK8(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.22/0.53    inference(cnf_transformation,[],[f53])).
% 1.22/0.53  fof(f53,plain,(
% 1.22/0.53    ! [X0] : ((v4_pre_topc(sK8(X0),X0) & v3_pre_topc(sK8(X0),X0) & ~v1_xboole_0(sK8(X0)) & m1_subset_1(sK8(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f26,f52])).
% 1.22/0.53  fof(f52,plain,(
% 1.22/0.53    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v4_pre_topc(sK8(X0),X0) & v3_pre_topc(sK8(X0),X0) & ~v1_xboole_0(sK8(X0)) & m1_subset_1(sK8(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.22/0.53    introduced(choice_axiom,[])).
% 1.22/0.53  fof(f26,plain,(
% 1.22/0.53    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.22/0.53    inference(flattening,[],[f25])).
% 1.22/0.53  fof(f25,plain,(
% 1.22/0.53    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.22/0.53    inference(ennf_transformation,[],[f14])).
% 1.22/0.53  fof(f14,axiom,(
% 1.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_tops_1)).
% 1.22/0.53  fof(f277,plain,(
% 1.22/0.53    ( ! [X0] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0)) | ~l1_pre_topc(X0) | v1_xboole_0(sK8(X0))) )),
% 1.22/0.53    inference(resolution,[],[f176,f104])).
% 1.22/0.53  fof(f104,plain,(
% 1.22/0.53    ( ! [X0] : (r2_hidden(sK9(X0),X0) | v1_xboole_0(X0)) )),
% 1.22/0.53    inference(cnf_transformation,[],[f57])).
% 1.22/0.53  fof(f57,plain,(
% 1.22/0.53    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK9(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f55,f56])).
% 1.22/0.53  fof(f56,plain,(
% 1.22/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK9(X0),X0))),
% 1.22/0.53    introduced(choice_axiom,[])).
% 1.22/0.53  fof(f55,plain,(
% 1.22/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.22/0.53    inference(rectify,[],[f54])).
% 1.22/0.53  fof(f54,plain,(
% 1.22/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.22/0.53    inference(nnf_transformation,[],[f1])).
% 1.22/0.53  fof(f1,axiom,(
% 1.22/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.22/0.53  fof(f176,plain,(
% 1.22/0.53    ( ! [X0,X1] : (~r2_hidden(X1,sK8(X0)) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 1.22/0.53    inference(resolution,[],[f98,f110])).
% 1.22/0.53  fof(f110,plain,(
% 1.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 1.22/0.53    inference(cnf_transformation,[],[f33])).
% 1.22/0.53  fof(f33,plain,(
% 1.22/0.53    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.22/0.53    inference(ennf_transformation,[],[f6])).
% 1.22/0.53  fof(f6,axiom,(
% 1.22/0.53    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.22/0.53  fof(f98,plain,(
% 1.22/0.53    ( ! [X0] : (m1_subset_1(sK8(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.22/0.53    inference(cnf_transformation,[],[f53])).
% 1.22/0.53  fof(f272,plain,(
% 1.22/0.53    spl11_3),
% 1.22/0.53    inference(avatar_contradiction_clause,[],[f271])).
% 1.22/0.53  fof(f271,plain,(
% 1.22/0.53    $false | spl11_3),
% 1.22/0.53    inference(subsumption_resolution,[],[f270,f61])).
% 1.22/0.53  fof(f270,plain,(
% 1.22/0.53    ~v2_pre_topc(sK2) | spl11_3),
% 1.22/0.53    inference(subsumption_resolution,[],[f269,f62])).
% 1.22/0.53  fof(f269,plain,(
% 1.22/0.53    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | spl11_3),
% 1.22/0.53    inference(resolution,[],[f140,f153])).
% 1.22/0.53  fof(f153,plain,(
% 1.22/0.53    ( ! [X0] : (v4_pre_topc(u1_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.22/0.53    inference(subsumption_resolution,[],[f152,f74])).
% 1.22/0.53  fof(f74,plain,(
% 1.22/0.53    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.22/0.53    inference(cnf_transformation,[],[f21])).
% 1.22/0.53  fof(f21,plain,(
% 1.22/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.22/0.53    inference(ennf_transformation,[],[f12])).
% 1.22/0.53  fof(f12,axiom,(
% 1.22/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.22/0.53  fof(f152,plain,(
% 1.22/0.53    ( ! [X0] : (v4_pre_topc(u1_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~l1_struct_0(X0)) )),
% 1.22/0.53    inference(superposition,[],[f102,f73])).
% 1.22/0.53  fof(f73,plain,(
% 1.22/0.53    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.22/0.53    inference(cnf_transformation,[],[f20])).
% 1.22/0.53  fof(f20,plain,(
% 1.22/0.53    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 1.22/0.53    inference(ennf_transformation,[],[f10])).
% 1.22/0.53  fof(f10,axiom,(
% 1.22/0.53    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 1.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.22/0.53  fof(f102,plain,(
% 1.22/0.53    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.22/0.53    inference(cnf_transformation,[],[f28])).
% 1.22/0.53  fof(f28,plain,(
% 1.22/0.53    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.22/0.53    inference(flattening,[],[f27])).
% 1.22/0.53  fof(f27,plain,(
% 1.22/0.53    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.22/0.53    inference(ennf_transformation,[],[f13])).
% 1.22/0.53  fof(f13,axiom,(
% 1.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 1.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).
% 1.22/0.53  fof(f140,plain,(
% 1.22/0.53    ~v4_pre_topc(u1_struct_0(sK2),sK2) | spl11_3),
% 1.22/0.53    inference(avatar_component_clause,[],[f130])).
% 1.22/0.53  fof(f268,plain,(
% 1.22/0.53    spl11_2),
% 1.22/0.53    inference(avatar_contradiction_clause,[],[f267])).
% 1.22/0.53  fof(f267,plain,(
% 1.22/0.53    $false | spl11_2),
% 1.22/0.53    inference(subsumption_resolution,[],[f266,f144])).
% 1.22/0.53  fof(f144,plain,(
% 1.22/0.53    sP0(sK2)),
% 1.22/0.53    inference(subsumption_resolution,[],[f143,f61])).
% 1.22/0.53  fof(f143,plain,(
% 1.22/0.53    ~v2_pre_topc(sK2) | sP0(sK2)),
% 1.22/0.53    inference(resolution,[],[f75,f118])).
% 1.22/0.53  fof(f118,plain,(
% 1.22/0.53    sP1(sK2)),
% 1.22/0.53    inference(resolution,[],[f95,f62])).
% 1.22/0.53  fof(f95,plain,(
% 1.22/0.53    ( ! [X0] : (~l1_pre_topc(X0) | sP1(X0)) )),
% 1.22/0.53    inference(cnf_transformation,[],[f36])).
% 1.22/0.53  fof(f36,plain,(
% 1.22/0.53    ! [X0] : (sP1(X0) | ~l1_pre_topc(X0))),
% 1.22/0.53    inference(definition_folding,[],[f23,f35,f34])).
% 1.22/0.53  fof(f34,plain,(
% 1.22/0.53    ! [X0] : (sP0(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))))),
% 1.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.22/0.53  fof(f35,plain,(
% 1.22/0.53    ! [X0] : ((v2_pre_topc(X0) <=> sP0(X0)) | ~sP1(X0))),
% 1.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.22/0.53  fof(f23,plain,(
% 1.22/0.53    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.22/0.53    inference(flattening,[],[f22])).
% 1.22/0.53  fof(f22,plain,(
% 1.22/0.53    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.22/0.53    inference(ennf_transformation,[],[f17])).
% 1.22/0.53  fof(f17,plain,(
% 1.22/0.53    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 1.22/0.53    inference(rectify,[],[f9])).
% 1.22/0.53  fof(f9,axiom,(
% 1.22/0.53    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 1.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).
% 1.22/0.53  fof(f75,plain,(
% 1.22/0.53    ( ! [X0] : (~sP1(X0) | ~v2_pre_topc(X0) | sP0(X0)) )),
% 1.22/0.53    inference(cnf_transformation,[],[f43])).
% 1.22/0.53  fof(f43,plain,(
% 1.22/0.53    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0)) & (sP0(X0) | ~v2_pre_topc(X0))) | ~sP1(X0))),
% 1.22/0.53    inference(nnf_transformation,[],[f35])).
% 1.22/0.53  fof(f266,plain,(
% 1.22/0.53    ~sP0(sK2) | spl11_2),
% 1.22/0.53    inference(subsumption_resolution,[],[f265,f62])).
% 1.22/0.53  fof(f265,plain,(
% 1.22/0.53    ~l1_pre_topc(sK2) | ~sP0(sK2) | spl11_2),
% 1.22/0.53    inference(resolution,[],[f263,f139])).
% 1.22/0.53  fof(f139,plain,(
% 1.22/0.53    ~v3_pre_topc(u1_struct_0(sK2),sK2) | spl11_2),
% 1.22/0.53    inference(avatar_component_clause,[],[f126])).
% 1.22/0.53  fof(f263,plain,(
% 1.22/0.53    ( ! [X1] : (v3_pre_topc(u1_struct_0(X1),X1) | ~l1_pre_topc(X1) | ~sP0(X1)) )),
% 1.22/0.53    inference(resolution,[],[f206,f77])).
% 1.22/0.53  fof(f77,plain,(
% 1.22/0.53    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~sP0(X0)) )),
% 1.22/0.53    inference(cnf_transformation,[],[f50])).
% 1.22/0.53  fof(f50,plain,(
% 1.22/0.53    ! [X0] : ((sP0(X0) | ((~r2_hidden(k9_subset_1(u1_struct_0(X0),sK5(X0),sK6(X0)),u1_pre_topc(X0)) & r2_hidden(sK6(X0),u1_pre_topc(X0)) & r2_hidden(sK5(X0),u1_pre_topc(X0)) & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK7(X0)),u1_pre_topc(X0)) & r1_tarski(sK7(X0),u1_pre_topc(X0)) & m1_subset_1(sK7(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((! [X4] : (! [X5] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0)) | ~r2_hidden(X5,u1_pre_topc(X0)) | ~r2_hidden(X4,u1_pre_topc(X0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X6] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0)) | ~r1_tarski(X6,u1_pre_topc(X0)) | ~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP0(X0)))),
% 1.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f46,f49,f48,f47])).
% 1.22/0.53  fof(f47,plain,(
% 1.22/0.53    ! [X0] : (? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK5(X0),X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(sK5(X0),u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.22/0.53    introduced(choice_axiom,[])).
% 1.22/0.53  fof(f48,plain,(
% 1.22/0.53    ! [X0] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK5(X0),X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(sK5(X0),u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK5(X0),sK6(X0)),u1_pre_topc(X0)) & r2_hidden(sK6(X0),u1_pre_topc(X0)) & r2_hidden(sK5(X0),u1_pre_topc(X0)) & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.22/0.53    introduced(choice_axiom,[])).
% 1.22/0.53  fof(f49,plain,(
% 1.22/0.53    ! [X0] : (? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK7(X0)),u1_pre_topc(X0)) & r1_tarski(sK7(X0),u1_pre_topc(X0)) & m1_subset_1(sK7(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 1.22/0.53    introduced(choice_axiom,[])).
% 1.22/0.53  fof(f46,plain,(
% 1.22/0.53    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((! [X4] : (! [X5] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0)) | ~r2_hidden(X5,u1_pre_topc(X0)) | ~r2_hidden(X4,u1_pre_topc(X0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X6] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0)) | ~r1_tarski(X6,u1_pre_topc(X0)) | ~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP0(X0)))),
% 1.22/0.53    inference(rectify,[],[f45])).
% 1.22/0.53  fof(f45,plain,(
% 1.22/0.53    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP0(X0)))),
% 1.22/0.53    inference(flattening,[],[f44])).
% 1.22/0.53  fof(f44,plain,(
% 1.22/0.53    ! [X0] : ((sP0(X0) | (? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP0(X0)))),
% 1.22/0.53    inference(nnf_transformation,[],[f34])).
% 1.22/0.53  fof(f206,plain,(
% 1.22/0.53    ( ! [X0] : (~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | v3_pre_topc(u1_struct_0(X0),X0) | ~l1_pre_topc(X0)) )),
% 1.22/0.53    inference(resolution,[],[f97,f116])).
% 1.22/0.53  fof(f97,plain,(
% 1.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,u1_pre_topc(X0)) | v3_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.22/0.53    inference(cnf_transformation,[],[f51])).
% 1.22/0.53  fof(f51,plain,(
% 1.22/0.53    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.22/0.53    inference(nnf_transformation,[],[f24])).
% 1.22/0.53  fof(f24,plain,(
% 1.22/0.53    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.22/0.53    inference(ennf_transformation,[],[f11])).
% 1.22/0.53  fof(f11,axiom,(
% 1.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 1.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).
% 1.22/0.53  fof(f160,plain,(
% 1.22/0.53    spl11_4 | spl11_5),
% 1.22/0.53    inference(avatar_split_clause,[],[f154,f158,f134])).
% 1.22/0.53  fof(f154,plain,(
% 1.22/0.53    v1_xboole_0(u1_struct_0(sK2)) | r2_hidden(sK3,u1_struct_0(sK2))),
% 1.22/0.53    inference(resolution,[],[f108,f63])).
% 1.22/0.53  fof(f63,plain,(
% 1.22/0.53    m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.22/0.53    inference(cnf_transformation,[],[f42])).
% 1.22/0.53  fof(f108,plain,(
% 1.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.22/0.53    inference(cnf_transformation,[],[f31])).
% 1.22/0.53  fof(f31,plain,(
% 1.22/0.53    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.22/0.53    inference(flattening,[],[f30])).
% 1.22/0.53  fof(f30,plain,(
% 1.22/0.53    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.22/0.53    inference(ennf_transformation,[],[f5])).
% 1.22/0.53  fof(f5,axiom,(
% 1.22/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.22/0.53  % SZS output end Proof for theBenchmark
% 1.22/0.53  % (24545)------------------------------
% 1.22/0.53  % (24545)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.53  % (24545)Termination reason: Refutation
% 1.22/0.53  
% 1.22/0.53  % (24545)Memory used [KB]: 10746
% 1.22/0.53  % (24545)Time elapsed: 0.116 s
% 1.22/0.53  % (24545)------------------------------
% 1.22/0.53  % (24545)------------------------------
% 1.22/0.53  % (24542)Success in time 0.173 s
%------------------------------------------------------------------------------
