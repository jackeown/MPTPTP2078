%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 346 expanded)
%              Number of leaves         :   42 ( 138 expanded)
%              Depth                    :   13
%              Number of atoms          :  703 (1448 expanded)
%              Number of equality atoms :   55 (  90 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f308,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f89,f94,f99,f106,f111,f121,f123,f131,f136,f141,f153,f172,f187,f200,f233,f246,f253,f286,f294,f300,f305,f306,f307])).

% (5085)Termination reason: Refutation not found, incomplete strategy

% (5085)Memory used [KB]: 10618
% (5085)Time elapsed: 0.102 s
% (5085)------------------------------
% (5085)------------------------------
fof(f307,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | sK1 != k2_struct_0(sK0)
    | u1_struct_0(sK0) = sK1 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f306,plain,
    ( sK1 != k2_struct_0(sK0)
    | v3_tex_2(sK1,sK0)
    | ~ v3_tex_2(k2_struct_0(sK0),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f305,plain,
    ( ~ spl4_11
    | ~ spl4_28 ),
    inference(avatar_contradiction_clause,[],[f304])).

fof(f304,plain,
    ( $false
    | ~ spl4_11
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f302,f140])).

fof(f140,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl4_11
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f302,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl4_28 ),
    inference(resolution,[],[f293,f112])).

fof(f112,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f58,f57])).

fof(f57,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f293,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(X2))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X2)) )
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f292])).

fof(f292,plain,
    ( spl4_28
  <=> ! [X2] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X2))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f300,plain,
    ( ~ spl4_7
    | ~ spl4_11
    | spl4_12
    | ~ spl4_26
    | ~ spl4_27 ),
    inference(avatar_contradiction_clause,[],[f299])).

fof(f299,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_11
    | spl4_12
    | ~ spl4_26
    | ~ spl4_27 ),
    inference(unit_resulting_resolution,[],[f116,f151,f140,f112,f290,f285])).

fof(f285,plain,
    ( ! [X0,X1] :
        ( ~ v3_tex_2(X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | X0 = X1 )
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f284])).

fof(f284,plain,
    ( spl4_26
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X0,X1)
        | ~ v3_tex_2(X0,sK0)
        | X0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f290,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0))
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl4_27
  <=> r1_tarski(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f151,plain,
    ( sK1 != k2_struct_0(sK0)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl4_12
  <=> sK1 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f116,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl4_7
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f294,plain,
    ( spl4_27
    | spl4_28
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f279,f138,f292,f288])).

fof(f279,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X2))
        | r1_tarski(sK1,k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(X2)) )
    | ~ spl4_11 ),
    inference(resolution,[],[f276,f140])).

fof(f276,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | r1_tarski(X2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f274])).

fof(f274,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | r1_tarski(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f188,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK3(X0,X1,X2),X2)
            & r2_hidden(sK3(X0,X1,X2),X1)
            & m1_subset_1(sK3(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f47])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK3(X0,X1,X2),X2)
        & r2_hidden(sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

fof(f188,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK3(X2,X0,X1),X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
      | r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X3)) ) ),
    inference(resolution,[],[f77,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f286,plain,
    ( spl4_26
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f277,f231,f128,f96,f284])).

fof(f96,plain,
    ( spl4_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f128,plain,
    ( spl4_9
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f231,plain,
    ( spl4_19
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v2_tex_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f277,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X0,X1)
        | ~ v3_tex_2(X0,sK0)
        | X0 = X1 )
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f221,f232])).

fof(f232,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v2_tex_2(X0,sK0) )
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f231])).

fof(f221,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X0,X1)
        | ~ v2_tex_2(X1,sK0)
        | ~ v3_tex_2(X0,sK0)
        | X0 = X1 )
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f220,f130])).

fof(f130,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f128])).

fof(f220,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(X0,X1)
        | ~ v2_tex_2(X1,sK0)
        | ~ v3_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | X0 = X1 )
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f219,f130])).

fof(f219,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | X0 = X1 )
    | ~ spl4_4 ),
    inference(resolution,[],[f66,f98])).

fof(f98,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f96])).

% (5081)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
fof(f66,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,X3)
      | ~ v2_tex_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK2(X0,X1) != X1
                & r1_tarski(X1,sK2(X0,X1))
                & v2_tex_2(sK2(X0,X1),X0)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK2(X0,X1) != X1
        & r1_tarski(X1,sK2(X0,X1))
        & v2_tex_2(sK2(X0,X1),X0)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

fof(f253,plain,
    ( spl4_22
    | ~ spl4_16
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f248,f244,f197,f250])).

fof(f250,plain,
    ( spl4_22
  <=> v3_tex_2(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f197,plain,
    ( spl4_16
  <=> v1_tops_1(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f244,plain,
    ( spl4_21
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v1_tops_1(X0,sK0)
        | v3_tex_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f248,plain,
    ( v3_tex_2(k2_struct_0(sK0),sK0)
    | ~ spl4_16
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f247,f112])).

fof(f247,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v3_tex_2(k2_struct_0(sK0),sK0)
    | ~ spl4_16
    | ~ spl4_21 ),
    inference(resolution,[],[f245,f199])).

fof(f199,plain,
    ( v1_tops_1(k2_struct_0(sK0),sK0)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f197])).

fof(f245,plain,
    ( ! [X0] :
        ( ~ v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v3_tex_2(X0,sK0) )
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f244])).

fof(f246,plain,
    ( spl4_21
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f237,f231,f128,f96,f86,f81,f244])).

fof(f81,plain,
    ( spl4_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f86,plain,
    ( spl4_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f237,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v1_tops_1(X0,sK0)
        | v3_tex_2(X0,sK0) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f218,f232])).

fof(f218,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | ~ v1_tops_1(X0,sK0)
        | v3_tex_2(X0,sK0) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f217,f130])).

fof(f217,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_tex_2(X0,sK0) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f216,f83])).

fof(f83,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f216,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_tex_2(X0,sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f215,f88])).

fof(f88,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f215,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_tex_2(X0,sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f72,f98])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tex_2(X1,X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
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
         => ( ( v2_tex_2(X1,X0)
              & v1_tops_1(X1,X0) )
           => v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).

fof(f233,plain,
    ( spl4_19
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f229,f128,f96,f91,f81,f231])).

fof(f91,plain,
    ( spl4_3
  <=> v1_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f229,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v2_tex_2(X0,sK0) )
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f180,f130])).

fof(f180,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK0) )
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f179,f83])).

fof(f179,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f178,f98])).

fof(f178,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | v2_tex_2(X0,sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f160,f93])).

fof(f93,plain,
    ( v1_tdlat_3(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f160,plain,(
    ! [X0,X1] :
      ( ~ v1_tdlat_3(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_tex_2(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f71,f62])).

fof(f62,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(f71,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

fof(f200,plain,
    ( spl4_16
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f193,f184,f128,f96,f197])).

fof(f184,plain,
    ( spl4_15
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f193,plain,
    ( v1_tops_1(k2_struct_0(sK0),sK0)
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f192,f112])).

fof(f192,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_tops_1(k2_struct_0(sK0),sK0)
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f191,f130])).

fof(f191,plain,
    ( v1_tops_1(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f190,f98])).

fof(f190,plain,
    ( v1_tops_1(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_9
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f189,f130])).

fof(f189,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | v1_tops_1(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_15 ),
    inference(superposition,[],[f64,f186])).

fof(f186,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f184])).

fof(f64,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) != k2_pre_topc(X0,X1)
      | v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

fof(f187,plain,
    ( spl4_15
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f142,f96,f184])).

fof(f142,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))
    | ~ spl4_4 ),
    inference(resolution,[],[f61,f98])).

fof(f61,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tops_1)).

fof(f172,plain,
    ( ~ spl4_8
    | ~ spl4_13 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f170,f100])).

fof(f100,plain,(
    ! [X0] : ~ v1_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f56,f57])).

fof(f56,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

fof(f170,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f119,f157])).

fof(f157,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl4_13
  <=> u1_struct_0(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f119,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl4_8
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f153,plain,
    ( spl4_12
    | spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f145,f138,f133,f150])).

fof(f133,plain,
    ( spl4_10
  <=> v1_subset_1(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f145,plain,
    ( sK1 = k2_struct_0(sK0)
    | spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f144,f135])).

fof(f135,plain,
    ( ~ v1_subset_1(sK1,k2_struct_0(sK0))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f133])).

fof(f144,plain,
    ( sK1 = k2_struct_0(sK0)
    | v1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl4_11 ),
    inference(resolution,[],[f74,f140])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f141,plain,
    ( spl4_11
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f126,f108,f103,f138])).

fof(f103,plain,
    ( spl4_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f108,plain,
    ( spl4_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f126,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f110,f124])).

fof(f124,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_5 ),
    inference(resolution,[],[f59,f105])).

fof(f105,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f103])).

fof(f59,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

% (5081)Refutation not found, incomplete strategy% (5081)------------------------------
% (5081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5081)Termination reason: Refutation not found, incomplete strategy

% (5081)Memory used [KB]: 1663
% (5081)Time elapsed: 0.072 s
% (5081)------------------------------
% (5081)------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f110,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f108])).

fof(f136,plain,
    ( ~ spl4_10
    | ~ spl4_5
    | spl4_8 ),
    inference(avatar_split_clause,[],[f125,f118,f103,f133])).

fof(f125,plain,
    ( ~ v1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl4_5
    | spl4_8 ),
    inference(backward_demodulation,[],[f120,f124])).

fof(f120,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f118])).

fof(f131,plain,
    ( spl4_9
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f124,f103,f128])).

fof(f123,plain,
    ( ~ spl4_7
    | spl4_8 ),
    inference(avatar_split_clause,[],[f122,f118,f114])).

fof(f122,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | spl4_8 ),
    inference(subsumption_resolution,[],[f55,f120])).

fof(f55,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( v1_subset_1(sK1,u1_struct_0(sK0))
      | ~ v3_tex_2(sK1,sK0) )
    & ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
      | v3_tex_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v1_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( v1_subset_1(X1,u1_struct_0(X0))
              | ~ v3_tex_2(X1,X0) )
            & ( ~ v1_subset_1(X1,u1_struct_0(X0))
              | v3_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(sK0))
            | ~ v3_tex_2(X1,sK0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(sK0))
            | v3_tex_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v1_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X1] :
        ( ( v1_subset_1(X1,u1_struct_0(sK0))
          | ~ v3_tex_2(X1,sK0) )
        & ( ~ v1_subset_1(X1,u1_struct_0(sK0))
          | v3_tex_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( v1_subset_1(sK1,u1_struct_0(sK0))
        | ~ v3_tex_2(sK1,sK0) )
      & ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
        | v3_tex_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).

fof(f121,plain,
    ( spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f54,f118,f114])).

fof(f54,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f111,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f53,f108])).

fof(f53,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f106,plain,
    ( spl4_5
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f101,f96,f103])).

fof(f101,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f60,f98])).

% (5075)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
fof(f60,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f99,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f52,f96])).

fof(f52,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f94,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f51,f91])).

fof(f51,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f89,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f50,f86])).

fof(f50,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f84,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f49,f81])).

fof(f49,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:55:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.49  % (5074)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.50  % (5078)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (5076)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.50  % (5091)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.50  % (5088)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (5076)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % (5092)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.50  % (5080)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.50  % (5093)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.50  % (5083)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.50  % (5080)Refutation not found, incomplete strategy% (5080)------------------------------
% 0.20/0.50  % (5080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (5074)Refutation not found, incomplete strategy% (5074)------------------------------
% 0.20/0.51  % (5074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (5074)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (5074)Memory used [KB]: 10618
% 0.20/0.51  % (5074)Time elapsed: 0.085 s
% 0.20/0.51  % (5074)------------------------------
% 0.20/0.51  % (5074)------------------------------
% 0.20/0.51  % (5098)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.51  % (5077)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  % (5100)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.51  % (5089)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.51  % (5085)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.51  % (5085)Refutation not found, incomplete strategy% (5085)------------------------------
% 0.20/0.51  % (5085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (5080)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (5080)Memory used [KB]: 10618
% 0.20/0.51  % (5080)Time elapsed: 0.080 s
% 0.20/0.51  % (5080)------------------------------
% 0.20/0.51  % (5080)------------------------------
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f308,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f84,f89,f94,f99,f106,f111,f121,f123,f131,f136,f141,f153,f172,f187,f200,f233,f246,f253,f286,f294,f300,f305,f306,f307])).
% 0.20/0.51  % (5085)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (5085)Memory used [KB]: 10618
% 0.20/0.51  % (5085)Time elapsed: 0.102 s
% 0.20/0.51  % (5085)------------------------------
% 0.20/0.51  % (5085)------------------------------
% 0.20/0.51  fof(f307,plain,(
% 0.20/0.51    u1_struct_0(sK0) != k2_struct_0(sK0) | sK1 != k2_struct_0(sK0) | u1_struct_0(sK0) = sK1),
% 0.20/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.51  fof(f306,plain,(
% 0.20/0.51    sK1 != k2_struct_0(sK0) | v3_tex_2(sK1,sK0) | ~v3_tex_2(k2_struct_0(sK0),sK0)),
% 0.20/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.51  fof(f305,plain,(
% 0.20/0.51    ~spl4_11 | ~spl4_28),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f304])).
% 0.20/0.51  fof(f304,plain,(
% 0.20/0.51    $false | (~spl4_11 | ~spl4_28)),
% 0.20/0.51    inference(subsumption_resolution,[],[f302,f140])).
% 0.20/0.51  fof(f140,plain,(
% 0.20/0.51    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl4_11),
% 0.20/0.51    inference(avatar_component_clause,[],[f138])).
% 0.20/0.51  fof(f138,plain,(
% 0.20/0.51    spl4_11 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.51  fof(f302,plain,(
% 0.20/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl4_28),
% 0.20/0.51    inference(resolution,[],[f293,f112])).
% 0.20/0.51  fof(f112,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(forward_demodulation,[],[f58,f57])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.51  fof(f293,plain,(
% 0.20/0.51    ( ! [X2] : (~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(X2)) | ~m1_subset_1(sK1,k1_zfmisc_1(X2))) ) | ~spl4_28),
% 0.20/0.51    inference(avatar_component_clause,[],[f292])).
% 0.20/0.51  fof(f292,plain,(
% 0.20/0.51    spl4_28 <=> ! [X2] : (~m1_subset_1(sK1,k1_zfmisc_1(X2)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(X2)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.20/0.51  fof(f300,plain,(
% 0.20/0.51    ~spl4_7 | ~spl4_11 | spl4_12 | ~spl4_26 | ~spl4_27),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f299])).
% 0.20/0.51  fof(f299,plain,(
% 0.20/0.51    $false | (~spl4_7 | ~spl4_11 | spl4_12 | ~spl4_26 | ~spl4_27)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f116,f151,f140,f112,f290,f285])).
% 0.20/0.51  fof(f285,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v3_tex_2(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | X0 = X1) ) | ~spl4_26),
% 0.20/0.51    inference(avatar_component_clause,[],[f284])).
% 0.20/0.51  fof(f284,plain,(
% 0.20/0.51    spl4_26 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,X1) | ~v3_tex_2(X0,sK0) | X0 = X1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.20/0.51  fof(f290,plain,(
% 0.20/0.51    r1_tarski(sK1,k2_struct_0(sK0)) | ~spl4_27),
% 0.20/0.51    inference(avatar_component_clause,[],[f288])).
% 0.20/0.51  fof(f288,plain,(
% 0.20/0.51    spl4_27 <=> r1_tarski(sK1,k2_struct_0(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.20/0.51  fof(f151,plain,(
% 0.20/0.51    sK1 != k2_struct_0(sK0) | spl4_12),
% 0.20/0.51    inference(avatar_component_clause,[],[f150])).
% 0.20/0.51  fof(f150,plain,(
% 0.20/0.51    spl4_12 <=> sK1 = k2_struct_0(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.51  fof(f116,plain,(
% 0.20/0.51    v3_tex_2(sK1,sK0) | ~spl4_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f114])).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    spl4_7 <=> v3_tex_2(sK1,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.51  fof(f294,plain,(
% 0.20/0.51    spl4_27 | spl4_28 | ~spl4_11),
% 0.20/0.51    inference(avatar_split_clause,[],[f279,f138,f292,f288])).
% 0.20/0.51  fof(f279,plain,(
% 0.20/0.51    ( ! [X2] : (~m1_subset_1(sK1,k1_zfmisc_1(X2)) | r1_tarski(sK1,k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(X2))) ) | ~spl4_11),
% 0.20/0.51    inference(resolution,[],[f276,f140])).
% 0.20/0.51  fof(f276,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | r1_tarski(X2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f274])).
% 0.20/0.51  fof(f274,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | r1_tarski(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) )),
% 0.20/0.51    inference(resolution,[],[f188,f78])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | (~r2_hidden(sK3(X0,X1,X2),X2) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) => (~r2_hidden(sK3(X0,X1,X2),X2) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),X0)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(flattening,[],[f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).
% 0.20/0.51  fof(f188,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(sK3(X2,X0,X1),X3) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~m1_subset_1(X0,k1_zfmisc_1(X2)) | r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X3))) )),
% 0.20/0.51    inference(resolution,[],[f77,f75])).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X1) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f48])).
% 0.20/0.51  fof(f286,plain,(
% 0.20/0.51    spl4_26 | ~spl4_4 | ~spl4_9 | ~spl4_19),
% 0.20/0.51    inference(avatar_split_clause,[],[f277,f231,f128,f96,f284])).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    spl4_4 <=> l1_pre_topc(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.51  fof(f128,plain,(
% 0.20/0.51    spl4_9 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.51  fof(f231,plain,(
% 0.20/0.51    spl4_19 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_tex_2(X0,sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.20/0.51  fof(f277,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,X1) | ~v3_tex_2(X0,sK0) | X0 = X1) ) | (~spl4_4 | ~spl4_9 | ~spl4_19)),
% 0.20/0.51    inference(subsumption_resolution,[],[f221,f232])).
% 0.20/0.51  fof(f232,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_tex_2(X0,sK0)) ) | ~spl4_19),
% 0.20/0.51    inference(avatar_component_clause,[],[f231])).
% 0.20/0.51  fof(f221,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,X1) | ~v2_tex_2(X1,sK0) | ~v3_tex_2(X0,sK0) | X0 = X1) ) | (~spl4_4 | ~spl4_9)),
% 0.20/0.51    inference(forward_demodulation,[],[f220,f130])).
% 0.20/0.51  fof(f130,plain,(
% 0.20/0.51    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl4_9),
% 0.20/0.51    inference(avatar_component_clause,[],[f128])).
% 0.20/0.51  fof(f220,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,X1) | ~v2_tex_2(X1,sK0) | ~v3_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | X0 = X1) ) | (~spl4_4 | ~spl4_9)),
% 0.20/0.51    inference(forward_demodulation,[],[f219,f130])).
% 0.20/0.51  fof(f219,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | X0 = X1) ) | ~spl4_4),
% 0.20/0.51    inference(resolution,[],[f66,f98])).
% 0.20/0.51  fof(f98,plain,(
% 0.20/0.51    l1_pre_topc(sK0) | ~spl4_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f96])).
% 0.20/0.51  % (5081)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | X1 = X3) )),
% 0.20/0.51    inference(cnf_transformation,[],[f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(rectify,[],[f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).
% 0.20/0.51  fof(f253,plain,(
% 0.20/0.51    spl4_22 | ~spl4_16 | ~spl4_21),
% 0.20/0.51    inference(avatar_split_clause,[],[f248,f244,f197,f250])).
% 0.20/0.51  fof(f250,plain,(
% 0.20/0.51    spl4_22 <=> v3_tex_2(k2_struct_0(sK0),sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.20/0.51  fof(f197,plain,(
% 0.20/0.51    spl4_16 <=> v1_tops_1(k2_struct_0(sK0),sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.20/0.51  fof(f244,plain,(
% 0.20/0.51    spl4_21 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_1(X0,sK0) | v3_tex_2(X0,sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.20/0.51  fof(f248,plain,(
% 0.20/0.51    v3_tex_2(k2_struct_0(sK0),sK0) | (~spl4_16 | ~spl4_21)),
% 0.20/0.51    inference(subsumption_resolution,[],[f247,f112])).
% 0.20/0.51  fof(f247,plain,(
% 0.20/0.51    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v3_tex_2(k2_struct_0(sK0),sK0) | (~spl4_16 | ~spl4_21)),
% 0.20/0.51    inference(resolution,[],[f245,f199])).
% 0.20/0.51  fof(f199,plain,(
% 0.20/0.51    v1_tops_1(k2_struct_0(sK0),sK0) | ~spl4_16),
% 0.20/0.51    inference(avatar_component_clause,[],[f197])).
% 0.20/0.51  fof(f245,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v3_tex_2(X0,sK0)) ) | ~spl4_21),
% 0.20/0.51    inference(avatar_component_clause,[],[f244])).
% 0.20/0.51  fof(f246,plain,(
% 0.20/0.51    spl4_21 | spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_9 | ~spl4_19),
% 0.20/0.51    inference(avatar_split_clause,[],[f237,f231,f128,f96,f86,f81,f244])).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    spl4_1 <=> v2_struct_0(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    spl4_2 <=> v2_pre_topc(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.51  fof(f237,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_1(X0,sK0) | v3_tex_2(X0,sK0)) ) | (spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_9 | ~spl4_19)),
% 0.20/0.51    inference(subsumption_resolution,[],[f218,f232])).
% 0.20/0.51  fof(f218,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | ~v1_tops_1(X0,sK0) | v3_tex_2(X0,sK0)) ) | (spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_9)),
% 0.20/0.51    inference(forward_demodulation,[],[f217,f130])).
% 0.20/0.51  fof(f217,plain,(
% 0.20/0.51    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(X0,sK0)) ) | (spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.20/0.51    inference(subsumption_resolution,[],[f216,f83])).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    ~v2_struct_0(sK0) | spl4_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f81])).
% 0.20/0.51  fof(f216,plain,(
% 0.20/0.51    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(X0,sK0) | v2_struct_0(sK0)) ) | (~spl4_2 | ~spl4_4)),
% 0.20/0.51    inference(subsumption_resolution,[],[f215,f88])).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    v2_pre_topc(sK0) | ~spl4_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f86])).
% 0.20/0.51  fof(f215,plain,(
% 0.20/0.51    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(X0,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl4_4),
% 0.20/0.51    inference(resolution,[],[f72,f98])).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_tex_2(X1,X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) | (~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,axiom,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).
% 0.20/0.51  fof(f233,plain,(
% 0.20/0.51    spl4_19 | spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_9),
% 0.20/0.51    inference(avatar_split_clause,[],[f229,f128,f96,f91,f81,f231])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    spl4_3 <=> v1_tdlat_3(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.51  fof(f229,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_tex_2(X0,sK0)) ) | (spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_9)),
% 0.20/0.51    inference(forward_demodulation,[],[f180,f130])).
% 0.20/0.51  fof(f180,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) ) | (spl4_1 | ~spl4_3 | ~spl4_4)),
% 0.20/0.51    inference(subsumption_resolution,[],[f179,f83])).
% 0.20/0.51  fof(f179,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0) | v2_struct_0(sK0)) ) | (~spl4_3 | ~spl4_4)),
% 0.20/0.51    inference(subsumption_resolution,[],[f178,f98])).
% 0.20/0.51  fof(f178,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v2_tex_2(X0,sK0) | v2_struct_0(sK0)) ) | ~spl4_3),
% 0.20/0.51    inference(resolution,[],[f160,f93])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    v1_tdlat_3(sK0) | ~spl4_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f91])).
% 0.20/0.51  fof(f160,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_tdlat_3(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_tex_2(X1,X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f71,f62])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ( ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,axiom,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).
% 0.20/0.51  fof(f200,plain,(
% 0.20/0.51    spl4_16 | ~spl4_4 | ~spl4_9 | ~spl4_15),
% 0.20/0.51    inference(avatar_split_clause,[],[f193,f184,f128,f96,f197])).
% 0.20/0.51  fof(f184,plain,(
% 0.20/0.51    spl4_15 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.51  fof(f193,plain,(
% 0.20/0.51    v1_tops_1(k2_struct_0(sK0),sK0) | (~spl4_4 | ~spl4_9 | ~spl4_15)),
% 0.20/0.51    inference(subsumption_resolution,[],[f192,f112])).
% 0.20/0.51  fof(f192,plain,(
% 0.20/0.51    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v1_tops_1(k2_struct_0(sK0),sK0) | (~spl4_4 | ~spl4_9 | ~spl4_15)),
% 0.20/0.51    inference(forward_demodulation,[],[f191,f130])).
% 0.20/0.51  fof(f191,plain,(
% 0.20/0.51    v1_tops_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_4 | ~spl4_9 | ~spl4_15)),
% 0.20/0.51    inference(subsumption_resolution,[],[f190,f98])).
% 0.20/0.51  fof(f190,plain,(
% 0.20/0.51    v1_tops_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl4_9 | ~spl4_15)),
% 0.20/0.51    inference(subsumption_resolution,[],[f189,f130])).
% 0.20/0.51  fof(f189,plain,(
% 0.20/0.51    u1_struct_0(sK0) != k2_struct_0(sK0) | v1_tops_1(k2_struct_0(sK0),sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_15),
% 0.20/0.51    inference(superposition,[],[f64,f186])).
% 0.20/0.51  fof(f186,plain,(
% 0.20/0.51    k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) | ~spl4_15),
% 0.20/0.51    inference(avatar_component_clause,[],[f184])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    ( ! [X0,X1] : (u1_struct_0(X0) != k2_pre_topc(X0,X1) | v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).
% 0.20/0.51  fof(f187,plain,(
% 0.20/0.51    spl4_15 | ~spl4_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f142,f96,f184])).
% 0.20/0.51  fof(f142,plain,(
% 0.20/0.51    k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) | ~spl4_4),
% 0.20/0.51    inference(resolution,[],[f61,f98])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0] : (k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tops_1)).
% 0.20/0.51  fof(f172,plain,(
% 0.20/0.51    ~spl4_8 | ~spl4_13),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f171])).
% 0.20/0.51  fof(f171,plain,(
% 0.20/0.51    $false | (~spl4_8 | ~spl4_13)),
% 0.20/0.51    inference(subsumption_resolution,[],[f170,f100])).
% 0.20/0.51  fof(f100,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_subset_1(X0,X0)) )),
% 0.20/0.51    inference(backward_demodulation,[],[f56,f57])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).
% 0.20/0.51  fof(f170,plain,(
% 0.20/0.51    v1_subset_1(sK1,sK1) | (~spl4_8 | ~spl4_13)),
% 0.20/0.51    inference(forward_demodulation,[],[f119,f157])).
% 0.20/0.51  fof(f157,plain,(
% 0.20/0.51    u1_struct_0(sK0) = sK1 | ~spl4_13),
% 0.20/0.51    inference(avatar_component_clause,[],[f155])).
% 0.20/0.51  fof(f155,plain,(
% 0.20/0.51    spl4_13 <=> u1_struct_0(sK0) = sK1),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.51  fof(f119,plain,(
% 0.20/0.51    v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl4_8),
% 0.20/0.51    inference(avatar_component_clause,[],[f118])).
% 0.20/0.51  fof(f118,plain,(
% 0.20/0.51    spl4_8 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.51  fof(f153,plain,(
% 0.20/0.51    spl4_12 | spl4_10 | ~spl4_11),
% 0.20/0.51    inference(avatar_split_clause,[],[f145,f138,f133,f150])).
% 0.20/0.51  fof(f133,plain,(
% 0.20/0.51    spl4_10 <=> v1_subset_1(sK1,k2_struct_0(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.51  fof(f145,plain,(
% 0.20/0.51    sK1 = k2_struct_0(sK0) | (spl4_10 | ~spl4_11)),
% 0.20/0.51    inference(subsumption_resolution,[],[f144,f135])).
% 0.20/0.51  fof(f135,plain,(
% 0.20/0.51    ~v1_subset_1(sK1,k2_struct_0(sK0)) | spl4_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f133])).
% 0.20/0.51  fof(f144,plain,(
% 0.20/0.51    sK1 = k2_struct_0(sK0) | v1_subset_1(sK1,k2_struct_0(sK0)) | ~spl4_11),
% 0.20/0.51    inference(resolution,[],[f74,f140])).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f46])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(nnf_transformation,[],[f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.20/0.51  fof(f141,plain,(
% 0.20/0.51    spl4_11 | ~spl4_5 | ~spl4_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f126,f108,f103,f138])).
% 0.20/0.51  fof(f103,plain,(
% 0.20/0.51    spl4_5 <=> l1_struct_0(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    spl4_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.51  fof(f126,plain,(
% 0.20/0.51    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl4_5 | ~spl4_6)),
% 0.20/0.51    inference(backward_demodulation,[],[f110,f124])).
% 0.20/0.51  fof(f124,plain,(
% 0.20/0.51    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl4_5),
% 0.20/0.51    inference(resolution,[],[f59,f105])).
% 0.20/0.51  fof(f105,plain,(
% 0.20/0.51    l1_struct_0(sK0) | ~spl4_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f103])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  % (5081)Refutation not found, incomplete strategy% (5081)------------------------------
% 0.20/0.51  % (5081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (5081)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (5081)Memory used [KB]: 1663
% 0.20/0.51  % (5081)Time elapsed: 0.072 s
% 0.20/0.51  % (5081)------------------------------
% 0.20/0.51  % (5081)------------------------------
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.51  fof(f110,plain,(
% 0.20/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f108])).
% 0.20/0.51  fof(f136,plain,(
% 0.20/0.51    ~spl4_10 | ~spl4_5 | spl4_8),
% 0.20/0.51    inference(avatar_split_clause,[],[f125,f118,f103,f133])).
% 0.20/0.51  fof(f125,plain,(
% 0.20/0.51    ~v1_subset_1(sK1,k2_struct_0(sK0)) | (~spl4_5 | spl4_8)),
% 0.20/0.51    inference(backward_demodulation,[],[f120,f124])).
% 0.20/0.51  fof(f120,plain,(
% 0.20/0.51    ~v1_subset_1(sK1,u1_struct_0(sK0)) | spl4_8),
% 0.20/0.51    inference(avatar_component_clause,[],[f118])).
% 0.20/0.51  fof(f131,plain,(
% 0.20/0.51    spl4_9 | ~spl4_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f124,f103,f128])).
% 0.20/0.51  fof(f123,plain,(
% 0.20/0.51    ~spl4_7 | spl4_8),
% 0.20/0.51    inference(avatar_split_clause,[],[f122,f118,f114])).
% 0.20/0.51  fof(f122,plain,(
% 0.20/0.51    ~v3_tex_2(sK1,sK0) | spl4_8),
% 0.20/0.51    inference(subsumption_resolution,[],[f55,f120])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ((v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)) & (~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((v1_subset_1(X1,u1_struct_0(sK0)) | ~v3_tex_2(X1,sK0)) & (~v1_subset_1(X1,u1_struct_0(sK0)) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ? [X1] : ((v1_subset_1(X1,u1_struct_0(sK0)) | ~v3_tex_2(X1,sK0)) & (~v1_subset_1(X1,u1_struct_0(sK0)) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)) & (~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,negated_conjecture,(
% 0.20/0.51    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.20/0.51    inference(negated_conjecture,[],[f15])).
% 0.20/0.51  fof(f15,conjecture,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).
% 0.20/0.51  fof(f121,plain,(
% 0.20/0.51    spl4_7 | ~spl4_8),
% 0.20/0.51    inference(avatar_split_clause,[],[f54,f118,f114])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    ~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f39])).
% 0.20/0.51  fof(f111,plain,(
% 0.20/0.51    spl4_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f53,f108])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    inference(cnf_transformation,[],[f39])).
% 0.20/0.51  fof(f106,plain,(
% 0.20/0.51    spl4_5 | ~spl4_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f101,f96,f103])).
% 0.20/0.51  fof(f101,plain,(
% 0.20/0.51    l1_struct_0(sK0) | ~spl4_4),
% 0.20/0.51    inference(resolution,[],[f60,f98])).
% 0.20/0.51  % (5075)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.51  fof(f99,plain,(
% 0.20/0.51    spl4_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f52,f96])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    l1_pre_topc(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f39])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    spl4_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f51,f91])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    v1_tdlat_3(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f39])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    spl4_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f50,f86])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    v2_pre_topc(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f39])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    ~spl4_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f49,f81])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ~v2_struct_0(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f39])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (5076)------------------------------
% 0.20/0.51  % (5076)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (5076)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (5076)Memory used [KB]: 6268
% 0.20/0.51  % (5076)Time elapsed: 0.095 s
% 0.20/0.51  % (5076)------------------------------
% 0.20/0.51  % (5076)------------------------------
% 0.20/0.51  % (5071)Success in time 0.154 s
%------------------------------------------------------------------------------
