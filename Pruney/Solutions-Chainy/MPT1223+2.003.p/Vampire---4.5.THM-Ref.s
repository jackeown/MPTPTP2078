%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:51 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 128 expanded)
%              Number of leaves         :   17 (  57 expanded)
%              Depth                    :    8
%              Number of atoms          :  251 ( 616 expanded)
%              Number of equality atoms :   16 (  21 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f89,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f38,f43,f48,f53,f61,f65,f70,f77,f82,f88])).

fof(f88,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f87])).

fof(f87,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f86,f27])).

fof(f27,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK2),sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl3_1
  <=> r1_tarski(k2_pre_topc(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f86,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK2),sK1)
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f85,f76])).

fof(f76,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl3_11
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f85,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f84,f42])).

fof(f42,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f84,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f83,f47])).

fof(f47,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl3_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f83,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(resolution,[],[f81,f32])).

fof(f32,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl3_2
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f81,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1)) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f82,plain,
    ( spl3_12
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f78,f63,f50,f80])).

fof(f50,plain,
    ( spl3_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f63,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
        | ~ r1_tarski(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1)) )
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(resolution,[],[f64,f52])).

fof(f52,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f50])).

fof(f64,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ r1_tarski(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f63])).

fof(f77,plain,
    ( spl3_11
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f72,f68,f45,f35,f74])).

fof(f35,plain,
    ( spl3_3
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f68,plain,
    ( spl3_10
  <=> ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f72,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f71,f47])).

fof(f71,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(resolution,[],[f69,f37])).

fof(f37,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f69,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0 )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f68])).

fof(f70,plain,
    ( spl3_10
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f66,f59,f50,f68])).

fof(f59,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,X1) = X1
        | ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f66,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0 )
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(resolution,[],[f60,f52])).

fof(f60,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_pre_topc(X0,X1) = X1 )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f59])).

fof(f65,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f23,f63])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).

fof(f61,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f21,f59])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f53,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f15,f50])).

fof(f15,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK2),sK1)
    & r1_tarski(sK2,sK1)
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f13,f12,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k2_pre_topc(X0,X2),X1)
                & r1_tarski(X2,X1)
                & v4_pre_topc(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(sK0,X2),X1)
              & r1_tarski(X2,X1)
              & v4_pre_topc(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k2_pre_topc(sK0,X2),X1)
            & r1_tarski(X2,X1)
            & v4_pre_topc(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k2_pre_topc(sK0,X2),sK1)
          & r1_tarski(X2,sK1)
          & v4_pre_topc(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k2_pre_topc(sK0,X2),sK1)
        & r1_tarski(X2,sK1)
        & v4_pre_topc(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k2_pre_topc(sK0,sK2),sK1)
      & r1_tarski(sK2,sK1)
      & v4_pre_topc(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(X0,X2),X1)
              & r1_tarski(X2,X1)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(X0,X2),X1)
              & r1_tarski(X2,X1)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r1_tarski(X2,X1)
                    & v4_pre_topc(X1,X0) )
                 => r1_tarski(k2_pre_topc(X0,X2),X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X2,X1)
                  & v4_pre_topc(X1,X0) )
               => r1_tarski(k2_pre_topc(X0,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_1)).

fof(f48,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f16,f45])).

fof(f16,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f43,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f17,f40])).

fof(f17,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f38,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f18,f35])).

fof(f18,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f33,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f19,f30])).

fof(f19,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f28,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f20,f25])).

fof(f20,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n010.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 14:51:29 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.19/0.38  % (16222)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.19/0.38  % (16218)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.19/0.39  % (16223)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.19/0.40  % (16223)Refutation found. Thanks to Tanya!
% 0.19/0.40  % SZS status Theorem for theBenchmark
% 0.19/0.40  % SZS output start Proof for theBenchmark
% 0.19/0.40  fof(f89,plain,(
% 0.19/0.40    $false),
% 0.19/0.40    inference(avatar_sat_refutation,[],[f28,f33,f38,f43,f48,f53,f61,f65,f70,f77,f82,f88])).
% 0.19/0.40  fof(f88,plain,(
% 0.19/0.40    spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_11 | ~spl3_12),
% 0.19/0.40    inference(avatar_contradiction_clause,[],[f87])).
% 0.19/0.40  fof(f87,plain,(
% 0.19/0.40    $false | (spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_11 | ~spl3_12)),
% 0.19/0.40    inference(subsumption_resolution,[],[f86,f27])).
% 0.19/0.40  fof(f27,plain,(
% 0.19/0.40    ~r1_tarski(k2_pre_topc(sK0,sK2),sK1) | spl3_1),
% 0.19/0.40    inference(avatar_component_clause,[],[f25])).
% 0.19/0.40  fof(f25,plain,(
% 0.19/0.40    spl3_1 <=> r1_tarski(k2_pre_topc(sK0,sK2),sK1)),
% 0.19/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.40  fof(f86,plain,(
% 0.19/0.40    r1_tarski(k2_pre_topc(sK0,sK2),sK1) | (~spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_11 | ~spl3_12)),
% 0.19/0.40    inference(forward_demodulation,[],[f85,f76])).
% 0.19/0.40  fof(f76,plain,(
% 0.19/0.40    sK1 = k2_pre_topc(sK0,sK1) | ~spl3_11),
% 0.19/0.40    inference(avatar_component_clause,[],[f74])).
% 0.19/0.40  fof(f74,plain,(
% 0.19/0.40    spl3_11 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.19/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.19/0.40  fof(f85,plain,(
% 0.19/0.40    r1_tarski(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1)) | (~spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_12)),
% 0.19/0.40    inference(subsumption_resolution,[],[f84,f42])).
% 0.19/0.40  fof(f42,plain,(
% 0.19/0.40    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_4),
% 0.19/0.40    inference(avatar_component_clause,[],[f40])).
% 0.19/0.40  fof(f40,plain,(
% 0.19/0.40    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.19/0.40  fof(f84,plain,(
% 0.19/0.40    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1)) | (~spl3_2 | ~spl3_5 | ~spl3_12)),
% 0.19/0.40    inference(subsumption_resolution,[],[f83,f47])).
% 0.19/0.40  fof(f47,plain,(
% 0.19/0.40    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 0.19/0.40    inference(avatar_component_clause,[],[f45])).
% 0.19/0.40  fof(f45,plain,(
% 0.19/0.40    spl3_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.19/0.40  fof(f83,plain,(
% 0.19/0.40    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1)) | (~spl3_2 | ~spl3_12)),
% 0.19/0.40    inference(resolution,[],[f81,f32])).
% 0.19/0.40  fof(f32,plain,(
% 0.19/0.40    r1_tarski(sK2,sK1) | ~spl3_2),
% 0.19/0.40    inference(avatar_component_clause,[],[f30])).
% 0.19/0.40  fof(f30,plain,(
% 0.19/0.40    spl3_2 <=> r1_tarski(sK2,sK1)),
% 0.19/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.40  fof(f81,plain,(
% 0.19/0.40    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1))) ) | ~spl3_12),
% 0.19/0.40    inference(avatar_component_clause,[],[f80])).
% 0.19/0.40  fof(f80,plain,(
% 0.19/0.40    spl3_12 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1)))),
% 0.19/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.19/0.40  fof(f82,plain,(
% 0.19/0.40    spl3_12 | ~spl3_6 | ~spl3_9),
% 0.19/0.40    inference(avatar_split_clause,[],[f78,f63,f50,f80])).
% 0.19/0.40  fof(f50,plain,(
% 0.19/0.40    spl3_6 <=> l1_pre_topc(sK0)),
% 0.19/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.19/0.40  fof(f63,plain,(
% 0.19/0.40    spl3_9 <=> ! [X1,X0,X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.19/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.19/0.40  fof(f78,plain,(
% 0.19/0.40    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1))) ) | (~spl3_6 | ~spl3_9)),
% 0.19/0.40    inference(resolution,[],[f64,f52])).
% 0.19/0.40  fof(f52,plain,(
% 0.19/0.40    l1_pre_topc(sK0) | ~spl3_6),
% 0.19/0.40    inference(avatar_component_clause,[],[f50])).
% 0.19/0.40  fof(f64,plain,(
% 0.19/0.40    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) | ~spl3_9),
% 0.19/0.40    inference(avatar_component_clause,[],[f63])).
% 0.19/0.40  fof(f77,plain,(
% 0.19/0.40    spl3_11 | ~spl3_3 | ~spl3_5 | ~spl3_10),
% 0.19/0.40    inference(avatar_split_clause,[],[f72,f68,f45,f35,f74])).
% 0.19/0.40  fof(f35,plain,(
% 0.19/0.40    spl3_3 <=> v4_pre_topc(sK1,sK0)),
% 0.19/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.19/0.40  fof(f68,plain,(
% 0.19/0.40    spl3_10 <=> ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0)),
% 0.19/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.19/0.40  fof(f72,plain,(
% 0.19/0.40    sK1 = k2_pre_topc(sK0,sK1) | (~spl3_3 | ~spl3_5 | ~spl3_10)),
% 0.19/0.40    inference(subsumption_resolution,[],[f71,f47])).
% 0.19/0.40  fof(f71,plain,(
% 0.19/0.40    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k2_pre_topc(sK0,sK1) | (~spl3_3 | ~spl3_10)),
% 0.19/0.40    inference(resolution,[],[f69,f37])).
% 0.19/0.40  fof(f37,plain,(
% 0.19/0.40    v4_pre_topc(sK1,sK0) | ~spl3_3),
% 0.19/0.40    inference(avatar_component_clause,[],[f35])).
% 0.19/0.40  fof(f69,plain,(
% 0.19/0.40    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0) ) | ~spl3_10),
% 0.19/0.40    inference(avatar_component_clause,[],[f68])).
% 0.19/0.40  fof(f70,plain,(
% 0.19/0.40    spl3_10 | ~spl3_6 | ~spl3_8),
% 0.19/0.40    inference(avatar_split_clause,[],[f66,f59,f50,f68])).
% 0.19/0.40  fof(f59,plain,(
% 0.19/0.40    spl3_8 <=> ! [X1,X0] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.19/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.19/0.40  fof(f66,plain,(
% 0.19/0.40    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0) ) | (~spl3_6 | ~spl3_8)),
% 0.19/0.40    inference(resolution,[],[f60,f52])).
% 0.19/0.40  fof(f60,plain,(
% 0.19/0.40    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = X1) ) | ~spl3_8),
% 0.19/0.40    inference(avatar_component_clause,[],[f59])).
% 0.19/0.40  fof(f65,plain,(
% 0.19/0.40    spl3_9),
% 0.19/0.40    inference(avatar_split_clause,[],[f23,f63])).
% 0.19/0.40  fof(f23,plain,(
% 0.19/0.40    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.19/0.40    inference(cnf_transformation,[],[f10])).
% 0.19/0.40  fof(f10,plain,(
% 0.19/0.40    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.40    inference(flattening,[],[f9])).
% 0.19/0.40  fof(f9,plain,(
% 0.19/0.40    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.40    inference(ennf_transformation,[],[f1])).
% 0.19/0.40  fof(f1,axiom,(
% 0.19/0.40    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).
% 0.19/0.40  fof(f61,plain,(
% 0.19/0.40    spl3_8),
% 0.19/0.40    inference(avatar_split_clause,[],[f21,f59])).
% 0.19/0.40  fof(f21,plain,(
% 0.19/0.40    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.19/0.40    inference(cnf_transformation,[],[f8])).
% 0.19/0.40  fof(f8,plain,(
% 0.19/0.40    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.40    inference(flattening,[],[f7])).
% 0.19/0.40  fof(f7,plain,(
% 0.19/0.40    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.40    inference(ennf_transformation,[],[f2])).
% 0.19/0.40  fof(f2,axiom,(
% 0.19/0.40    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.19/0.40  fof(f53,plain,(
% 0.19/0.40    spl3_6),
% 0.19/0.40    inference(avatar_split_clause,[],[f15,f50])).
% 0.19/0.40  fof(f15,plain,(
% 0.19/0.40    l1_pre_topc(sK0)),
% 0.19/0.40    inference(cnf_transformation,[],[f14])).
% 0.19/0.40  fof(f14,plain,(
% 0.19/0.40    ((~r1_tarski(k2_pre_topc(sK0,sK2),sK1) & r1_tarski(sK2,sK1) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.19/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f13,f12,f11])).
% 0.19/0.40  fof(f11,plain,(
% 0.19/0.40    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,X2),X1) & r1_tarski(X2,X1) & v4_pre_topc(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(sK0,X2),X1) & r1_tarski(X2,X1) & v4_pre_topc(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.19/0.40    introduced(choice_axiom,[])).
% 0.19/0.40  fof(f12,plain,(
% 0.19/0.40    ? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(sK0,X2),X1) & r1_tarski(X2,X1) & v4_pre_topc(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~r1_tarski(k2_pre_topc(sK0,X2),sK1) & r1_tarski(X2,sK1) & v4_pre_topc(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.40    introduced(choice_axiom,[])).
% 0.19/0.40  fof(f13,plain,(
% 0.19/0.40    ? [X2] : (~r1_tarski(k2_pre_topc(sK0,X2),sK1) & r1_tarski(X2,sK1) & v4_pre_topc(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k2_pre_topc(sK0,sK2),sK1) & r1_tarski(sK2,sK1) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.40    introduced(choice_axiom,[])).
% 0.19/0.40  fof(f6,plain,(
% 0.19/0.40    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,X2),X1) & r1_tarski(X2,X1) & v4_pre_topc(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.19/0.40    inference(flattening,[],[f5])).
% 0.19/0.40  fof(f5,plain,(
% 0.19/0.40    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k2_pre_topc(X0,X2),X1) & (r1_tarski(X2,X1) & v4_pre_topc(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.19/0.40    inference(ennf_transformation,[],[f4])).
% 0.19/0.40  fof(f4,negated_conjecture,(
% 0.19/0.40    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X2,X1) & v4_pre_topc(X1,X0)) => r1_tarski(k2_pre_topc(X0,X2),X1)))))),
% 0.19/0.40    inference(negated_conjecture,[],[f3])).
% 0.19/0.40  fof(f3,conjecture,(
% 0.19/0.40    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X2,X1) & v4_pre_topc(X1,X0)) => r1_tarski(k2_pre_topc(X0,X2),X1)))))),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_1)).
% 0.19/0.40  fof(f48,plain,(
% 0.19/0.40    spl3_5),
% 0.19/0.40    inference(avatar_split_clause,[],[f16,f45])).
% 0.19/0.40  fof(f16,plain,(
% 0.19/0.40    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.40    inference(cnf_transformation,[],[f14])).
% 0.19/0.40  fof(f43,plain,(
% 0.19/0.40    spl3_4),
% 0.19/0.40    inference(avatar_split_clause,[],[f17,f40])).
% 0.19/0.40  fof(f17,plain,(
% 0.19/0.40    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.40    inference(cnf_transformation,[],[f14])).
% 0.19/0.40  fof(f38,plain,(
% 0.19/0.40    spl3_3),
% 0.19/0.40    inference(avatar_split_clause,[],[f18,f35])).
% 0.19/0.40  fof(f18,plain,(
% 0.19/0.40    v4_pre_topc(sK1,sK0)),
% 0.19/0.40    inference(cnf_transformation,[],[f14])).
% 0.19/0.40  fof(f33,plain,(
% 0.19/0.40    spl3_2),
% 0.19/0.40    inference(avatar_split_clause,[],[f19,f30])).
% 0.19/0.40  fof(f19,plain,(
% 0.19/0.40    r1_tarski(sK2,sK1)),
% 0.19/0.40    inference(cnf_transformation,[],[f14])).
% 0.19/0.40  fof(f28,plain,(
% 0.19/0.40    ~spl3_1),
% 0.19/0.40    inference(avatar_split_clause,[],[f20,f25])).
% 0.19/0.40  fof(f20,plain,(
% 0.19/0.40    ~r1_tarski(k2_pre_topc(sK0,sK2),sK1)),
% 0.19/0.40    inference(cnf_transformation,[],[f14])).
% 0.19/0.40  % SZS output end Proof for theBenchmark
% 0.19/0.40  % (16223)------------------------------
% 0.19/0.40  % (16223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.40  % (16223)Termination reason: Refutation
% 0.19/0.40  
% 0.19/0.40  % (16223)Memory used [KB]: 10618
% 0.19/0.40  % (16223)Time elapsed: 0.006 s
% 0.19/0.40  % (16223)------------------------------
% 0.19/0.40  % (16223)------------------------------
% 0.19/0.40  % (16217)Success in time 0.063 s
%------------------------------------------------------------------------------
