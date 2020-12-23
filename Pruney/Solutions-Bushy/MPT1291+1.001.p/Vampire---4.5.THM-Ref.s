%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1291+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:39 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 132 expanded)
%              Number of leaves         :   21 (  64 expanded)
%              Depth                    :    7
%              Number of atoms          :  222 ( 446 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f114,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f44,f48,f52,f56,f60,f66,f71,f82,f87,f93,f99,f106,f113])).

fof(f113,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f111,f104,f36,f31])).

fof(f31,plain,
    ( spl4_2
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f36,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f104,plain,
    ( spl4_16
  <=> ! [X2] :
        ( ~ r1_tarski(sK2,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f111,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ spl4_3
    | ~ spl4_16 ),
    inference(resolution,[],[f105,f38])).

fof(f38,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f105,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(sK2,X2) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f104])).

fof(f106,plain,
    ( spl4_16
    | ~ spl4_5
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f101,f97,f46,f104])).

fof(f46,plain,
    ( spl4_5
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f97,plain,
    ( spl4_15
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f101,plain,
    ( ! [X2] :
        ( ~ r1_tarski(sK2,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl4_5
    | ~ spl4_15 ),
    inference(resolution,[],[f98,f47])).

fof(f47,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f46])).

fof(f98,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK2,X0) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f97])).

fof(f99,plain,
    ( spl4_9
    | spl4_15
    | ~ spl4_7
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f94,f91,f54,f97,f63])).

fof(f63,plain,
    ( spl4_9
  <=> r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f54,plain,
    ( spl4_7
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | r2_hidden(sK3(X0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f91,plain,
    ( spl4_14
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK3(sK2,k1_zfmisc_1(u1_struct_0(sK0))),X1)
        | ~ r1_tarski(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f94,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK2,X0)
        | r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_7
    | ~ spl4_14 ),
    inference(resolution,[],[f92,f55])).

% (26160)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
fof(f55,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,X1),X0)
        | r1_tarski(X0,X1) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f54])).

fof(f92,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK3(sK2,k1_zfmisc_1(u1_struct_0(sK0))),X1)
        | ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X1,X0) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f91])).

fof(f93,plain,
    ( spl4_14
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f89,f85,f69,f91])).

fof(f69,plain,
    ( spl4_10
  <=> ! [X1,X3,X0] :
        ( r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f85,plain,
    ( spl4_13
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK3(sK2,k1_zfmisc_1(u1_struct_0(sK0))),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK3(sK2,k1_zfmisc_1(u1_struct_0(sK0))),X1)
        | ~ r1_tarski(X1,X0) )
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(resolution,[],[f86,f70])).

fof(f70,plain,
    ( ! [X0,X3,X1] :
        ( r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f69])).

fof(f86,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK2,k1_zfmisc_1(u1_struct_0(sK0))),X0)
        | ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f85])).

fof(f87,plain,
    ( spl4_13
    | spl4_9
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f83,f80,f63,f85])).

fof(f80,plain,
    ( spl4_12
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(sK3(X0,X1),X2)
        | ~ r1_tarski(X2,X1)
        | r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f83,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK3(sK2,k1_zfmisc_1(u1_struct_0(sK0))),X0) )
    | spl4_9
    | ~ spl4_12 ),
    inference(resolution,[],[f81,f65])).

fof(f65,plain,
    ( ~ r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f63])).

fof(f81,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,X1)
        | ~ r1_tarski(X2,X1)
        | ~ r2_hidden(sK3(X0,X1),X2) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f80])).

fof(f82,plain,
    ( spl4_12
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f78,f69,f58,f80])).

fof(f58,plain,
    ( spl4_8
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f78,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK3(X0,X1),X2)
        | ~ r1_tarski(X2,X1)
        | r1_tarski(X0,X1) )
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(resolution,[],[f70,f59])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK3(X0,X1),X1)
        | r1_tarski(X0,X1) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f58])).

fof(f71,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f20,f69])).

fof(f20,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f13])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f66,plain,
    ( ~ spl4_9
    | spl4_4
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f61,f50,f41,f63])).

fof(f41,plain,
    ( spl4_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f50,plain,
    ( spl4_6
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f61,plain,
    ( ~ r1_tarski(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_4
    | ~ spl4_6 ),
    inference(resolution,[],[f51,f43])).

fof(f43,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f51,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f50])).

fof(f60,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f22,f58])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f56,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f21,f54])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f52,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f24,f50])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f48,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f23,f46])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f44,plain,(
    ~ spl4_4 ),
    inference(avatar_split_clause,[],[f19,f41])).

fof(f19,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & r1_tarski(sK2,sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f9,f8,f7])).

fof(f7,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                & r1_tarski(X2,X1) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
              & r1_tarski(X2,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
            & r1_tarski(X2,X1) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ? [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
          & r1_tarski(X2,sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,
    ( ? [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        & r1_tarski(X2,sK1) )
   => ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      & r1_tarski(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & r1_tarski(X2,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( r1_tarski(X2,X1)
               => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( r1_tarski(X2,X1)
             => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_tops_2)).

fof(f39,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f17,f36])).

fof(f17,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f10])).

fof(f34,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f18,f31])).

fof(f18,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f10])).

%------------------------------------------------------------------------------
