%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 106 expanded)
%              Number of leaves         :   12 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :  201 ( 878 expanded)
%              Number of equality atoms :   14 (  92 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f127,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f73,f87,f101,f111,f126])).

fof(f126,plain,(
    ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | ~ spl4_10 ),
    inference(resolution,[],[f119,f23])).

fof(f23,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ! [X4] :
        ( sK3 != X4
        | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_pre_topc(sK1,sK2)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f6,f13,f12,f11,f10])).

fof(f10,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( X3 != X4
                    | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                & m1_subset_1(X3,u1_struct_0(X1)) )
            & m1_pre_topc(X1,X2)
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X2)) )
              & m1_subset_1(X3,u1_struct_0(sK1)) )
          & m1_pre_topc(sK1,X2)
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ! [X4] :
                ( X3 != X4
                | ~ m1_subset_1(X4,u1_struct_0(X2)) )
            & m1_subset_1(X3,u1_struct_0(sK1)) )
        & m1_pre_topc(sK1,X2)
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ! [X4] :
              ( X3 != X4
              | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
          & m1_subset_1(X3,u1_struct_0(sK1)) )
      & m1_pre_topc(sK1,sK2)
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X3] :
        ( ! [X4] :
            ( X3 != X4
            | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
        & m1_subset_1(X3,u1_struct_0(sK1)) )
   => ( ! [X4] :
          ( sK3 != X4
          | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
      & m1_subset_1(sK3,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( m1_pre_topc(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X1))
                     => ? [X4] :
                          ( X3 = X4
                          & m1_subset_1(X4,u1_struct_0(X2)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( m1_pre_topc(X1,X2)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ? [X4] :
                        ( X3 = X4
                        & m1_subset_1(X4,u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_tmap_1)).

fof(f119,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ spl4_10 ),
    inference(resolution,[],[f86,f27])).

fof(f27,plain,(
    ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X4] :
      ( sK3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f86,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl4_10
  <=> ! [X0] :
        ( m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f111,plain,(
    ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | ~ spl4_9 ),
    inference(resolution,[],[f83,f18])).

fof(f18,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f83,plain,
    ( v2_struct_0(sK1)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl4_9
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f101,plain,(
    ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | ~ spl4_8 ),
    inference(resolution,[],[f79,f20])).

fof(f20,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f79,plain,
    ( v2_struct_0(sK2)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl4_8
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f87,plain,
    ( spl4_8
    | ~ spl4_6
    | spl4_9
    | spl4_10 ),
    inference(avatar_split_clause,[],[f74,f85,f81,f58,f77])).

fof(f58,plain,
    ( spl4_6
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f74,plain,(
    ! [X0] :
      ( m1_subset_1(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f22,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f22,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f73,plain,
    ( ~ spl4_1
    | spl4_6 ),
    inference(avatar_split_clause,[],[f72,f58,f31])).

fof(f31,plain,
    ( spl4_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f72,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f21,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f21,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f69,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f67])).

fof(f67,plain,
    ( $false
    | spl4_1 ),
    inference(resolution,[],[f33,f17])).

fof(f17,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f33,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:05:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.43  % (19423)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.43  % (19423)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f127,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f69,f73,f87,f101,f111,f126])).
% 0.21/0.43  fof(f126,plain,(
% 0.21/0.43    ~spl4_10),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f124])).
% 0.21/0.43  fof(f124,plain,(
% 0.21/0.43    $false | ~spl4_10),
% 0.21/0.43    inference(resolution,[],[f119,f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    m1_subset_1(sK3,u1_struct_0(sK1))),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    (((! [X4] : (sK3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK1))) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f6,f13,f12,f11,f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(X3,u1_struct_0(sK1))) & m1_pre_topc(sK1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(X3,u1_struct_0(sK1))) & m1_pre_topc(sK1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2))) & m1_subset_1(X3,u1_struct_0(sK1))) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2))) & m1_subset_1(X3,u1_struct_0(sK1))) => (! [X4] : (sK3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK1)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f6,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.43    inference(flattening,[],[f5])).
% 0.21/0.43  fof(f5,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_pre_topc(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,negated_conjecture,(
% 0.21/0.43    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))))))))),
% 0.21/0.43    inference(negated_conjecture,[],[f3])).
% 0.21/0.43  fof(f3,conjecture,(
% 0.21/0.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))))))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_tmap_1)).
% 0.21/0.43  fof(f119,plain,(
% 0.21/0.43    ~m1_subset_1(sK3,u1_struct_0(sK1)) | ~spl4_10),
% 0.21/0.43    inference(resolution,[],[f86,f27])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ~m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.21/0.43    inference(equality_resolution,[],[f24])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ( ! [X4] : (sK3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK2))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f86,plain,(
% 0.21/0.43    ( ! [X0] : (m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK1))) ) | ~spl4_10),
% 0.21/0.43    inference(avatar_component_clause,[],[f85])).
% 0.21/0.43  fof(f85,plain,(
% 0.21/0.43    spl4_10 <=> ! [X0] : (m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK1)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.43  fof(f111,plain,(
% 0.21/0.43    ~spl4_9),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f110])).
% 0.21/0.43  fof(f110,plain,(
% 0.21/0.43    $false | ~spl4_9),
% 0.21/0.43    inference(resolution,[],[f83,f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ~v2_struct_0(sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f83,plain,(
% 0.21/0.43    v2_struct_0(sK1) | ~spl4_9),
% 0.21/0.43    inference(avatar_component_clause,[],[f81])).
% 0.21/0.43  fof(f81,plain,(
% 0.21/0.43    spl4_9 <=> v2_struct_0(sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.43  fof(f101,plain,(
% 0.21/0.43    ~spl4_8),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f100])).
% 0.21/0.43  fof(f100,plain,(
% 0.21/0.43    $false | ~spl4_8),
% 0.21/0.43    inference(resolution,[],[f79,f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ~v2_struct_0(sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f79,plain,(
% 0.21/0.43    v2_struct_0(sK2) | ~spl4_8),
% 0.21/0.43    inference(avatar_component_clause,[],[f77])).
% 0.21/0.43  fof(f77,plain,(
% 0.21/0.43    spl4_8 <=> v2_struct_0(sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.43  fof(f87,plain,(
% 0.21/0.43    spl4_8 | ~spl4_6 | spl4_9 | spl4_10),
% 0.21/0.43    inference(avatar_split_clause,[],[f74,f85,f81,f58,f77])).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    spl4_6 <=> l1_pre_topc(sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.43  fof(f74,plain,(
% 0.21/0.43    ( ! [X0] : (m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.43    inference(resolution,[],[f22,f26])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.43    inference(flattening,[],[f8])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    m1_pre_topc(sK1,sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f73,plain,(
% 0.21/0.43    ~spl4_1 | spl4_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f72,f58,f31])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    spl4_1 <=> l1_pre_topc(sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.43  fof(f72,plain,(
% 0.21/0.43    l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 0.21/0.43    inference(resolution,[],[f21,f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    m1_pre_topc(sK2,sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f69,plain,(
% 0.21/0.43    spl4_1),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f67])).
% 0.21/0.43  fof(f67,plain,(
% 0.21/0.43    $false | spl4_1),
% 0.21/0.43    inference(resolution,[],[f33,f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    l1_pre_topc(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    ~l1_pre_topc(sK0) | spl4_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f31])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (19423)------------------------------
% 0.21/0.43  % (19423)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (19423)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (19423)Memory used [KB]: 6140
% 0.21/0.43  % (19423)Time elapsed: 0.006 s
% 0.21/0.43  % (19423)------------------------------
% 0.21/0.43  % (19423)------------------------------
% 0.21/0.43  % (19410)Success in time 0.068 s
%------------------------------------------------------------------------------
