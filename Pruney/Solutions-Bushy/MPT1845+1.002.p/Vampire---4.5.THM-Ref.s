%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1845+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:44 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 554 expanded)
%              Number of leaves         :   29 ( 202 expanded)
%              Depth                    :   13
%              Number of atoms          :  550 (2609 expanded)
%              Number of equality atoms :   30 ( 436 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f457,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f82,f98,f228,f233,f238,f297,f302,f318,f327,f332,f337,f345,f362,f365,f428,f439,f456])).

fof(f456,plain,
    ( ~ spl8_23
    | ~ spl8_18
    | ~ spl8_17
    | ~ spl8_22
    | ~ spl8_2
    | ~ spl8_3
    | spl8_16 ),
    inference(avatar_split_clause,[],[f452,f225,f87,f77,f294,f230,f235,f299])).

fof(f299,plain,
    ( spl8_23
  <=> r2_hidden(sK7(sK4),u1_pre_topc(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f235,plain,
    ( spl8_18
  <=> m1_subset_1(sK6(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f230,plain,
    ( spl8_17
  <=> m1_subset_1(sK7(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f294,plain,
    ( spl8_22
  <=> r2_hidden(sK6(sK4),u1_pre_topc(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f77,plain,
    ( spl8_2
  <=> sP1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f87,plain,
    ( spl8_3
  <=> m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f225,plain,
    ( spl8_16
  <=> r2_hidden(k9_subset_1(u1_struct_0(sK3),sK6(sK4),sK7(sK4)),u1_pre_topc(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f452,plain,
    ( ~ r2_hidden(sK6(sK4),u1_pre_topc(sK3))
    | ~ m1_subset_1(sK7(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(sK7(sK4),u1_pre_topc(sK3))
    | ~ spl8_2
    | ~ spl8_3
    | spl8_16 ),
    inference(resolution,[],[f367,f281])).

fof(f281,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK3),sK6(sK4),sK7(sK4)),u1_pre_topc(sK3))
    | ~ spl8_3
    | spl8_16 ),
    inference(backward_demodulation,[],[f227,f276])).

fof(f276,plain,
    ( u1_pre_topc(sK3) = u1_pre_topc(sK4)
    | ~ spl8_3 ),
    inference(equality_resolution,[],[f196])).

fof(f196,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
        | u1_pre_topc(sK4) = X1 )
    | ~ spl8_3 ),
    inference(superposition,[],[f176,f43])).

fof(f43,plain,(
    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ v2_pre_topc(sK4)
    & v2_pre_topc(sK3)
    & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    & l1_pre_topc(sK4)
    & l1_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f12,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_pre_topc(X1)
            & v2_pre_topc(X0)
            & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v2_pre_topc(X1)
          & v2_pre_topc(sK3)
          & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ~ v2_pre_topc(X1)
        & v2_pre_topc(sK3)
        & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
        & l1_pre_topc(X1) )
   => ( ~ v2_pre_topc(sK4)
      & v2_pre_topc(sK3)
      & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
      & l1_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_pre_topc(X1)
          & v2_pre_topc(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_pre_topc(X1)
          & v2_pre_topc(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v2_pre_topc(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v2_pre_topc(X1) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v2_pre_topc(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v2_pre_topc(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tex_2)).

fof(f176,plain,
    ( ! [X4,X3] :
        ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(X3,X4)
        | u1_pre_topc(sK4) = X4 )
    | ~ spl8_3 ),
    inference(resolution,[],[f68,f88])).

fof(f88,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f227,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK3),sK6(sK4),sK7(sK4)),u1_pre_topc(sK4))
    | spl8_16 ),
    inference(avatar_component_clause,[],[f225])).

fof(f367,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k9_subset_1(u1_struct_0(sK3),X1,X0),u1_pre_topc(sK3))
        | ~ r2_hidden(X1,u1_pre_topc(sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ r2_hidden(X0,u1_pre_topc(sK3)) )
    | ~ spl8_2 ),
    inference(resolution,[],[f56,f84])).

fof(f84,plain,
    ( sP0(sK3)
    | ~ spl8_2 ),
    inference(resolution,[],[f79,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( sP1(X0)
        | ~ sP0(X0)
        | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK5(X0)),u1_pre_topc(X0))
          & r1_tarski(sK5(X0),u1_pre_topc(X0))
          & m1_subset_1(sK5(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( sP0(X0)
          & ! [X2] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
              | ~ r1_tarski(X2,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK5(X0)),u1_pre_topc(X0))
        & r1_tarski(sK5(X0),u1_pre_topc(X0))
        & m1_subset_1(sK5(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( sP1(X0)
        | ~ sP0(X0)
        | ? [X1] :
            ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
            & r1_tarski(X1,u1_pre_topc(X0))
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( sP0(X0)
          & ! [X2] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
              | ~ r1_tarski(X2,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP1(X0) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( sP1(X0)
        | ~ sP0(X0)
        | ? [X3] :
            ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            & r1_tarski(X3,u1_pre_topc(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP1(X0) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( sP1(X0)
        | ~ sP0(X0)
        | ? [X3] :
            ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            & r1_tarski(X3,u1_pre_topc(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP1(X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( sP1(X0)
    <=> ( sP0(X0)
        & ! [X3] :
            ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            | ~ r1_tarski(X3,u1_pre_topc(X0))
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f79,plain,
    ( sP1(sK3)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f56,plain,(
    ! [X4,X0,X3] :
      ( ~ sP0(X0)
      | ~ r2_hidden(X4,u1_pre_topc(X0))
      | ~ r2_hidden(X3,u1_pre_topc(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(k9_subset_1(u1_struct_0(X0),X3,X4),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK6(X0),sK7(X0)),u1_pre_topc(X0))
          & r2_hidden(sK7(X0),u1_pre_topc(X0))
          & r2_hidden(sK6(X0),u1_pre_topc(X0))
          & m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0)))
          & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( ! [X4] :
                ( r2_hidden(k9_subset_1(u1_struct_0(X0),X3,X4),u1_pre_topc(X0))
                | ~ r2_hidden(X4,u1_pre_topc(X0))
                | ~ r2_hidden(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f37,f39,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              & r2_hidden(X2,u1_pre_topc(X0))
              & r2_hidden(X1,u1_pre_topc(X0))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK6(X0),X2),u1_pre_topc(X0))
            & r2_hidden(X2,u1_pre_topc(X0))
            & r2_hidden(sK6(X0),u1_pre_topc(X0))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK6(X0),X2),u1_pre_topc(X0))
          & r2_hidden(X2,u1_pre_topc(X0))
          & r2_hidden(sK6(X0),u1_pre_topc(X0))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK6(X0),sK7(X0)),u1_pre_topc(X0))
        & r2_hidden(sK7(X0),u1_pre_topc(X0))
        & r2_hidden(sK6(X0),u1_pre_topc(X0))
        & m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                & r2_hidden(X2,u1_pre_topc(X0))
                & r2_hidden(X1,u1_pre_topc(X0))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( ! [X4] :
                ( r2_hidden(k9_subset_1(u1_struct_0(X0),X3,X4),u1_pre_topc(X0))
                | ~ r2_hidden(X4,u1_pre_topc(X0))
                | ~ r2_hidden(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                & r2_hidden(X2,u1_pre_topc(X0))
                & r2_hidden(X1,u1_pre_topc(X0))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X1] :
            ( ! [X2] :
                ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                | ~ r2_hidden(X2,u1_pre_topc(X0))
                | ~ r2_hidden(X1,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              | ~ r2_hidden(X2,u1_pre_topc(X0))
              | ~ r2_hidden(X1,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f439,plain,(
    ~ spl8_29 ),
    inference(avatar_contradiction_clause,[],[f436])).

fof(f436,plain,
    ( $false
    | ~ spl8_29 ),
    inference(resolution,[],[f361,f45])).

fof(f45,plain,(
    ~ v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f29])).

fof(f361,plain,
    ( v2_pre_topc(sK4)
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f359])).

fof(f359,plain,
    ( spl8_29
  <=> v2_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f428,plain,
    ( ~ spl8_27
    | ~ spl8_24
    | ~ spl8_2
    | spl8_26 ),
    inference(avatar_split_clause,[],[f427,f329,f77,f320,f334])).

fof(f334,plain,
    ( spl8_27
  <=> r1_tarski(sK5(sK4),u1_pre_topc(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f320,plain,
    ( spl8_24
  <=> m1_subset_1(sK5(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f329,plain,
    ( spl8_26
  <=> r2_hidden(k5_setfam_1(u1_struct_0(sK3),sK5(sK4)),u1_pre_topc(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f427,plain,
    ( ~ m1_subset_1(sK5(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ r1_tarski(sK5(sK4),u1_pre_topc(sK3))
    | ~ spl8_2
    | spl8_26 ),
    inference(resolution,[],[f339,f331])).

fof(f331,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK3),sK5(sK4)),u1_pre_topc(sK3))
    | spl8_26 ),
    inference(avatar_component_clause,[],[f329])).

fof(f339,plain,
    ( ! [X0] :
        ( r2_hidden(k5_setfam_1(u1_struct_0(sK3),X0),u1_pre_topc(sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
        | ~ r1_tarski(X0,u1_pre_topc(sK3)) )
    | ~ spl8_2 ),
    inference(resolution,[],[f51,f79])).

fof(f51,plain,(
    ! [X2,X0] :
      ( ~ sP1(X0)
      | ~ r1_tarski(X2,u1_pre_topc(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f365,plain,(
    spl8_28 ),
    inference(avatar_contradiction_clause,[],[f364])).

fof(f364,plain,
    ( $false
    | spl8_28 ),
    inference(resolution,[],[f363,f42])).

fof(f42,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f29])).

fof(f363,plain,
    ( ~ l1_pre_topc(sK4)
    | spl8_28 ),
    inference(resolution,[],[f357,f62])).

fof(f62,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f17,f25,f24,f23])).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> sP1(X0) )
      | ~ sP2(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
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
    inference(rectify,[],[f2])).

fof(f2,axiom,(
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

fof(f357,plain,
    ( ~ sP2(sK4)
    | spl8_28 ),
    inference(avatar_component_clause,[],[f355])).

fof(f355,plain,
    ( spl8_28
  <=> sP2(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f362,plain,
    ( ~ spl8_28
    | spl8_29
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f348,f240,f359,f355])).

fof(f240,plain,
    ( spl8_19
  <=> sP1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f348,plain,
    ( v2_pre_topc(sK4)
    | ~ sP2(sK4)
    | ~ spl8_19 ),
    inference(resolution,[],[f241,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | v2_pre_topc(X0)
      | ~ sP2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP1(X0) )
        & ( sP1(X0)
          | ~ v2_pre_topc(X0) ) )
      | ~ sP2(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f241,plain,
    ( sP1(sK4)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f240])).

fof(f345,plain,
    ( ~ spl8_3
    | ~ spl8_20
    | spl8_25 ),
    inference(avatar_contradiction_clause,[],[f343])).

fof(f343,plain,
    ( $false
    | ~ spl8_3
    | ~ spl8_20
    | spl8_25 ),
    inference(resolution,[],[f326,f338])).

fof(f338,plain,
    ( r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK3))
    | ~ spl8_3
    | ~ spl8_20 ),
    inference(forward_demodulation,[],[f246,f276])).

fof(f246,plain,
    ( r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4))
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl8_20
  <=> r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f326,plain,
    ( ~ r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK3))
    | spl8_25 ),
    inference(avatar_component_clause,[],[f324])).

fof(f324,plain,
    ( spl8_25
  <=> r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f337,plain,
    ( spl8_19
    | ~ spl8_15
    | spl8_27
    | ~ spl8_25
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f304,f87,f324,f334,f221,f240])).

fof(f221,plain,
    ( spl8_15
  <=> sP0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f304,plain,
    ( ~ r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK3))
    | r1_tarski(sK5(sK4),u1_pre_topc(sK3))
    | ~ sP0(sK4)
    | sP1(sK4)
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f287,f200])).

fof(f200,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK4)
    | ~ spl8_3 ),
    inference(equality_resolution,[],[f168])).

fof(f168,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
        | u1_struct_0(sK4) = X0 )
    | ~ spl8_3 ),
    inference(superposition,[],[f167,f43])).

fof(f167,plain,
    ( ! [X4,X3] :
        ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(X3,X4)
        | u1_struct_0(sK4) = X3 )
    | ~ spl8_3 ),
    inference(resolution,[],[f67,f88])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f287,plain,
    ( r1_tarski(sK5(sK4),u1_pre_topc(sK3))
    | ~ sP0(sK4)
    | sP1(sK4)
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK3))
    | ~ spl8_3 ),
    inference(superposition,[],[f54,f276])).

fof(f54,plain,(
    ! [X0] :
      ( r1_tarski(sK5(X0),u1_pre_topc(X0))
      | ~ sP0(X0)
      | sP1(X0)
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f332,plain,
    ( spl8_19
    | ~ spl8_26
    | ~ spl8_25
    | ~ spl8_3
    | ~ spl8_15 ),
    inference(avatar_split_clause,[],[f312,f221,f87,f324,f329,f240])).

fof(f312,plain,
    ( ~ r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK3))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK3),sK5(sK4)),u1_pre_topc(sK3))
    | sP1(sK4)
    | ~ spl8_3
    | ~ spl8_15 ),
    inference(forward_demodulation,[],[f311,f200])).

fof(f311,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK3))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK3),sK5(sK4)),u1_pre_topc(sK3))
    | sP1(sK4)
    | ~ spl8_3
    | ~ spl8_15 ),
    inference(forward_demodulation,[],[f310,f276])).

fof(f310,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK3),sK5(sK4)),u1_pre_topc(sK3))
    | sP1(sK4)
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ spl8_3
    | ~ spl8_15 ),
    inference(forward_demodulation,[],[f309,f200])).

fof(f309,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK4),sK5(sK4)),u1_pre_topc(sK3))
    | sP1(sK4)
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ spl8_3
    | ~ spl8_15 ),
    inference(forward_demodulation,[],[f307,f276])).

fof(f307,plain,
    ( sP1(sK4)
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK4),sK5(sK4)),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ spl8_15 ),
    inference(resolution,[],[f223,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | sP1(X0)
      | ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK5(X0)),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f223,plain,
    ( sP0(sK4)
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f221])).

fof(f327,plain,
    ( spl8_19
    | spl8_24
    | ~ spl8_25
    | ~ spl8_3
    | ~ spl8_15 ),
    inference(avatar_split_clause,[],[f315,f221,f87,f324,f320,f240])).

fof(f315,plain,
    ( ~ r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK3))
    | m1_subset_1(sK5(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | sP1(sK4)
    | ~ spl8_3
    | ~ spl8_15 ),
    inference(forward_demodulation,[],[f314,f200])).

fof(f314,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK3))
    | m1_subset_1(sK5(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | sP1(sK4)
    | ~ spl8_3
    | ~ spl8_15 ),
    inference(forward_demodulation,[],[f313,f276])).

fof(f313,plain,
    ( m1_subset_1(sK5(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | sP1(sK4)
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ spl8_3
    | ~ spl8_15 ),
    inference(forward_demodulation,[],[f308,f200])).

fof(f308,plain,
    ( sP1(sK4)
    | m1_subset_1(sK5(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ spl8_15 ),
    inference(resolution,[],[f223,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | sP1(X0)
      | m1_subset_1(sK5(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f318,plain,
    ( ~ spl8_2
    | ~ spl8_3
    | spl8_20 ),
    inference(avatar_contradiction_clause,[],[f317])).

fof(f317,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_3
    | spl8_20 ),
    inference(resolution,[],[f316,f79])).

fof(f316,plain,
    ( ~ sP1(sK3)
    | ~ spl8_3
    | spl8_20 ),
    inference(resolution,[],[f282,f50])).

fof(f50,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f282,plain,
    ( ~ r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK3))
    | ~ spl8_3
    | spl8_20 ),
    inference(backward_demodulation,[],[f245,f276])).

fof(f245,plain,
    ( ~ r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4))
    | spl8_20 ),
    inference(avatar_component_clause,[],[f244])).

fof(f302,plain,
    ( spl8_15
    | spl8_23
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f289,f87,f299,f221])).

fof(f289,plain,
    ( r2_hidden(sK7(sK4),u1_pre_topc(sK3))
    | sP0(sK4)
    | ~ spl8_3 ),
    inference(superposition,[],[f60,f276])).

fof(f60,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),u1_pre_topc(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f297,plain,
    ( spl8_15
    | spl8_22
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f288,f87,f294,f221])).

fof(f288,plain,
    ( r2_hidden(sK6(sK4),u1_pre_topc(sK3))
    | sP0(sK4)
    | ~ spl8_3 ),
    inference(superposition,[],[f59,f276])).

fof(f59,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),u1_pre_topc(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f238,plain,
    ( spl8_15
    | spl8_18
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f218,f87,f235,f221])).

fof(f218,plain,
    ( m1_subset_1(sK6(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | sP0(sK4)
    | ~ spl8_3 ),
    inference(superposition,[],[f57,f200])).

fof(f57,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f233,plain,
    ( spl8_15
    | spl8_17
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f217,f87,f230,f221])).

fof(f217,plain,
    ( m1_subset_1(sK7(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | sP0(sK4)
    | ~ spl8_3 ),
    inference(superposition,[],[f58,f200])).

fof(f58,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f228,plain,
    ( spl8_15
    | ~ spl8_16
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f214,f87,f225,f221])).

fof(f214,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK3),sK6(sK4),sK7(sK4)),u1_pre_topc(sK4))
    | sP0(sK4)
    | ~ spl8_3 ),
    inference(superposition,[],[f61,f200])).

fof(f61,plain,(
    ! [X0] :
      ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK6(X0),sK7(X0)),u1_pre_topc(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f98,plain,(
    spl8_3 ),
    inference(avatar_contradiction_clause,[],[f97])).

fof(f97,plain,
    ( $false
    | spl8_3 ),
    inference(resolution,[],[f96,f42])).

fof(f96,plain,
    ( ~ l1_pre_topc(sK4)
    | spl8_3 ),
    inference(resolution,[],[f89,f46])).

fof(f46,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f89,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | spl8_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f82,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f81])).

fof(f81,plain,
    ( $false
    | spl8_1 ),
    inference(resolution,[],[f75,f41])).

fof(f41,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f29])).

% (1830)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f75,plain,
    ( ~ l1_pre_topc(sK3)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl8_1
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f80,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f71,f77,f73])).

fof(f71,plain,
    ( sP1(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f70,f44])).

fof(f44,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | sP1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f48,f62])).

fof(f48,plain,(
    ! [X0] :
      ( ~ sP2(X0)
      | ~ v2_pre_topc(X0)
      | sP1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

%------------------------------------------------------------------------------
