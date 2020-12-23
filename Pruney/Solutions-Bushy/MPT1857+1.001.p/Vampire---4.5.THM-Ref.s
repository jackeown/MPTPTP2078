%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1857+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 308 expanded)
%              Number of leaves         :   16 ( 114 expanded)
%              Depth                    :   23
%              Number of atoms          :  415 (2023 expanded)
%              Number of equality atoms :   65 ( 483 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f308,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f126,f129,f306])).

fof(f306,plain,(
    ~ spl9_6 ),
    inference(avatar_contradiction_clause,[],[f305])).

fof(f305,plain,
    ( $false
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f299,f68])).

fof(f68,plain,(
    sP1(sK3,sK5) ),
    inference(subsumption_resolution,[],[f67,f40])).

fof(f40,plain,(
    v2_tex_2(sK5,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ v2_tex_2(sK6,sK4)
    & v2_tex_2(sK5,sK3)
    & sK5 = sK6
    & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    & l1_pre_topc(sK4)
    & l1_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f8,f21,f20,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v2_tex_2(X3,X1)
                    & v2_tex_2(X2,X0)
                    & X2 = X3
                    & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tex_2(X3,X1)
                  & v2_tex_2(X2,sK3)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v2_tex_2(X3,X1)
                & v2_tex_2(X2,sK3)
                & X2 = X3
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v2_tex_2(X3,sK4)
              & v2_tex_2(X2,sK3)
              & X2 = X3
              & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) )
      & l1_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v2_tex_2(X3,sK4)
            & v2_tex_2(X2,sK3)
            & X2 = X3
            & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) )
   => ( ? [X3] :
          ( ~ v2_tex_2(X3,sK4)
          & v2_tex_2(sK5,sK3)
          & sK5 = X3
          & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
      & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X3] :
        ( ~ v2_tex_2(X3,sK4)
        & v2_tex_2(sK5,sK3)
        & sK5 = X3
        & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
   => ( ~ v2_tex_2(sK6,sK4)
      & v2_tex_2(sK5,sK3)
      & sK5 = sK6
      & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
      & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ) ),
    introduced(choice_axiom,[])).

% (13632)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tex_2(X3,X1)
                  & v2_tex_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tex_2(X3,X1)
                  & v2_tex_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v2_tex_2(X2,X0)
                        & X2 = X3
                        & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                     => v2_tex_2(X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v2_tex_2(X2,X0)
                      & X2 = X3
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => v2_tex_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tex_2)).

fof(f67,plain,
    ( ~ v2_tex_2(sK5,sK3)
    | sP1(sK3,sK5) ),
    inference(resolution,[],[f64,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | ~ v2_tex_2(X0,X1)
      | sP1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( v2_tex_2(X0,X1)
          | ~ sP1(X1,X0) )
        & ( sP1(X1,X0)
          | ~ v2_tex_2(X0,X1) ) )
      | ~ sP2(X0,X1) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ( ( v2_tex_2(X1,X0)
          | ~ sP1(X0,X1) )
        & ( sP1(X0,X1)
          | ~ v2_tex_2(X1,X0) ) )
      | ~ sP2(X1,X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ( v2_tex_2(X1,X0)
      <=> sP1(X0,X1) )
      | ~ sP2(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f64,plain,(
    sP2(sK5,sK3) ),
    inference(subsumption_resolution,[],[f61,f34])).

fof(f34,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f61,plain,
    ( sP2(sK5,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f55,f36])).

fof(f36,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f22])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f12,f16,f15,f14])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( sP0(X2,X1,X0)
    <=> ? [X3] :
          ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f15,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ! [X2] :
          ( sP0(X2,X1,X0)
          | ~ r1_tarski(X2,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v3_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).

fof(f299,plain,
    ( ~ sP1(sK3,sK5)
    | ~ spl9_6 ),
    inference(resolution,[],[f298,f71])).

fof(f71,plain,(
    ~ sP1(sK4,sK5) ),
    inference(subsumption_resolution,[],[f69,f59])).

fof(f59,plain,(
    ~ v2_tex_2(sK5,sK4) ),
    inference(forward_demodulation,[],[f41,f39])).

fof(f39,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f22])).

fof(f41,plain,(
    ~ v2_tex_2(sK6,sK4) ),
    inference(cnf_transformation,[],[f22])).

fof(f69,plain,
    ( ~ sP1(sK4,sK5)
    | v2_tex_2(sK5,sK4) ),
    inference(resolution,[],[f65,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | ~ sP1(X1,X0)
      | v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f65,plain,(
    sP2(sK5,sK4) ),
    inference(subsumption_resolution,[],[f62,f35])).

fof(f35,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f22])).

fof(f62,plain,
    ( sP2(sK5,sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(resolution,[],[f55,f60])).

fof(f60,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(forward_demodulation,[],[f37,f39])).

fof(f37,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f22])).

fof(f298,plain,
    ( ! [X0] :
        ( sP1(sK4,X0)
        | ~ sP1(sK3,X0) )
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f297,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK7(X0,X1),X1)
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ( ~ sP0(sK7(X0,X1),X1,X0)
          & r1_tarski(sK7(X0,X1),X1)
          & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( sP0(X3,X1,X0)
            | ~ r1_tarski(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ sP0(X2,X1,X0)
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ sP0(sK7(X0,X1),X1,X0)
        & r1_tarski(sK7(X0,X1),X1)
        & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ~ sP0(X2,X1,X0)
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( sP0(X3,X1,X0)
            | ~ r1_tarski(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP1(X0,X1) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ~ sP0(X2,X1,X0)
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( sP0(X2,X1,X0)
            | ~ r1_tarski(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f297,plain,
    ( ! [X0] :
        ( sP1(sK4,X0)
        | ~ r1_tarski(sK7(sK4,X0),X0)
        | ~ sP1(sK3,X0) )
    | ~ spl9_6 ),
    inference(duplicate_literal_removal,[],[f295])).

fof(f295,plain,
    ( ! [X0] :
        ( sP1(sK4,X0)
        | ~ r1_tarski(sK7(sK4,X0),X0)
        | sP1(sK4,X0)
        | ~ sP1(sK3,X0) )
    | ~ spl9_6 ),
    inference(resolution,[],[f293,f157])).

fof(f157,plain,
    ( ! [X2,X1] :
        ( sP0(sK7(sK4,X1),X2,sK3)
        | ~ r1_tarski(sK7(sK4,X1),X2)
        | sP1(sK4,X1)
        | ~ sP1(sK3,X2) )
    | ~ spl9_6 ),
    inference(resolution,[],[f140,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X3,X1)
      | sP0(X3,X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f140,plain,
    ( ! [X4] :
        ( m1_subset_1(sK7(sK4,X4),k1_zfmisc_1(u1_struct_0(sK3)))
        | sP1(sK4,X4) )
    | ~ spl9_6 ),
    inference(superposition,[],[f48,f131])).

fof(f131,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK4)
    | ~ spl9_6 ),
    inference(equality_resolution,[],[f125])).

fof(f125,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
        | u1_struct_0(sK4) = X0 )
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl9_6
  <=> ! [X1,X0] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
        | u1_struct_0(sK4) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f293,plain,
    ( ! [X0] :
        ( ~ sP0(sK7(sK4,X0),X0,sK3)
        | sP1(sK4,X0) )
    | ~ spl9_6 ),
    inference(resolution,[],[f292,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ sP0(sK7(X0,X1),X1,X0)
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f292,plain,
    ( ! [X0,X1] :
        ( sP0(X1,X0,sK4)
        | ~ sP0(X1,X0,sK3) )
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f268,f290])).

fof(f290,plain,
    ( ! [X2,X3] :
        ( v3_pre_topc(sK8(X2,X3,sK3),sK4)
        | ~ sP0(X2,X3,sK3) )
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f288,f34])).

fof(f288,plain,
    ( ! [X2,X3] :
        ( v3_pre_topc(sK8(X2,X3,sK3),sK4)
        | ~ sP0(X2,X3,sK3)
        | ~ l1_pre_topc(sK3) )
    | ~ spl9_6 ),
    inference(duplicate_literal_removal,[],[f287])).

fof(f287,plain,
    ( ! [X2,X3] :
        ( v3_pre_topc(sK8(X2,X3,sK3),sK4)
        | ~ sP0(X2,X3,sK3)
        | ~ l1_pre_topc(sK3)
        | ~ sP0(X2,X3,sK3) )
    | ~ spl9_6 ),
    inference(resolution,[],[f224,f101])).

fof(f101,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK8(X2,X3,X4),u1_pre_topc(X4))
      | ~ l1_pre_topc(X4)
      | ~ sP0(X2,X3,X4) ) ),
    inference(subsumption_resolution,[],[f80,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK8(X0,X1,X2),X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( k9_subset_1(u1_struct_0(X2),X1,X3) != X0
            | ~ v3_pre_topc(X3,X2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ( k9_subset_1(u1_struct_0(X2),X1,sK8(X0,X1,X2)) = X0
          & v3_pre_topc(sK8(X0,X1,X2),X2)
          & m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X2),X1,X4) = X0
          & v3_pre_topc(X4,X2)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( k9_subset_1(u1_struct_0(X2),X1,sK8(X0,X1,X2)) = X0
        & v3_pre_topc(sK8(X0,X1,X2),X2)
        & m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( k9_subset_1(u1_struct_0(X2),X1,X3) != X0
            | ~ v3_pre_topc(X3,X2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ? [X4] :
            ( k9_subset_1(u1_struct_0(X2),X1,X4) = X0
            & v3_pre_topc(X4,X2)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ( sP0(X2,X1,X0)
        | ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ? [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
            & v3_pre_topc(X3,X0)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f80,plain,(
    ! [X4,X2,X3] :
      ( ~ v3_pre_topc(sK8(X2,X3,X4),X4)
      | r2_hidden(sK8(X2,X3,X4),u1_pre_topc(X4))
      | ~ l1_pre_topc(X4)
      | ~ sP0(X2,X3,X4) ) ),
    inference(resolution,[],[f43,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f224,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(sK8(X4,X5,sK3),u1_pre_topc(sK3))
        | v3_pre_topc(sK8(X4,X5,sK3),sK4)
        | ~ sP0(X4,X5,sK3) )
    | ~ spl9_6 ),
    inference(resolution,[],[f206,f51])).

fof(f206,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ r2_hidden(X1,u1_pre_topc(sK3))
        | v3_pre_topc(X1,sK4) )
    | ~ spl9_6 ),
    inference(backward_demodulation,[],[f146,f202])).

fof(f202,plain,
    ( u1_pre_topc(sK3) = u1_pre_topc(sK4)
    | ~ spl9_6 ),
    inference(equality_resolution,[],[f173])).

fof(f173,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
        | u1_pre_topc(sK4) = X1 )
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f170,f144])).

fof(f144,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f136,f35])).

fof(f136,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK4)
    | ~ spl9_6 ),
    inference(superposition,[],[f42,f131])).

fof(f42,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f170,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
        | u1_pre_topc(sK4) = X1
        | ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) )
    | ~ spl9_6 ),
    inference(superposition,[],[f57,f134])).

fof(f134,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK4))
    | ~ spl9_6 ),
    inference(backward_demodulation,[],[f38,f131])).

fof(f38,plain,(
    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(cnf_transformation,[],[f22])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f146,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ r2_hidden(X1,u1_pre_topc(sK4))
        | v3_pre_topc(X1,sK4) )
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f138,f35])).

fof(f138,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ r2_hidden(X1,u1_pre_topc(sK4))
        | v3_pre_topc(X1,sK4)
        | ~ l1_pre_topc(sK4) )
    | ~ spl9_6 ),
    inference(superposition,[],[f44,f131])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f268,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(sK8(X1,X0,sK3),sK4)
        | sP0(X1,X0,sK4)
        | ~ sP0(X1,X0,sK3) )
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f266,f51])).

fof(f266,plain,
    ( ! [X0,X1] :
        ( sP0(X1,X0,sK4)
        | ~ v3_pre_topc(sK8(X1,X0,sK3),sK4)
        | ~ m1_subset_1(sK8(X1,X0,sK3),k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ sP0(X1,X0,sK3) )
    | ~ spl9_6 ),
    inference(superposition,[],[f197,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(u1_struct_0(X2),X1,sK8(X0,X1,X2)) = X0
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f197,plain,
    ( ! [X0,X1] :
        ( sP0(k9_subset_1(u1_struct_0(sK3),X0,X1),X0,sK4)
        | ~ v3_pre_topc(X1,sK4)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) )
    | ~ spl9_6 ),
    inference(superposition,[],[f58,f131])).

fof(f58,plain,(
    ! [X2,X3,X1] :
      ( sP0(k9_subset_1(u1_struct_0(X2),X1,X3),X1,X2)
      | ~ v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2)
      | k9_subset_1(u1_struct_0(X2),X1,X3) != X0
      | ~ v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f129,plain,(
    spl9_5 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | spl9_5 ),
    inference(subsumption_resolution,[],[f127,f35])).

fof(f127,plain,
    ( ~ l1_pre_topc(sK4)
    | spl9_5 ),
    inference(resolution,[],[f122,f42])).

fof(f122,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | spl9_5 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl9_5
  <=> m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f126,plain,
    ( ~ spl9_5
    | spl9_6 ),
    inference(avatar_split_clause,[],[f116,f124,f120])).

fof(f116,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
      | u1_struct_0(sK4) = X0
      | ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ) ),
    inference(superposition,[],[f56,f38])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f13])).

%------------------------------------------------------------------------------
