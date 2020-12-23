%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1845+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:44 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  204 (3035 expanded)
%              Number of leaves         :   18 ( 949 expanded)
%              Depth                    :   27
%              Number of atoms          :  820 (15057 expanded)
%              Number of equality atoms :   33 (3246 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f298,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f113,f136,f147,f165,f182,f192,f198,f203,f208,f242,f252,f264,f274,f280,f286,f292,f297])).

fof(f297,plain,
    ( spl5_5
    | spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f296,f106,f102,f144])).

fof(f144,plain,
    ( spl5_5
  <=> r2_hidden(sK3(sK1),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f102,plain,
    ( spl5_2
  <=> r1_tarski(sK4(sK1),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f106,plain,
    ( spl5_3
  <=> r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f296,plain,
    ( r1_tarski(sK4(sK1),u1_pre_topc(sK0))
    | r2_hidden(sK3(sK1),u1_pre_topc(sK0))
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f295,f107])).

fof(f107,plain,
    ( r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f106])).

fof(f295,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r1_tarski(sK4(sK1),u1_pre_topc(sK0))
    | r2_hidden(sK3(sK1),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f294,f63])).

fof(f63,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(trivial_inequality_removal,[],[f61])).

fof(f61,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
    | u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(superposition,[],[f59,f30])).

fof(f30,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ v2_pre_topc(sK1)
    & v2_pre_topc(sK0)
    & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_pre_topc(X1)
            & v2_pre_topc(X0)
            & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v2_pre_topc(X1)
          & v2_pre_topc(sK0)
          & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ~ v2_pre_topc(X1)
        & v2_pre_topc(sK0)
        & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        & l1_pre_topc(X1) )
   => ( ~ v2_pre_topc(sK1)
      & v2_pre_topc(sK0)
      & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_pre_topc(X1)
          & v2_pre_topc(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

% (30391)Refutation not found, incomplete strategy% (30391)------------------------------
% (30391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30391)Termination reason: Refutation not found, incomplete strategy

% (30391)Memory used [KB]: 10618
% (30391)Time elapsed: 0.064 s
% (30391)------------------------------
% (30391)------------------------------
fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_pre_topc(X1)
          & v2_pre_topc(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v2_pre_topc(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v2_pre_topc(X1) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v2_pre_topc(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v2_pre_topc(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tex_2)).

fof(f59,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | u1_struct_0(sK0) = X0 ) ),
    inference(resolution,[],[f57,f28])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = X1
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(X1,X2) ) ),
    inference(resolution,[],[f54,f33])).

fof(f33,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f294,plain,
    ( r1_tarski(sK4(sK1),u1_pre_topc(sK0))
    | r2_hidden(sK3(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f293,f29])).

fof(f29,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f293,plain,
    ( r1_tarski(sK4(sK1),u1_pre_topc(sK0))
    | r2_hidden(sK3(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f119,f32])).

fof(f32,plain,(
    ~ v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f119,plain,
    ( r1_tarski(sK4(sK1),u1_pre_topc(sK0))
    | r2_hidden(sK3(sK1),u1_pre_topc(sK0))
    | v2_pre_topc(sK1)
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK1) ),
    inference(superposition,[],[f47,f80])).

fof(f80,plain,(
    u1_pre_topc(sK0) = u1_pre_topc(sK1) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | u1_pre_topc(sK1) = X1 ) ),
    inference(superposition,[],[f68,f64])).

fof(f64,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) ),
    inference(backward_demodulation,[],[f30,f63])).

fof(f68,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))
      | u1_pre_topc(sK1) = X1 ) ),
    inference(resolution,[],[f67,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f67,plain,(
    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f66,f29])).

fof(f66,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK1) ),
    inference(superposition,[],[f33,f63])).

fof(f47,plain,(
    ! [X0] :
      ( r1_tarski(sK4(X0),u1_pre_topc(X0))
      | r2_hidden(sK3(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0)
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK2(X0),sK3(X0)),u1_pre_topc(X0))
            & r2_hidden(sK3(X0),u1_pre_topc(X0))
            & r2_hidden(sK2(X0),u1_pre_topc(X0))
            & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
            & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) )
          | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK4(X0)),u1_pre_topc(X0))
            & r1_tarski(sK4(X0),u1_pre_topc(X0))
            & m1_subset_1(sK4(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
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
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f23,f26,f25,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              & r2_hidden(X2,u1_pre_topc(X0))
              & r2_hidden(X1,u1_pre_topc(X0))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK2(X0),X2),u1_pre_topc(X0))
            & r2_hidden(X2,u1_pre_topc(X0))
            & r2_hidden(sK2(X0),u1_pre_topc(X0))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK2(X0),X2),u1_pre_topc(X0))
          & r2_hidden(X2,u1_pre_topc(X0))
          & r2_hidden(sK2(X0),u1_pre_topc(X0))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK2(X0),sK3(X0)),u1_pre_topc(X0))
        & r2_hidden(sK3(X0),u1_pre_topc(X0))
        & r2_hidden(sK2(X0),u1_pre_topc(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
          & r1_tarski(X3,u1_pre_topc(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK4(X0)),u1_pre_topc(X0))
        & r1_tarski(sK4(X0),u1_pre_topc(X0))
        & m1_subset_1(sK4(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
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
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
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
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
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
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

fof(f292,plain,
    ( spl5_8
    | ~ spl5_6
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f291,f106,f162,f189])).

fof(f189,plain,
    ( spl5_8
  <=> m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f162,plain,
    ( spl5_6
  <=> r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK4(sK1)),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f291,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK4(sK1)),u1_pre_topc(sK0))
    | m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f290,f107])).

fof(f290,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK4(sK1)),u1_pre_topc(sK0))
    | m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f289,f80])).

fof(f289,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK4(sK1)),u1_pre_topc(sK0))
    | m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1)) ),
    inference(forward_demodulation,[],[f288,f80])).

fof(f288,plain,
    ( m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK4(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1)) ),
    inference(subsumption_resolution,[],[f287,f29])).

fof(f287,plain,
    ( m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK4(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f211,f32])).

fof(f211,plain,
    ( m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_pre_topc(sK1)
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK4(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(superposition,[],[f42,f63])).

fof(f42,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_pre_topc(X0)
      | ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK4(X0)),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f286,plain,
    ( spl5_1
    | ~ spl5_6
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f285,f106,f162,f98])).

fof(f98,plain,
    ( spl5_1
  <=> r2_hidden(sK2(sK1),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f285,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK4(sK1)),u1_pre_topc(sK0))
    | r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f284,f107])).

fof(f284,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK4(sK1)),u1_pre_topc(sK0))
    | r2_hidden(sK2(sK1),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f283,f63])).

fof(f283,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK4(sK1)),u1_pre_topc(sK0))
    | r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f282,f63])).

fof(f282,plain,
    ( r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK1),sK4(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f281,f29])).

fof(f281,plain,
    ( r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK1),sK4(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f154,f32])).

fof(f154,plain,
    ( r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | v2_pre_topc(sK1)
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK1),sK4(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK1) ),
    inference(superposition,[],[f45,f80])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0)
      | ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK4(X0)),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f280,plain,
    ( ~ spl5_9
    | ~ spl5_6
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f279,f106,f162,f249])).

fof(f249,plain,
    ( spl5_9
  <=> r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2(sK1),sK3(sK1)),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f279,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK4(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2(sK1),sK3(sK1)),u1_pre_topc(sK0))
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f278,f107])).

fof(f278,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK4(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2(sK1),sK3(sK1)),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f277,f63])).

fof(f277,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK4(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2(sK1),sK3(sK1)),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f254,f80])).

fof(f254,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK4(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2(sK1),sK3(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(forward_demodulation,[],[f253,f63])).

fof(f253,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK1),sK4(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2(sK1),sK3(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(forward_demodulation,[],[f231,f80])).

fof(f231,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2(sK1),sK3(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK1),sK4(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(forward_demodulation,[],[f230,f63])).

fof(f230,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK1),sK2(sK1),sK3(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK1),sK4(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(forward_demodulation,[],[f229,f80])).

fof(f229,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK1),sK2(sK1),sK3(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK1),sK4(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(subsumption_resolution,[],[f226,f29])).

fof(f226,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK1),sK2(sK1),sK3(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK1),sK4(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f51,f32])).

fof(f51,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK2(X0),sK3(X0)),u1_pre_topc(X0))
      | ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK4(X0)),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f274,plain,
    ( ~ spl5_1
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | spl5_9 ),
    inference(avatar_contradiction_clause,[],[f273])).

fof(f273,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | spl5_9 ),
    inference(subsumption_resolution,[],[f272,f146])).

fof(f146,plain,
    ( r2_hidden(sK3(sK1),u1_pre_topc(sK0))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f144])).

fof(f272,plain,
    ( ~ r2_hidden(sK3(sK1),u1_pre_topc(sK0))
    | ~ spl5_1
    | ~ spl5_7
    | ~ spl5_8
    | spl5_9 ),
    inference(subsumption_resolution,[],[f271,f181])).

fof(f181,plain,
    ( m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl5_7
  <=> m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f271,plain,
    ( ~ m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK3(sK1),u1_pre_topc(sK0))
    | ~ spl5_1
    | ~ spl5_8
    | spl5_9 ),
    inference(subsumption_resolution,[],[f270,f191])).

fof(f191,plain,
    ( m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f189])).

fof(f270,plain,
    ( ~ m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK3(sK1),u1_pre_topc(sK0))
    | ~ spl5_1
    | spl5_9 ),
    inference(subsumption_resolution,[],[f268,f100])).

fof(f100,plain,
    ( r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f98])).

fof(f268,plain,
    ( ~ r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | ~ m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK3(sK1),u1_pre_topc(sK0))
    | spl5_9 ),
    inference(resolution,[],[f251,f234])).

fof(f234,plain,(
    ! [X0,X1] :
      ( r2_hidden(k9_subset_1(u1_struct_0(sK0),X1,X0),u1_pre_topc(sK0))
      | ~ r2_hidden(X1,u1_pre_topc(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,u1_pre_topc(sK0)) ) ),
    inference(subsumption_resolution,[],[f232,f31])).

fof(f31,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f232,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_pre_topc(sK0))
      | ~ r2_hidden(X1,u1_pre_topc(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | r2_hidden(k9_subset_1(u1_struct_0(sK0),X1,X0),u1_pre_topc(sK0)) ) ),
    inference(resolution,[],[f36,f28])).

fof(f36,plain,(
    ! [X4,X0,X5] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X5,u1_pre_topc(X0))
      | ~ r2_hidden(X4,u1_pre_topc(X0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f251,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2(sK1),sK3(sK1)),u1_pre_topc(sK0))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f249])).

fof(f264,plain,
    ( ~ spl5_2
    | ~ spl5_4
    | spl5_6 ),
    inference(avatar_split_clause,[],[f209,f162,f133,f102])).

fof(f133,plain,
    ( spl5_4
  <=> m1_subset_1(sK4(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f209,plain,
    ( ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(sK4(sK1),u1_pre_topc(sK0))
    | spl5_6 ),
    inference(resolution,[],[f164,f123])).

fof(f123,plain,(
    ! [X0] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(sK0),X0),u1_pre_topc(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ r1_tarski(X0,u1_pre_topc(sK0)) ) ),
    inference(subsumption_resolution,[],[f122,f28])).

fof(f122,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_pre_topc(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | r2_hidden(k5_setfam_1(u1_struct_0(sK0),X0),u1_pre_topc(sK0))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f35,f31])).

fof(f35,plain,(
    ! [X6,X0] :
      ( ~ v2_pre_topc(X0)
      | ~ r1_tarski(X6,u1_pre_topc(X0))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f164,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK4(sK1)),u1_pre_topc(sK0))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f162])).

fof(f252,plain,
    ( spl5_2
    | ~ spl5_9
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f247,f106,f249,f102])).

fof(f247,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2(sK1),sK3(sK1)),u1_pre_topc(sK0))
    | r1_tarski(sK4(sK1),u1_pre_topc(sK0))
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f246,f107])).

fof(f246,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2(sK1),sK3(sK1)),u1_pre_topc(sK0))
    | r1_tarski(sK4(sK1),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f245,f63])).

fof(f245,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2(sK1),sK3(sK1)),u1_pre_topc(sK0))
    | r1_tarski(sK4(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f244,f63])).

fof(f244,plain,
    ( r1_tarski(sK4(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK1),sK2(sK1),sK3(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f243,f29])).

fof(f243,plain,
    ( r1_tarski(sK4(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK1),sK2(sK1),sK3(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f212,f32])).

fof(f212,plain,
    ( r1_tarski(sK4(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK1),sK2(sK1),sK3(sK1)),u1_pre_topc(sK0))
    | v2_pre_topc(sK1)
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK1) ),
    inference(superposition,[],[f50,f80])).

fof(f50,plain,(
    ! [X0] :
      ( r1_tarski(sK4(X0),u1_pre_topc(X0))
      | ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK2(X0),sK3(X0)),u1_pre_topc(X0))
      | v2_pre_topc(X0)
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f242,plain,
    ( ~ spl5_1
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f241])).

fof(f241,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f240,f146])).

fof(f240,plain,
    ( ~ r2_hidden(sK3(sK1),u1_pre_topc(sK0))
    | ~ spl5_1
    | ~ spl5_3
    | spl5_4
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f239,f181])).

fof(f239,plain,
    ( ~ m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK3(sK1),u1_pre_topc(sK0))
    | ~ spl5_1
    | ~ spl5_3
    | spl5_4
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f238,f191])).

fof(f238,plain,
    ( ~ m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK3(sK1),u1_pre_topc(sK0))
    | ~ spl5_1
    | ~ spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f235,f100])).

fof(f235,plain,
    ( ~ r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | ~ m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK3(sK1),u1_pre_topc(sK0))
    | ~ spl5_3
    | spl5_4 ),
    inference(resolution,[],[f234,f223])).

fof(f223,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2(sK1),sK3(sK1)),u1_pre_topc(sK0))
    | ~ spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f222,f107])).

fof(f222,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2(sK1),sK3(sK1)),u1_pre_topc(sK0))
    | spl5_4 ),
    inference(forward_demodulation,[],[f221,f63])).

fof(f221,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2(sK1),sK3(sK1)),u1_pre_topc(sK0))
    | spl5_4 ),
    inference(forward_demodulation,[],[f220,f80])).

fof(f220,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2(sK1),sK3(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | spl5_4 ),
    inference(subsumption_resolution,[],[f219,f134])).

fof(f134,plain,
    ( ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f133])).

fof(f219,plain,
    ( m1_subset_1(sK4(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2(sK1),sK3(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(forward_demodulation,[],[f218,f63])).

fof(f218,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2(sK1),sK3(sK1)),u1_pre_topc(sK0))
    | m1_subset_1(sK4(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(forward_demodulation,[],[f217,f63])).

fof(f217,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK1),sK2(sK1),sK3(sK1)),u1_pre_topc(sK0))
    | m1_subset_1(sK4(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(forward_demodulation,[],[f216,f80])).

fof(f216,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK1),sK2(sK1),sK3(sK1)),u1_pre_topc(sK1))
    | m1_subset_1(sK4(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(subsumption_resolution,[],[f213,f29])).

fof(f213,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK1),sK2(sK1),sK3(sK1)),u1_pre_topc(sK1))
    | m1_subset_1(sK4(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f49,f32])).

fof(f49,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK2(X0),sK3(X0)),u1_pre_topc(X0))
      | m1_subset_1(sK4(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f208,plain,
    ( spl5_4
    | spl5_7
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f207,f106,f179,f133])).

fof(f207,plain,
    ( m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK4(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f206,f107])).

fof(f206,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK4(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f205,f80])).

fof(f205,plain,
    ( m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK4(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1)) ),
    inference(subsumption_resolution,[],[f204,f29])).

fof(f204,plain,
    ( m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK4(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f152,f32])).

fof(f152,plain,
    ( m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_pre_topc(sK1)
    | m1_subset_1(sK4(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(superposition,[],[f37,f63])).

fof(f37,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_pre_topc(X0)
      | m1_subset_1(sK4(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f203,plain,
    ( spl5_4
    | spl5_8
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f202,f106,f189,f133])).

fof(f202,plain,
    ( m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK4(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f201,f107])).

fof(f201,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK4(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f200,f80])).

fof(f200,plain,
    ( m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK4(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1)) ),
    inference(subsumption_resolution,[],[f199,f29])).

fof(f199,plain,
    ( m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK4(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f153,f32])).

fof(f153,plain,
    ( m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_pre_topc(sK1)
    | m1_subset_1(sK4(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(superposition,[],[f40,f63])).

fof(f40,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_pre_topc(X0)
      | m1_subset_1(sK4(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f198,plain,
    ( spl5_2
    | spl5_7
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f197,f106,f179,f102])).

fof(f197,plain,
    ( m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK4(sK1),u1_pre_topc(sK0))
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f196,f107])).

fof(f196,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK4(sK1),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f195,f63])).

fof(f195,plain,
    ( m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK4(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f194,f63])).

fof(f194,plain,
    ( r1_tarski(sK4(sK1),u1_pre_topc(sK0))
    | m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f193,f29])).

fof(f193,plain,
    ( r1_tarski(sK4(sK1),u1_pre_topc(sK0))
    | m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f120,f32])).

fof(f120,plain,
    ( r1_tarski(sK4(sK1),u1_pre_topc(sK0))
    | m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_pre_topc(sK1)
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK1) ),
    inference(superposition,[],[f38,f80])).

fof(f38,plain,(
    ! [X0] :
      ( r1_tarski(sK4(X0),u1_pre_topc(X0))
      | m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_pre_topc(X0)
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f192,plain,
    ( spl5_2
    | spl5_8
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f187,f106,f189,f102])).

fof(f187,plain,
    ( m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK4(sK1),u1_pre_topc(sK0))
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f186,f107])).

fof(f186,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK4(sK1),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f185,f63])).

fof(f185,plain,
    ( m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK4(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f184,f63])).

fof(f184,plain,
    ( r1_tarski(sK4(sK1),u1_pre_topc(sK0))
    | m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f183,f29])).

fof(f183,plain,
    ( r1_tarski(sK4(sK1),u1_pre_topc(sK0))
    | m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f121,f32])).

fof(f121,plain,
    ( r1_tarski(sK4(sK1),u1_pre_topc(sK0))
    | m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_pre_topc(sK1)
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK1) ),
    inference(superposition,[],[f41,f80])).

fof(f41,plain,(
    ! [X0] :
      ( r1_tarski(sK4(X0),u1_pre_topc(X0))
      | m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_pre_topc(X0)
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f182,plain,
    ( spl5_7
    | ~ spl5_6
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f177,f106,f162,f179])).

fof(f177,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK4(sK1)),u1_pre_topc(sK0))
    | m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f176,f107])).

fof(f176,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK4(sK1)),u1_pre_topc(sK0))
    | m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f175,f80])).

fof(f175,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK4(sK1)),u1_pre_topc(sK0))
    | m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1)) ),
    inference(forward_demodulation,[],[f174,f80])).

fof(f174,plain,
    ( m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK4(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1)) ),
    inference(subsumption_resolution,[],[f173,f29])).

fof(f173,plain,
    ( m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK4(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f172,f32])).

fof(f172,plain,
    ( m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_pre_topc(sK1)
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK4(sK1)),u1_pre_topc(sK1))
    | ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(superposition,[],[f39,f63])).

fof(f39,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_pre_topc(X0)
      | ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK4(X0)),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f165,plain,
    ( spl5_5
    | ~ spl5_6
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f160,f106,f162,f144])).

fof(f160,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK4(sK1)),u1_pre_topc(sK0))
    | r2_hidden(sK3(sK1),u1_pre_topc(sK0))
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f159,f107])).

fof(f159,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK4(sK1)),u1_pre_topc(sK0))
    | r2_hidden(sK3(sK1),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f158,f63])).

fof(f158,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK0),sK4(sK1)),u1_pre_topc(sK0))
    | r2_hidden(sK3(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f157,f63])).

fof(f157,plain,
    ( r2_hidden(sK3(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK1),sK4(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f156,f29])).

fof(f156,plain,
    ( r2_hidden(sK3(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK1),sK4(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f155,f32])).

fof(f155,plain,
    ( r2_hidden(sK3(sK1),u1_pre_topc(sK0))
    | v2_pre_topc(sK1)
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK1),sK4(sK1)),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK1) ),
    inference(superposition,[],[f48,f80])).

fof(f48,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0)
      | ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK4(X0)),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f147,plain,
    ( spl5_5
    | spl5_4
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f142,f106,f133,f144])).

fof(f142,plain,
    ( m1_subset_1(sK4(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r2_hidden(sK3(sK1),u1_pre_topc(sK0))
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f141,f107])).

fof(f141,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK4(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r2_hidden(sK3(sK1),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f140,f63])).

fof(f140,plain,
    ( m1_subset_1(sK4(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r2_hidden(sK3(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f139,f63])).

fof(f139,plain,
    ( r2_hidden(sK3(sK1),u1_pre_topc(sK0))
    | m1_subset_1(sK4(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f138,f29])).

fof(f138,plain,
    ( r2_hidden(sK3(sK1),u1_pre_topc(sK0))
    | m1_subset_1(sK4(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f137,f32])).

fof(f137,plain,
    ( r2_hidden(sK3(sK1),u1_pre_topc(sK0))
    | v2_pre_topc(sK1)
    | m1_subset_1(sK4(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK1) ),
    inference(superposition,[],[f46,f80])).

fof(f46,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0)
      | m1_subset_1(sK4(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f136,plain,
    ( spl5_1
    | spl5_4
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f131,f106,f133,f98])).

fof(f131,plain,
    ( m1_subset_1(sK4(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f130,f107])).

fof(f130,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | m1_subset_1(sK4(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r2_hidden(sK2(sK1),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f129,f63])).

fof(f129,plain,
    ( m1_subset_1(sK4(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f128,f63])).

fof(f128,plain,
    ( r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | m1_subset_1(sK4(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f127,f29])).

fof(f127,plain,
    ( r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | m1_subset_1(sK4(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f126,f32])).

fof(f126,plain,
    ( r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | v2_pre_topc(sK1)
    | m1_subset_1(sK4(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK1) ),
    inference(superposition,[],[f43,f80])).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0)
      | m1_subset_1(sK4(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f113,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | spl5_3 ),
    inference(subsumption_resolution,[],[f111,f28])).

fof(f111,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f110,f31])).

fof(f110,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | spl5_3 ),
    inference(resolution,[],[f108,f34])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f108,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f106])).

fof(f109,plain,
    ( spl5_1
    | spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f96,f106,f102,f98])).

fof(f96,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | r1_tarski(sK4(sK1),u1_pre_topc(sK0))
    | r2_hidden(sK2(sK1),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f95,f63])).

fof(f95,plain,
    ( r1_tarski(sK4(sK1),u1_pre_topc(sK0))
    | r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f94,f29])).

fof(f94,plain,
    ( r1_tarski(sK4(sK1),u1_pre_topc(sK0))
    | r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f93,f32])).

fof(f93,plain,
    ( r1_tarski(sK4(sK1),u1_pre_topc(sK0))
    | r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | v2_pre_topc(sK1)
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK1) ),
    inference(superposition,[],[f44,f80])).

% (30381)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f44,plain,(
    ! [X0] :
      ( r1_tarski(sK4(X0),u1_pre_topc(X0))
      | r2_hidden(sK2(X0),u1_pre_topc(X0))
      | v2_pre_topc(X0)
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

%------------------------------------------------------------------------------
