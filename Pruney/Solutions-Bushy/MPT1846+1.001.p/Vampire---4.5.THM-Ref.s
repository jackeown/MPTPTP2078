%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1846+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:44 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 207 expanded)
%              Number of leaves         :    8 (  65 expanded)
%              Depth                    :   17
%              Number of atoms          :  242 (1517 expanded)
%              Number of equality atoms :   27 ( 219 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f76,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f60,f75])).

fof(f75,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f74])).

fof(f74,plain,
    ( $false
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f73,f18])).

fof(f18,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( ~ v1_tex_2(sK1,sK0)
      | ~ v1_subset_1(sK2,u1_struct_0(sK0)) )
    & ( v1_tex_2(sK1,sK0)
      | v1_subset_1(sK2,u1_struct_0(sK0)) )
    & u1_struct_0(sK1) = sK2
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_pre_topc(sK1,sK0)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12,f11,f10])).

fof(f10,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ v1_tex_2(X1,X0)
                  | ~ v1_subset_1(X2,u1_struct_0(X0)) )
                & ( v1_tex_2(X1,X0)
                  | v1_subset_1(X2,u1_struct_0(X0)) )
                & u1_struct_0(X1) = X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v1_tex_2(X1,sK0)
                | ~ v1_subset_1(X2,u1_struct_0(sK0)) )
              & ( v1_tex_2(X1,sK0)
                | v1_subset_1(X2,u1_struct_0(sK0)) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_pre_topc(X1,sK0) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ v1_tex_2(X1,sK0)
              | ~ v1_subset_1(X2,u1_struct_0(sK0)) )
            & ( v1_tex_2(X1,sK0)
              | v1_subset_1(X2,u1_struct_0(sK0)) )
            & u1_struct_0(X1) = X2
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_pre_topc(X1,sK0) )
   => ( ? [X2] :
          ( ( ~ v1_tex_2(sK1,sK0)
            | ~ v1_subset_1(X2,u1_struct_0(sK0)) )
          & ( v1_tex_2(sK1,sK0)
            | v1_subset_1(X2,u1_struct_0(sK0)) )
          & u1_struct_0(sK1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_pre_topc(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X2] :
        ( ( ~ v1_tex_2(sK1,sK0)
          | ~ v1_subset_1(X2,u1_struct_0(sK0)) )
        & ( v1_tex_2(sK1,sK0)
          | v1_subset_1(X2,u1_struct_0(sK0)) )
        & u1_struct_0(sK1) = X2
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ v1_tex_2(sK1,sK0)
        | ~ v1_subset_1(sK2,u1_struct_0(sK0)) )
      & ( v1_tex_2(sK1,sK0)
        | v1_subset_1(sK2,u1_struct_0(sK0)) )
      & u1_struct_0(sK1) = sK2
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v1_tex_2(X1,X0)
                | ~ v1_subset_1(X2,u1_struct_0(X0)) )
              & ( v1_tex_2(X1,X0)
                | v1_subset_1(X2,u1_struct_0(X0)) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v1_tex_2(X1,X0)
                | ~ v1_subset_1(X2,u1_struct_0(X0)) )
              & ( v1_tex_2(X1,X0)
                | v1_subset_1(X2,u1_struct_0(X0)) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v1_subset_1(X2,u1_struct_0(X0))
              <~> v1_tex_2(X1,X0) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v1_subset_1(X2,u1_struct_0(X0))
              <~> v1_tex_2(X1,X0) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => ( v1_subset_1(X2,u1_struct_0(X0))
                  <=> v1_tex_2(X1,X0) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v1_subset_1(X2,u1_struct_0(X0))
                <=> v1_tex_2(X1,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_tex_2)).

fof(f73,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f72,f19])).

fof(f19,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f72,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f70,f63])).

fof(f63,plain,(
    ~ v1_tex_2(sK1,sK0) ),
    inference(global_subsumption,[],[f23,f62])).

fof(f62,plain,
    ( v1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v1_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f61,f18])).

fof(f61,plain,
    ( v1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v1_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f54,f19])).

fof(f54,plain,
    ( v1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v1_tex_2(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f52,f20])).

fof(f20,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f52,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_subset_1(sK2,u1_struct_0(X0))
      | ~ v1_tex_2(sK1,X0)
      | ~ m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f28,f21])).

fof(f21,plain,(
    u1_struct_0(sK1) = sK2 ),
    inference(cnf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X0,X3,X1] :
      ( v1_subset_1(X3,u1_struct_0(X0))
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & u1_struct_0(X1) = sK3(X0,X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK3(X0,X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v1_subset_1(X2,u1_struct_0(X0))
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f7])).

% (31194)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

fof(f23,plain,
    ( ~ v1_tex_2(sK1,sK0)
    | ~ v1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f70,plain,
    ( v1_tex_2(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_1 ),
    inference(resolution,[],[f64,f36])).

fof(f36,plain,
    ( v1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl4_1
  <=> v1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK2,u1_struct_0(X0))
      | v1_tex_2(sK1,X0)
      | ~ m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f41,f21])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f27,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X1) = sK3(X0,X1)
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f60,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f59])).

fof(f59,plain,
    ( $false
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f58,f18])).

fof(f58,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f57,f19])).

fof(f57,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f56,f37])).

fof(f37,plain,
    ( v1_tex_2(sK1,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl4_2
  <=> v1_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f56,plain,
    ( ~ v1_tex_2(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f54,f31])).

fof(f31,plain,
    ( ~ v1_subset_1(sK2,u1_struct_0(sK0))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f38,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f22,f33,f30])).

fof(f22,plain,
    ( v1_tex_2(sK1,sK0)
    | v1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f13])).

%------------------------------------------------------------------------------
