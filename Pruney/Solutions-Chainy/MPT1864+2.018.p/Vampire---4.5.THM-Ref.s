%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 275 expanded)
%              Number of leaves         :   13 ( 101 expanded)
%              Depth                    :   27
%              Number of atoms          :  298 (1944 expanded)
%              Number of equality atoms :   36 ( 254 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f103,plain,(
    $false ),
    inference(subsumption_resolution,[],[f36,f100])).

fof(f100,plain,(
    ! [X2] : ~ r2_hidden(X2,sK3) ),
    inference(resolution,[],[f98,f33])).

fof(f33,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ! [X3] :
        ( k9_subset_1(u1_struct_0(sK2),sK3,X3) != k1_tarski(sK4)
        | ~ v3_pre_topc(X3,sK2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
    & r2_hidden(sK4,sK3)
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & v2_tex_2(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f11,f23,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),X1,X3)
                  | ~ v3_pre_topc(X3,sK2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & v2_tex_2(X1,sK2)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ! [X3] :
                ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),X1,X3)
                | ~ v3_pre_topc(X3,sK2)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
            & r2_hidden(X2,X1)
            & m1_subset_1(X2,u1_struct_0(sK2)) )
        & v2_tex_2(X1,sK2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ? [X2] :
          ( ! [X3] :
              ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),sK3,X3)
              | ~ v3_pre_topc(X3,sK2)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
          & r2_hidden(X2,sK3)
          & m1_subset_1(X2,u1_struct_0(sK2)) )
      & v2_tex_2(sK3,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),sK3,X3)
            | ~ v3_pre_topc(X3,sK2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
        & r2_hidden(X2,sK3)
        & m1_subset_1(X2,u1_struct_0(sK2)) )
   => ( ! [X3] :
          ( k9_subset_1(u1_struct_0(sK2),sK3,X3) != k1_tarski(sK4)
          | ~ v3_pre_topc(X3,sK2)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
      & r2_hidden(sK4,sK3)
      & m1_subset_1(sK4,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tex_2(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ ( ! [X3] :
                          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
                              & v3_pre_topc(X3,X0) ) )
                      & r2_hidden(X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
                            & v3_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tex_2)).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f97,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f97,plain,(
    v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f96,f36])).

fof(f96,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ r2_hidden(sK4,sK3) ),
    inference(resolution,[],[f95,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f95,plain,
    ( ~ r1_tarski(k1_tarski(sK4),sK3)
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f94,f55])).

fof(f55,plain,
    ( r2_hidden(sK4,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f50,f35])).

fof(f35,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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

fof(f94,plain,
    ( ~ r2_hidden(sK4,u1_struct_0(sK2))
    | ~ r1_tarski(k1_tarski(sK4),sK3) ),
    inference(resolution,[],[f93,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f93,plain,
    ( ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(k1_tarski(sK4),sK3) ),
    inference(subsumption_resolution,[],[f92,f64])).

fof(f64,plain,(
    sP0(sK3,sK2) ),
    inference(subsumption_resolution,[],[f63,f34])).

fof(f34,plain,(
    v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f63,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | sP0(sK3,sK2) ),
    inference(resolution,[],[f61,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ v2_tex_2(X1,X0)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( v2_tex_2(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v2_tex_2(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v2_tex_2(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f61,plain,(
    sP1(sK2,sK3) ),
    inference(resolution,[],[f59,f33])).

fof(f59,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(sK2,X0) ) ),
    inference(resolution,[],[f47,f32])).

fof(f32,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f13,f19,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( ? [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
              & v3_pre_topc(X3,X0)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ r1_tarski(X2,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f92,plain,
    ( ~ r1_tarski(k1_tarski(sK4),sK3)
    | ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ sP0(sK3,sK2) ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,
    ( ~ r1_tarski(k1_tarski(sK4),sK3)
    | ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(k1_tarski(sK4),sK3)
    | ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ sP0(sK3,sK2) ),
    inference(resolution,[],[f88,f41])).

% (29028)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f41,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tarski(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X1),X0,X3) != sK5(X0,X1)
              | ~ v3_pre_topc(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(sK5(X0,X1),X0)
          & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X4] :
            ( ( k9_subset_1(u1_struct_0(X1),X0,sK6(X0,X1,X4)) = X4
              & v3_pre_topc(sK6(X0,X1,X4),X1)
              & m1_subset_1(sK6(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r1_tarski(X4,X0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f27,f29,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X1),X0,X3) != X2
              | ~ v3_pre_topc(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X1),X0,X3) != sK5(X0,X1)
            | ~ v3_pre_topc(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        & r1_tarski(sK5(X0,X1),X0)
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X1),X0,X5) = X4
          & v3_pre_topc(X5,X1)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X1),X0,sK6(X0,X1,X4)) = X4
        & v3_pre_topc(sK6(X0,X1,X4),X1)
        & m1_subset_1(sK6(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X1),X0,X3) != X2
                | ~ v3_pre_topc(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & r1_tarski(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( k9_subset_1(u1_struct_0(X1),X0,X5) = X4
                & v3_pre_topc(X5,X1)
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r1_tarski(X4,X0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r1_tarski(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f88,plain,
    ( ~ m1_subset_1(sK6(sK3,sK2,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(k1_tarski(sK4),sK3)
    | ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f87,f64])).

fof(f87,plain,
    ( ~ m1_subset_1(sK6(sK3,sK2,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(k1_tarski(sK4),sK3)
    | ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ sP0(sK3,sK2) ),
    inference(resolution,[],[f86,f42])).

fof(f42,plain,(
    ! [X4,X0,X1] :
      ( v3_pre_topc(sK6(X0,X1,X4),X1)
      | ~ r1_tarski(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f86,plain,
    ( ~ v3_pre_topc(sK6(sK3,sK2,k1_tarski(sK4)),sK2)
    | ~ m1_subset_1(sK6(sK3,sK2,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(trivial_inequality_removal,[],[f84])).

fof(f84,plain,
    ( k1_tarski(sK4) != k1_tarski(sK4)
    | ~ v3_pre_topc(sK6(sK3,sK2,k1_tarski(sK4)),sK2)
    | ~ m1_subset_1(sK6(sK3,sK2,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(superposition,[],[f37,f83])).

fof(f83,plain,(
    k1_tarski(sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k1_tarski(sK4))) ),
    inference(resolution,[],[f80,f36])).

fof(f80,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK3)
      | k1_tarski(sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k1_tarski(sK4))) ) ),
    inference(resolution,[],[f78,f33])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k1_tarski(sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k1_tarski(sK4)))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f77,f53])).

fof(f77,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | k1_tarski(sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k1_tarski(sK4))) ),
    inference(subsumption_resolution,[],[f74,f64])).

fof(f74,plain,
    ( ~ sP0(sK3,sK2)
    | k1_tarski(sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k1_tarski(sK4)))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f73,f36])).

fof(f73,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4,X0)
      | ~ sP0(X0,sK2)
      | k1_tarski(sK4) = k9_subset_1(u1_struct_0(sK2),X0,sK6(X0,sK2,k1_tarski(sK4)))
      | v1_xboole_0(u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f72,f55])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(X1))
      | ~ sP0(X2,X1)
      | ~ r2_hidden(X0,X2)
      | k1_tarski(X0) = k9_subset_1(u1_struct_0(X1),X2,sK6(X2,X1,k1_tarski(X0))) ) ),
    inference(resolution,[],[f70,f49])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k1_tarski(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,sK6(X1,X0,k1_tarski(X2)))
      | ~ sP0(X1,X0)
      | ~ r2_hidden(X2,X1) ) ),
    inference(resolution,[],[f43,f52])).

fof(f43,plain,(
    ! [X4,X0,X1] :
      ( ~ r1_tarski(X4,X0)
      | k9_subset_1(u1_struct_0(X1),X0,sK6(X0,X1,X4)) = X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f37,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK2),sK3,X3) != k1_tarski(sK4)
      | ~ v3_pre_topc(X3,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f36,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:00:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (29030)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (29032)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.50  % (29023)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % (29052)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.50  % (29030)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (29048)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.51  % (29042)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.51  % (29027)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (29036)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (29025)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (29026)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f103,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(subsumption_resolution,[],[f36,f100])).
% 0.20/0.51  fof(f100,plain,(
% 0.20/0.51    ( ! [X2] : (~r2_hidden(X2,sK3)) )),
% 0.20/0.51    inference(resolution,[],[f98,f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ((! [X3] : (k9_subset_1(u1_struct_0(sK2),sK3,X3) != k1_tarski(sK4) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(sK4,sK3) & m1_subset_1(sK4,u1_struct_0(sK2))) & v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f11,f23,f22,f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),X1,X3) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK2))) & v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),X1,X3) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK2))) & v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) => (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),sK3,X3) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(X2,sK3) & m1_subset_1(X2,u1_struct_0(sK2))) & v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),sK3,X3) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(X2,sK3) & m1_subset_1(X2,u1_struct_0(sK2))) => (! [X3] : (k9_subset_1(u1_struct_0(sK2),sK3,X3) != k1_tarski(sK4) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(sK4,sK3) & m1_subset_1(sK4,u1_struct_0(sK2)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f10])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((? [X2] : ((! [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,negated_conjecture,(
% 0.20/0.51    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 0.20/0.51    inference(negated_conjecture,[],[f8])).
% 0.20/0.51  fof(f8,conjecture,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tex_2)).
% 0.20/0.51  fof(f98,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~r2_hidden(X1,X0)) )),
% 0.20/0.51    inference(resolution,[],[f97,f53])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.51  fof(f97,plain,(
% 0.20/0.51    v1_xboole_0(u1_struct_0(sK2))),
% 0.20/0.51    inference(subsumption_resolution,[],[f96,f36])).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    v1_xboole_0(u1_struct_0(sK2)) | ~r2_hidden(sK4,sK3)),
% 0.20/0.51    inference(resolution,[],[f95,f52])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.20/0.51    inference(nnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.20/0.51  fof(f95,plain,(
% 0.20/0.51    ~r1_tarski(k1_tarski(sK4),sK3) | v1_xboole_0(u1_struct_0(sK2))),
% 0.20/0.51    inference(resolution,[],[f94,f55])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    r2_hidden(sK4,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2))),
% 0.20/0.51    inference(resolution,[],[f50,f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    m1_subset_1(sK4,u1_struct_0(sK2))),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.51    inference(flattening,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    ~r2_hidden(sK4,u1_struct_0(sK2)) | ~r1_tarski(k1_tarski(sK4),sK3)),
% 0.20/0.51    inference(resolution,[],[f93,f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    ~m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(k1_tarski(sK4),sK3)),
% 0.20/0.51    inference(subsumption_resolution,[],[f92,f64])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    sP0(sK3,sK2)),
% 0.20/0.51    inference(subsumption_resolution,[],[f63,f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    v2_tex_2(sK3,sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    ~v2_tex_2(sK3,sK2) | sP0(sK3,sK2)),
% 0.20/0.51    inference(resolution,[],[f61,f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~sP1(X0,X1) | ~v2_tex_2(X1,X0) | sP0(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0,X1] : (((v2_tex_2(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v2_tex_2(X1,X0))) | ~sP1(X0,X1))),
% 0.20/0.51    inference(nnf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0,X1] : ((v2_tex_2(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    sP1(sK2,sK3)),
% 0.20/0.52    inference(resolution,[],[f59,f33])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(sK2,X0)) )),
% 0.20/0.52    inference(resolution,[],[f47,f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    l1_pre_topc(sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(definition_folding,[],[f13,f19,f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).
% 0.20/0.52  fof(f92,plain,(
% 0.20/0.52    ~r1_tarski(k1_tarski(sK4),sK3) | ~m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) | ~sP0(sK3,sK2)),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f91])).
% 0.20/0.52  fof(f91,plain,(
% 0.20/0.52    ~r1_tarski(k1_tarski(sK4),sK3) | ~m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(k1_tarski(sK4),sK3) | ~m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) | ~sP0(sK3,sK2)),
% 0.20/0.52    inference(resolution,[],[f88,f41])).
% 0.20/0.52  % (29028)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X4,X0,X1] : (m1_subset_1(sK6(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1))) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~sP0(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ! [X0,X1] : ((sP0(X0,X1) | (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != sK5(X0,X1) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(sK5(X0,X1),X0) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X1),X0,sK6(X0,X1,X4)) = X4 & v3_pre_topc(sK6(X0,X1,X4),X1) & m1_subset_1(sK6(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f27,f29,f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != X2 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != sK5(X0,X1) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(sK5(X0,X1),X0) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X1),X0,X5) = X4 & v3_pre_topc(X5,X1) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X1),X0,sK6(X0,X1,X4)) = X4 & v3_pre_topc(sK6(X0,X1,X4),X1) & m1_subset_1(sK6(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != X2 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X1),X0,X5) = X4 & v3_pre_topc(X5,X1) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 0.20/0.52    inference(rectify,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X1,X0)))),
% 0.20/0.52    inference(nnf_transformation,[],[f18])).
% 0.20/0.52  fof(f88,plain,(
% 0.20/0.52    ~m1_subset_1(sK6(sK3,sK2,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(k1_tarski(sK4),sK3) | ~m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.20/0.52    inference(subsumption_resolution,[],[f87,f64])).
% 0.20/0.52  fof(f87,plain,(
% 0.20/0.52    ~m1_subset_1(sK6(sK3,sK2,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(k1_tarski(sK4),sK3) | ~m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) | ~sP0(sK3,sK2)),
% 0.20/0.52    inference(resolution,[],[f86,f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X4,X0,X1] : (v3_pre_topc(sK6(X0,X1,X4),X1) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~sP0(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f30])).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    ~v3_pre_topc(sK6(sK3,sK2,k1_tarski(sK4)),sK2) | ~m1_subset_1(sK6(sK3,sK2,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f84])).
% 0.20/0.52  fof(f84,plain,(
% 0.20/0.52    k1_tarski(sK4) != k1_tarski(sK4) | ~v3_pre_topc(sK6(sK3,sK2,k1_tarski(sK4)),sK2) | ~m1_subset_1(sK6(sK3,sK2,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.20/0.52    inference(superposition,[],[f37,f83])).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    k1_tarski(sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k1_tarski(sK4)))),
% 0.20/0.52    inference(resolution,[],[f80,f36])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    ( ! [X2] : (~r2_hidden(X2,sK3) | k1_tarski(sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k1_tarski(sK4)))) )),
% 0.20/0.52    inference(resolution,[],[f78,f33])).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k1_tarski(sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k1_tarski(sK4))) | ~r2_hidden(X1,X0)) )),
% 0.20/0.52    inference(resolution,[],[f77,f53])).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    v1_xboole_0(u1_struct_0(sK2)) | k1_tarski(sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k1_tarski(sK4)))),
% 0.20/0.52    inference(subsumption_resolution,[],[f74,f64])).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    ~sP0(sK3,sK2) | k1_tarski(sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k1_tarski(sK4))) | v1_xboole_0(u1_struct_0(sK2))),
% 0.20/0.52    inference(resolution,[],[f73,f36])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(sK4,X0) | ~sP0(X0,sK2) | k1_tarski(sK4) = k9_subset_1(u1_struct_0(sK2),X0,sK6(X0,sK2,k1_tarski(sK4))) | v1_xboole_0(u1_struct_0(sK2))) )),
% 0.20/0.52    inference(resolution,[],[f72,f55])).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,u1_struct_0(X1)) | ~sP0(X2,X1) | ~r2_hidden(X0,X2) | k1_tarski(X0) = k9_subset_1(u1_struct_0(X1),X2,sK6(X2,X1,k1_tarski(X0)))) )),
% 0.20/0.52    inference(resolution,[],[f70,f49])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(k1_tarski(X2),k1_zfmisc_1(u1_struct_0(X0))) | k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,sK6(X1,X0,k1_tarski(X2))) | ~sP0(X1,X0) | ~r2_hidden(X2,X1)) )),
% 0.20/0.52    inference(resolution,[],[f43,f52])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ( ! [X4,X0,X1] : (~r1_tarski(X4,X0) | k9_subset_1(u1_struct_0(X1),X0,sK6(X0,X1,X4)) = X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~sP0(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f30])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X3] : (k9_subset_1(u1_struct_0(sK2),sK3,X3) != k1_tarski(sK4) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    r2_hidden(sK4,sK3)),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (29030)------------------------------
% 0.20/0.52  % (29030)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (29030)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (29030)Memory used [KB]: 6396
% 0.20/0.52  % (29030)Time elapsed: 0.098 s
% 0.20/0.52  % (29030)------------------------------
% 0.20/0.52  % (29030)------------------------------
% 0.20/0.52  % (29040)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.52  % (29022)Success in time 0.161 s
%------------------------------------------------------------------------------
