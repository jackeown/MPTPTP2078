%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 301 expanded)
%              Number of leaves         :   13 ( 109 expanded)
%              Depth                    :   33
%              Number of atoms          :  297 (2054 expanded)
%              Number of equality atoms :   36 ( 265 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f121,plain,(
    $false ),
    inference(subsumption_resolution,[],[f35,f118])).

fof(f118,plain,(
    ! [X4] : ~ r2_hidden(X4,sK3) ),
    inference(resolution,[],[f114,f32])).

fof(f32,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ! [X3] :
        ( k9_subset_1(u1_struct_0(sK2),sK3,X3) != k1_tarski(sK4)
        | ~ v3_pre_topc(X3,sK2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
    & r2_hidden(sK4,sK3)
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & v2_tex_2(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f10,f22,f21,f20])).

fof(f20,plain,
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

fof(f21,plain,
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

fof(f22,plain,
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
    inference(flattening,[],[f9])).

% (12629)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f9,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tex_2)).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f113,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f113,plain,(
    v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f58,f111])).

fof(f111,plain,(
    ~ r2_hidden(sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f110,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(f110,plain,(
    ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f109,f35])).

fof(f109,plain,
    ( ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK4,sK3) ),
    inference(resolution,[],[f108,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f47,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f108,plain,
    ( ~ r1_tarski(k1_tarski(sK4),sK3)
    | ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f107,f67])).

fof(f67,plain,(
    sP0(sK3,sK2) ),
    inference(subsumption_resolution,[],[f66,f33])).

fof(f33,plain,(
    v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f66,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | sP0(sK3,sK2) ),
    inference(resolution,[],[f64,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ v2_tex_2(X1,X0)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( v2_tex_2(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v2_tex_2(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v2_tex_2(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

% (12607)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f64,plain,(
    sP1(sK2,sK3) ),
    inference(resolution,[],[f61,f32])).

fof(f61,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(sK2,X0) ) ),
    inference(resolution,[],[f46,f31])).

fof(f31,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f12,f18,f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

fof(f107,plain,
    ( ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(k1_tarski(sK4),sK3)
    | ~ sP0(sK3,sK2) ),
    inference(duplicate_literal_removal,[],[f105])).

fof(f105,plain,
    ( ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(k1_tarski(sK4),sK3)
    | ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ sP0(sK3,sK2) ),
    inference(resolution,[],[f104,f40])).

fof(f40,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tarski(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f26,f28,f27])).

fof(f27,plain,(
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

fof(f28,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X1),X0,X5) = X4
          & v3_pre_topc(X5,X1)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X1),X0,sK6(X0,X1,X4)) = X4
        & v3_pre_topc(sK6(X0,X1,X4),X1)
        & m1_subset_1(sK6(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f104,plain,
    ( ~ m1_subset_1(sK6(sK3,sK2,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f103,f35])).

fof(f103,plain,
    ( ~ m1_subset_1(sK6(sK3,sK2,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK4,sK3) ),
    inference(resolution,[],[f102,f54])).

fof(f102,plain,
    ( ~ r1_tarski(k1_tarski(sK4),sK3)
    | ~ m1_subset_1(sK6(sK3,sK2,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f101,f67])).

fof(f101,plain,
    ( ~ m1_subset_1(sK6(sK3,sK2,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(k1_tarski(sK4),sK3)
    | ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ sP0(sK3,sK2) ),
    inference(resolution,[],[f100,f41])).

fof(f41,plain,(
    ! [X4,X0,X1] :
      ( v3_pre_topc(sK6(X0,X1,X4),X1)
      | ~ r1_tarski(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f100,plain,
    ( ~ v3_pre_topc(sK6(sK3,sK2,k1_tarski(sK4)),sK2)
    | ~ m1_subset_1(sK6(sK3,sK2,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(trivial_inequality_removal,[],[f98])).

fof(f98,plain,
    ( k1_tarski(sK4) != k1_tarski(sK4)
    | ~ v3_pre_topc(sK6(sK3,sK2,k1_tarski(sK4)),sK2)
    | ~ m1_subset_1(sK6(sK3,sK2,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(superposition,[],[f36,f97])).

% (12621)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f97,plain,(
    k1_tarski(sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k1_tarski(sK4))) ),
    inference(resolution,[],[f94,f35])).

fof(f94,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK3)
      | k1_tarski(sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k1_tarski(sK4))) ) ),
    inference(resolution,[],[f90,f32])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k1_tarski(sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k1_tarski(sK4)))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f89,f51])).

fof(f89,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | k1_tarski(sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k1_tarski(sK4))) ),
    inference(resolution,[],[f87,f58])).

fof(f87,plain,
    ( ~ r2_hidden(sK4,u1_struct_0(sK2))
    | k1_tarski(sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k1_tarski(sK4))) ),
    inference(resolution,[],[f86,f47])).

fof(f86,plain,
    ( ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tarski(sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k1_tarski(sK4))) ),
    inference(resolution,[],[f84,f35])).

fof(f84,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | k1_tarski(X0) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k1_tarski(X0)))
      | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f80,f54])).

fof(f80,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,X0)) = X0 ) ),
    inference(resolution,[],[f42,f67])).

fof(f42,plain,(
    ! [X4,X0,X1] :
      ( ~ sP0(X0,X1)
      | ~ r1_tarski(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | k9_subset_1(u1_struct_0(X1),X0,sK6(X0,X1,X4)) = X4 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f36,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK2),sK3,X3) != k1_tarski(sK4)
      | ~ v3_pre_topc(X3,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f58,plain,
    ( r2_hidden(sK4,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f48,f34])).

fof(f34,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f35,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:31:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.51  % (12611)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (12615)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (12616)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (12622)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (12610)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (12630)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (12614)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (12617)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (12617)Refutation not found, incomplete strategy% (12617)------------------------------
% 0.21/0.53  % (12617)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (12614)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f35,f118])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    ( ! [X4] : (~r2_hidden(X4,sK3)) )),
% 0.21/0.53    inference(resolution,[],[f114,f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ((! [X3] : (k9_subset_1(u1_struct_0(sK2),sK3,X3) != k1_tarski(sK4) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(sK4,sK3) & m1_subset_1(sK4,u1_struct_0(sK2))) & v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f10,f22,f21,f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),X1,X3) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK2))) & v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),X1,X3) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK2))) & v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) => (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),sK3,X3) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(X2,sK3) & m1_subset_1(X2,u1_struct_0(sK2))) & v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),sK3,X3) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(X2,sK3) & m1_subset_1(X2,u1_struct_0(sK2))) => (! [X3] : (k9_subset_1(u1_struct_0(sK2),sK3,X3) != k1_tarski(sK4) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(sK4,sK3) & m1_subset_1(sK4,u1_struct_0(sK2)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f9])).
% 0.21/0.53  % (12629)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  fof(f9,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : ((? [X2] : ((! [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,negated_conjecture,(
% 0.21/0.53    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 0.21/0.53    inference(negated_conjecture,[],[f7])).
% 0.21/0.53  fof(f7,conjecture,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tex_2)).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~r2_hidden(X1,X0)) )),
% 0.21/0.53    inference(resolution,[],[f113,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    v1_xboole_0(u1_struct_0(sK2))),
% 0.21/0.53    inference(subsumption_resolution,[],[f58,f111])).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    ~r2_hidden(sK4,u1_struct_0(sK2))),
% 0.21/0.53    inference(resolution,[],[f110,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    ~m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f109,f35])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    ~m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) | ~r2_hidden(sK4,sK3)),
% 0.21/0.53    inference(resolution,[],[f108,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(resolution,[],[f47,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.53    inference(nnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    ~r1_tarski(k1_tarski(sK4),sK3) | ~m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f107,f67])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    sP0(sK3,sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f66,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    v2_tex_2(sK3,sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ~v2_tex_2(sK3,sK2) | sP0(sK3,sK2)),
% 0.21/0.53    inference(resolution,[],[f64,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~sP1(X0,X1) | ~v2_tex_2(X1,X0) | sP0(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1] : (((v2_tex_2(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v2_tex_2(X1,X0))) | ~sP1(X0,X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1] : ((v2_tex_2(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.53  % (12607)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    sP1(sK2,sK3)),
% 0.21/0.53    inference(resolution,[],[f61,f32])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(sK2,X0)) )),
% 0.21/0.53    inference(resolution,[],[f46,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    l1_pre_topc(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(definition_folding,[],[f12,f18,f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    ~m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(k1_tarski(sK4),sK3) | ~sP0(sK3,sK2)),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f105])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    ~m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(k1_tarski(sK4),sK3) | ~m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) | ~sP0(sK3,sK2)),
% 0.21/0.53    inference(resolution,[],[f104,f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X4,X0,X1] : (m1_subset_1(sK6(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1))) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~sP0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1] : ((sP0(X0,X1) | (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != sK5(X0,X1) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(sK5(X0,X1),X0) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X1),X0,sK6(X0,X1,X4)) = X4 & v3_pre_topc(sK6(X0,X1,X4),X1) & m1_subset_1(sK6(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f26,f28,f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != X2 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != sK5(X0,X1) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(sK5(X0,X1),X0) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X1),X0,X5) = X4 & v3_pre_topc(X5,X1) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X1),X0,sK6(X0,X1,X4)) = X4 & v3_pre_topc(sK6(X0,X1,X4),X1) & m1_subset_1(sK6(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != X2 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X1),X0,X5) = X4 & v3_pre_topc(X5,X1) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 0.21/0.53    inference(rectify,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X1,X0)))),
% 0.21/0.53    inference(nnf_transformation,[],[f17])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    ~m1_subset_1(sK6(sK3,sK2,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f103,f35])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    ~m1_subset_1(sK6(sK3,sK2,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) | ~r2_hidden(sK4,sK3)),
% 0.21/0.53    inference(resolution,[],[f102,f54])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    ~r1_tarski(k1_tarski(sK4),sK3) | ~m1_subset_1(sK6(sK3,sK2,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f101,f67])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    ~m1_subset_1(sK6(sK3,sK2,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(k1_tarski(sK4),sK3) | ~m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) | ~sP0(sK3,sK2)),
% 0.21/0.53    inference(resolution,[],[f100,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X4,X0,X1] : (v3_pre_topc(sK6(X0,X1,X4),X1) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~sP0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    ~v3_pre_topc(sK6(sK3,sK2,k1_tarski(sK4)),sK2) | ~m1_subset_1(sK6(sK3,sK2,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f98])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    k1_tarski(sK4) != k1_tarski(sK4) | ~v3_pre_topc(sK6(sK3,sK2,k1_tarski(sK4)),sK2) | ~m1_subset_1(sK6(sK3,sK2,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.53    inference(superposition,[],[f36,f97])).
% 0.21/0.53  % (12621)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    k1_tarski(sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k1_tarski(sK4)))),
% 0.21/0.53    inference(resolution,[],[f94,f35])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    ( ! [X4] : (~r2_hidden(X4,sK3) | k1_tarski(sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k1_tarski(sK4)))) )),
% 0.21/0.53    inference(resolution,[],[f90,f32])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k1_tarski(sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k1_tarski(sK4))) | ~r2_hidden(X1,X0)) )),
% 0.21/0.53    inference(resolution,[],[f89,f51])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    v1_xboole_0(u1_struct_0(sK2)) | k1_tarski(sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k1_tarski(sK4)))),
% 0.21/0.53    inference(resolution,[],[f87,f58])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    ~r2_hidden(sK4,u1_struct_0(sK2)) | k1_tarski(sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k1_tarski(sK4)))),
% 0.21/0.53    inference(resolution,[],[f86,f47])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    ~m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) | k1_tarski(sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k1_tarski(sK4)))),
% 0.21/0.53    inference(resolution,[],[f84,f35])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,sK3) | k1_tarski(X0) = k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,k1_tarski(X0))) | ~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.21/0.53    inference(resolution,[],[f80,f54])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k9_subset_1(u1_struct_0(sK2),sK3,sK6(sK3,sK2,X0)) = X0) )),
% 0.21/0.53    inference(resolution,[],[f42,f67])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X4,X0,X1] : (~sP0(X0,X1) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | k9_subset_1(u1_struct_0(X1),X0,sK6(X0,X1,X4)) = X4) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X3] : (k9_subset_1(u1_struct_0(sK2),sK3,X3) != k1_tarski(sK4) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    r2_hidden(sK4,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2))),
% 0.21/0.53    inference(resolution,[],[f48,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    m1_subset_1(sK4,u1_struct_0(sK2))),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.53    inference(flattening,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    r2_hidden(sK4,sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (12614)------------------------------
% 0.21/0.53  % (12614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (12624)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (12614)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (12614)Memory used [KB]: 6396
% 0.21/0.53  % (12614)Time elapsed: 0.118 s
% 0.21/0.53  % (12614)------------------------------
% 0.21/0.53  % (12614)------------------------------
% 0.21/0.53  % (12606)Success in time 0.169 s
%------------------------------------------------------------------------------
