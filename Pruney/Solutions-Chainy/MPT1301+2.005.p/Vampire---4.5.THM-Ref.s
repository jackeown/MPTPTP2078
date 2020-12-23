%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 137 expanded)
%              Number of leaves         :   10 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :  209 ( 729 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f74,plain,(
    $false ),
    inference(subsumption_resolution,[],[f73,f61])).

fof(f61,plain,(
    ~ sP0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f59,f33])).

fof(f33,plain,(
    ~ v2_tops_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ v2_tops_2(sK3,sK2)
    & v2_tops_2(sK4,sK2)
    & r1_tarski(sK3,sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f8,f18,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tops_2(X1,X0)
                & v2_tops_2(X2,X0)
                & r1_tarski(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(X1,sK2)
              & v2_tops_2(X2,sK2)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_tops_2(X1,sK2)
            & v2_tops_2(X2,sK2)
            & r1_tarski(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
   => ( ? [X2] :
          ( ~ v2_tops_2(sK3,sK2)
          & v2_tops_2(X2,sK2)
          & r1_tarski(sK3,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2] :
        ( ~ v2_tops_2(sK3,sK2)
        & v2_tops_2(X2,sK2)
        & r1_tarski(sK3,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
   => ( ~ v2_tops_2(sK3,sK2)
      & v2_tops_2(sK4,sK2)
      & r1_tarski(sK3,sK4)
      & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(X1,X0)
              & v2_tops_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(X1,X0)
              & v2_tops_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( ( v2_tops_2(X2,X0)
                    & r1_tarski(X1,X2) )
                 => v2_tops_2(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v2_tops_2(X2,X0)
                  & r1_tarski(X1,X2) )
               => v2_tops_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tops_2)).

fof(f59,plain,
    ( ~ sP0(sK2,sK3)
    | v2_tops_2(sK3,sK2) ),
    inference(resolution,[],[f57,f35])).

% (16089)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
fof(f35,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X1,X0)
      | v2_tops_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( v2_tops_2(X0,X1)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v2_tops_2(X0,X1) ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ( ( v2_tops_2(X1,X0)
          | ~ sP0(X0,X1) )
        & ( sP0(X0,X1)
          | ~ v2_tops_2(X1,X0) ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ( v2_tops_2(X1,X0)
      <=> sP0(X0,X1) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f57,plain,(
    sP1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f55,f28])).

fof(f28,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f55,plain,
    ( sP1(sK3,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f40,f29])).

fof(f29,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | sP1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f10,f14,f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( v4_pre_topc(X2,X0)
          | ~ r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_2)).

fof(f73,plain,(
    sP0(sK2,sK3) ),
    inference(resolution,[],[f71,f64])).

fof(f64,plain,(
    sP0(sK2,sK4) ),
    inference(subsumption_resolution,[],[f63,f32])).

fof(f32,plain,(
    v2_tops_2(sK4,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f63,plain,
    ( ~ v2_tops_2(sK4,sK2)
    | sP0(sK2,sK4) ),
    inference(resolution,[],[f58,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ v2_tops_2(X0,X1)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f58,plain,(
    sP1(sK4,sK2) ),
    inference(subsumption_resolution,[],[f56,f28])).

fof(f56,plain,
    ( sP1(sK4,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f40,f30])).

fof(f30,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f71,plain,(
    ! [X2] :
      ( ~ sP0(X2,sK4)
      | sP0(X2,sK3) ) ),
    inference(duplicate_literal_removal,[],[f70])).

fof(f70,plain,(
    ! [X2] :
      ( ~ sP0(X2,sK4)
      | sP0(X2,sK3)
      | sP0(X2,sK3) ) ),
    inference(resolution,[],[f68,f52])).

fof(f52,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0,sK3),sK4)
      | sP0(X0,sK3) ) ),
    inference(resolution,[],[f50,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ~ v4_pre_topc(sK5(X0,X1),X0)
          & r2_hidden(sK5(X0,X1),X1)
          & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( v4_pre_topc(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v4_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK5(X0,X1),X0)
        & r2_hidden(sK5(X0,X1),X1)
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ~ v4_pre_topc(X2,X0)
            & r2_hidden(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( v4_pre_topc(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ~ v4_pre_topc(X2,X0)
            & r2_hidden(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( v4_pre_topc(X2,X0)
            | ~ r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f50,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | r2_hidden(X0,sK4) ) ),
    inference(resolution,[],[f49,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f49,plain,(
    ! [X0] :
      ( r1_tarski(k1_tarski(X0),sK4)
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f47,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f47,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK3)
      | r1_tarski(X0,sK4) ) ),
    inference(resolution,[],[f45,f31])).

fof(f31,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X2)
      | ~ sP0(X0,X2)
      | sP0(X0,X1) ) ),
    inference(subsumption_resolution,[],[f67,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(sK5(X0,X1),X0)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X2)
      | v4_pre_topc(sK5(X0,X1),X0)
      | ~ sP0(X0,X2)
      | sP0(X0,X1) ) ),
    inference(resolution,[],[f36,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X3,X1)
      | v4_pre_topc(X3,X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:42:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (16087)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.46  % (16087)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f74,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(subsumption_resolution,[],[f73,f61])).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    ~sP0(sK2,sK3)),
% 0.21/0.46    inference(subsumption_resolution,[],[f59,f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ~v2_tops_2(sK3,sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ((~v2_tops_2(sK3,sK2) & v2_tops_2(sK4,sK2) & r1_tarski(sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & l1_pre_topc(sK2)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f8,f18,f17,f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(X1,X0) & v2_tops_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tops_2(X1,sK2) & v2_tops_2(X2,sK2) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & l1_pre_topc(sK2))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ? [X1] : (? [X2] : (~v2_tops_2(X1,sK2) & v2_tops_2(X2,sK2) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) => (? [X2] : (~v2_tops_2(sK3,sK2) & v2_tops_2(X2,sK2) & r1_tarski(sK3,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ? [X2] : (~v2_tops_2(sK3,sK2) & v2_tops_2(X2,sK2) & r1_tarski(sK3,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) => (~v2_tops_2(sK3,sK2) & v2_tops_2(sK4,sK2) & r1_tarski(sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(X1,X0) & v2_tops_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.21/0.46    inference(flattening,[],[f7])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : ((~v2_tops_2(X1,X0) & (v2_tops_2(X2,X0) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,negated_conjecture,(
% 0.21/0.46    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v2_tops_2(X2,X0) & r1_tarski(X1,X2)) => v2_tops_2(X1,X0)))))),
% 0.21/0.46    inference(negated_conjecture,[],[f5])).
% 0.21/0.46  fof(f5,conjecture,(
% 0.21/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v2_tops_2(X2,X0) & r1_tarski(X1,X2)) => v2_tops_2(X1,X0)))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tops_2)).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    ~sP0(sK2,sK3) | v2_tops_2(sK3,sK2)),
% 0.21/0.46    inference(resolution,[],[f57,f35])).
% 0.21/0.46  % (16089)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~sP1(X0,X1) | ~sP0(X1,X0) | v2_tops_2(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ! [X0,X1] : (((v2_tops_2(X0,X1) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v2_tops_2(X0,X1))) | ~sP1(X0,X1))),
% 0.21/0.46    inference(rectify,[],[f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ! [X1,X0] : (((v2_tops_2(X1,X0) | ~sP0(X0,X1)) & (sP0(X0,X1) | ~v2_tops_2(X1,X0))) | ~sP1(X1,X0))),
% 0.21/0.46    inference(nnf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X1,X0] : ((v2_tops_2(X1,X0) <=> sP0(X0,X1)) | ~sP1(X1,X0))),
% 0.21/0.46    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    sP1(sK3,sK2)),
% 0.21/0.46    inference(subsumption_resolution,[],[f55,f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    l1_pre_topc(sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    sP1(sK3,sK2) | ~l1_pre_topc(sK2)),
% 0.21/0.46    inference(resolution,[],[f40,f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | sP1(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (sP1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.46    inference(definition_folding,[],[f10,f14,f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.46    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> ! [X2] : (v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.46    inference(flattening,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> ! [X2] : ((v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v4_pre_topc(X2,X0))))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_2)).
% 0.21/0.46  fof(f73,plain,(
% 0.21/0.46    sP0(sK2,sK3)),
% 0.21/0.46    inference(resolution,[],[f71,f64])).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    sP0(sK2,sK4)),
% 0.21/0.46    inference(subsumption_resolution,[],[f63,f32])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    v2_tops_2(sK4,sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    ~v2_tops_2(sK4,sK2) | sP0(sK2,sK4)),
% 0.21/0.46    inference(resolution,[],[f58,f34])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~sP1(X0,X1) | ~v2_tops_2(X0,X1) | sP0(X1,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f21])).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    sP1(sK4,sK2)),
% 0.21/0.46    inference(subsumption_resolution,[],[f56,f28])).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    sP1(sK4,sK2) | ~l1_pre_topc(sK2)),
% 0.21/0.46    inference(resolution,[],[f40,f30])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    ( ! [X2] : (~sP0(X2,sK4) | sP0(X2,sK3)) )),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f70])).
% 0.21/0.46  fof(f70,plain,(
% 0.21/0.46    ( ! [X2] : (~sP0(X2,sK4) | sP0(X2,sK3) | sP0(X2,sK3)) )),
% 0.21/0.46    inference(resolution,[],[f68,f52])).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    ( ! [X0] : (r2_hidden(sK5(X0,sK3),sK4) | sP0(X0,sK3)) )),
% 0.21/0.46    inference(resolution,[],[f50,f38])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | sP0(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ! [X0,X1] : ((sP0(X0,X1) | (~v4_pre_topc(sK5(X0,X1),X0) & r2_hidden(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v4_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1)))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ! [X1,X0] : (? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v4_pre_topc(sK5(X0,X1),X0) & r2_hidden(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v4_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1)))),
% 0.21/0.46    inference(rectify,[],[f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1)))),
% 0.21/0.46    inference(nnf_transformation,[],[f13])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    ( ! [X0] : (~r2_hidden(X0,sK3) | r2_hidden(X0,sK4)) )),
% 0.21/0.46    inference(resolution,[],[f49,f41])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.46    inference(nnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    ( ! [X0] : (r1_tarski(k1_tarski(X0),sK4) | ~r2_hidden(X0,sK3)) )),
% 0.21/0.46    inference(resolution,[],[f47,f42])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f26])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    ( ! [X0] : (~r1_tarski(X0,sK3) | r1_tarski(X0,sK4)) )),
% 0.21/0.46    inference(resolution,[],[f45,f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    r1_tarski(sK3,sK4)),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.46    inference(flattening,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.46  fof(f68,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r2_hidden(sK5(X0,X1),X2) | ~sP0(X0,X2) | sP0(X0,X1)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f67,f39])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v4_pre_topc(sK5(X0,X1),X0) | sP0(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f25])).
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r2_hidden(sK5(X0,X1),X2) | v4_pre_topc(sK5(X0,X1),X0) | ~sP0(X0,X2) | sP0(X0,X1)) )),
% 0.21/0.46    inference(resolution,[],[f36,f37])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ( ! [X0,X1] : (m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | sP0(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f25])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X3,X1) | v4_pre_topc(X3,X0) | ~sP0(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f25])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (16087)------------------------------
% 0.21/0.46  % (16087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (16087)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (16087)Memory used [KB]: 5373
% 0.21/0.46  % (16087)Time elapsed: 0.058 s
% 0.21/0.46  % (16087)------------------------------
% 0.21/0.46  % (16087)------------------------------
% 0.21/0.46  % (16093)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.46  % (16079)Success in time 0.107 s
%------------------------------------------------------------------------------
