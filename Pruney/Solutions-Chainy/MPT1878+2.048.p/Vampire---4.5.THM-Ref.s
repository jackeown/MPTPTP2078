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
% DateTime   : Thu Dec  3 13:21:50 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 200 expanded)
%              Number of leaves         :   22 (  60 expanded)
%              Depth                    :   21
%              Number of atoms          :  379 ( 952 expanded)
%              Number of equality atoms :   58 (  80 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f199,plain,(
    $false ),
    inference(subsumption_resolution,[],[f198,f52])).

fof(f52,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( v3_tex_2(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & v1_xboole_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f42,f41])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v3_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( v3_tex_2(X1,sK2)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X1] :
        ( v3_tex_2(X1,sK2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        & v1_xboole_0(X1) )
   => ( v3_tex_2(sK3,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      & v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => ~ v3_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

fof(f198,plain,(
    v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f197,f84])).

fof(f84,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f62,f54])).

fof(f54,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f62,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f197,plain,
    ( ~ l1_struct_0(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f187,f88])).

fof(f88,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f55,f85])).

fof(f85,plain,(
    k1_xboole_0 = sK3 ),
    inference(resolution,[],[f72,f55])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f55,plain,(
    v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f187,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0(sK2)
    | v2_struct_0(sK2) ),
    inference(superposition,[],[f74,f182])).

fof(f182,plain,(
    k1_xboole_0 = u1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f181,f54])).

% (13402)Refutation not found, incomplete strategy% (13402)------------------------------
% (13402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f181,plain,
    ( k1_xboole_0 = u1_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f180,f52])).

fof(f180,plain,
    ( v2_struct_0(sK2)
    | k1_xboole_0 = u1_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f179,f53])).

fof(f53,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f179,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | k1_xboole_0 = u1_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f178,f101])).

fof(f101,plain,(
    sP0(k1_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f100,f54])).

fof(f100,plain,
    ( ~ l1_pre_topc(sK2)
    | sP0(k1_xboole_0,sK2) ),
    inference(resolution,[],[f96,f87])).

fof(f87,plain,(
    v3_tex_2(k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f57,f85])).

fof(f57,plain,(
    v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f96,plain,(
    ! [X1] :
      ( ~ v3_tex_2(k1_xboole_0,X1)
      | ~ l1_pre_topc(X1)
      | sP0(k1_xboole_0,X1) ) ),
    inference(resolution,[],[f93,f63])).

% (13401)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
fof(f63,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ v3_tex_2(X1,X0)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v3_tex_2(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v3_tex_2(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v3_tex_2(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f93,plain,(
    ! [X0] :
      ( sP1(X0,k1_xboole_0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f71,f59])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f23,f39,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ( ! [X2] :
            ( X1 = X2
            | ~ r1_tarski(X1,X2)
            | ~ v2_tex_2(X2,X0)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & v2_tex_2(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

% (13414)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

fof(f178,plain,(
    ! [X0] :
      ( ~ sP0(k1_xboole_0,X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k1_xboole_0 = u1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f177,f90])).

fof(f90,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f75,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f75,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5,X6] :
            ( r1_xboole_0(X2,X0)
            | ~ r2_hidden(X6,sK5(X0))
            | ~ r2_hidden(X5,X6)
            | ~ r2_hidden(X4,X5)
            | ~ r2_hidden(X3,X4)
            | ~ r2_hidden(X2,X3) )
        & r2_hidden(sK5(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
     => ( ! [X6,X5,X4,X3,X2] :
            ( r1_xboole_0(X2,X0)
            | ~ r2_hidden(X6,sK5(X0))
            | ~ r2_hidden(X5,X6)
            | ~ r2_hidden(X4,X5)
            | ~ r2_hidden(X3,X4)
            | ~ r2_hidden(X2,X3) )
        & r2_hidden(sK5(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

fof(f177,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k1_xboole_0 = u1_struct_0(X0)
      | ~ sP0(k1_xboole_0,X0)
      | ~ m1_subset_1(sK5(u1_struct_0(X0)),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f176])).

fof(f176,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k1_xboole_0 = u1_struct_0(X0)
      | ~ sP0(k1_xboole_0,X0)
      | k1_xboole_0 = u1_struct_0(X0)
      | ~ m1_subset_1(sK5(u1_struct_0(X0)),u1_struct_0(X0)) ) ),
    inference(resolution,[],[f118,f154])).

fof(f154,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(k1_tarski(X0),X1)
      | ~ sP0(k1_xboole_0,X1)
      | k1_xboole_0 = u1_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f144,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ( k1_xboole_0 != X0
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

fof(f144,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(k1_tarski(X6),k1_zfmisc_1(u1_struct_0(X7)))
      | ~ v2_tex_2(k1_tarski(X6),X7)
      | ~ sP0(k1_xboole_0,X7) ) ),
    inference(forward_demodulation,[],[f143,f61])).

fof(f61,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f143,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(k1_tarski(X6),k1_zfmisc_1(u1_struct_0(X7)))
      | ~ v2_tex_2(k5_xboole_0(k1_tarski(X6),k1_xboole_0),X7)
      | ~ sP0(k1_xboole_0,X7) ) ),
    inference(forward_demodulation,[],[f142,f61])).

fof(f142,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(k5_xboole_0(k1_tarski(X6),k1_xboole_0),k1_zfmisc_1(u1_struct_0(X7)))
      | ~ v2_tex_2(k5_xboole_0(k1_tarski(X6),k1_xboole_0),X7)
      | ~ sP0(k1_xboole_0,X7) ) ),
    inference(subsumption_resolution,[],[f129,f58])).

fof(f58,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f129,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(k5_xboole_0(k1_tarski(X6),k1_xboole_0),k1_zfmisc_1(u1_struct_0(X7)))
      | ~ r1_tarski(k1_xboole_0,k5_xboole_0(k1_tarski(X6),k1_xboole_0))
      | ~ v2_tex_2(k5_xboole_0(k1_tarski(X6),k1_xboole_0),X7)
      | ~ sP0(k1_xboole_0,X7) ) ),
    inference(extensionality_resolution,[],[f66,f91])).

fof(f91,plain,(
    ! [X0] : k1_xboole_0 != k5_xboole_0(k1_tarski(X0),k1_xboole_0) ),
    inference(superposition,[],[f83,f60])).

fof(f60,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f83,plain,(
    ! [X0,X1] : k1_xboole_0 != k5_xboole_0(k1_tarski(X0),k4_xboole_0(X1,k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f77,f78])).

fof(f78,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f77,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tarski(X0,X3)
      | ~ v2_tex_2(X3,X1)
      | X0 = X3
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( sK4(X0,X1) != X0
          & r1_tarski(X0,sK4(X0,X1))
          & v2_tex_2(sK4(X0,X1),X1)
          & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ v2_tex_2(X0,X1) )
      & ( ( ! [X3] :
              ( X0 = X3
              | ~ r1_tarski(X0,X3)
              | ~ v2_tex_2(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & v2_tex_2(X0,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f47,f48])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X0 != X2
          & r1_tarski(X0,X2)
          & v2_tex_2(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( sK4(X0,X1) != X0
        & r1_tarski(X0,sK4(X0,X1))
        & v2_tex_2(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( X0 != X2
            & r1_tarski(X0,X2)
            & v2_tex_2(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ v2_tex_2(X0,X1) )
      & ( ( ! [X3] :
              ( X0 = X3
              | ~ r1_tarski(X0,X3)
              | ~ v2_tex_2(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & v2_tex_2(X0,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( X1 != X2
            & r1_tarski(X1,X2)
            & v2_tex_2(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ v2_tex_2(X1,X0) )
      & ( ( ! [X2] :
              ( X1 = X2
              | ~ r1_tarski(X1,X2)
              | ~ v2_tex_2(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & v2_tex_2(X1,X0) )
        | ~ sP0(X1,X0) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( X1 != X2
            & r1_tarski(X1,X2)
            & v2_tex_2(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ v2_tex_2(X1,X0) )
      & ( ( ! [X2] :
              ( X1 = X2
              | ~ r1_tarski(X1,X2)
              | ~ v2_tex_2(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & v2_tex_2(X1,X0) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f118,plain,(
    ! [X0] :
      ( v2_tex_2(k1_tarski(sK5(u1_struct_0(X0))),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k1_xboole_0 = u1_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f117,f90])).

fof(f117,plain,(
    ! [X0] :
      ( v2_tex_2(k1_tarski(sK5(u1_struct_0(X0))),X0)
      | ~ m1_subset_1(sK5(u1_struct_0(X0)),u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k1_xboole_0 = u1_struct_0(X0) ) ),
    inference(superposition,[],[f73,f109])).

fof(f109,plain,(
    ! [X3] :
      ( k1_tarski(sK5(X3)) = k6_domain_1(X3,sK5(X3))
      | k1_xboole_0 = X3 ) ),
    inference(subsumption_resolution,[],[f108,f72])).

fof(f108,plain,(
    ! [X3] :
      ( k1_tarski(sK5(X3)) = k6_domain_1(X3,sK5(X3))
      | v1_xboole_0(X3)
      | k1_xboole_0 = X3 ) ),
    inference(resolution,[],[f81,f90])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k1_tarski(X1) = k6_domain_1(X0,X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f73,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:02:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (13400)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.51  % (13406)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.51  % (13413)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.52  % (13394)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (13400)Refutation not found, incomplete strategy% (13400)------------------------------
% 0.20/0.52  % (13400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (13392)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (13413)Refutation not found, incomplete strategy% (13413)------------------------------
% 0.20/0.52  % (13413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (13391)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (13413)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (13413)Memory used [KB]: 6268
% 0.20/0.53  % (13413)Time elapsed: 0.115 s
% 0.20/0.53  % (13413)------------------------------
% 0.20/0.53  % (13413)------------------------------
% 0.20/0.53  % (13400)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (13400)Memory used [KB]: 10746
% 0.20/0.53  % (13400)Time elapsed: 0.105 s
% 0.20/0.53  % (13400)------------------------------
% 0.20/0.53  % (13400)------------------------------
% 0.20/0.53  % (13394)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (13416)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.53  % (13415)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.53  % (13407)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.53  % (13390)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.54  % (13408)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (13398)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.54  % (13389)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.54  % (13415)Refutation not found, incomplete strategy% (13415)------------------------------
% 0.20/0.54  % (13415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (13409)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.54  % (13395)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.54  % (13402)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f199,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(subsumption_resolution,[],[f198,f52])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ~v2_struct_0(sK2)),
% 0.20/0.54    inference(cnf_transformation,[],[f43])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    (v3_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f42,f41])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (v3_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ? [X1] : (v3_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(X1)) => (v3_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(sK3))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.54    inference(flattening,[],[f19])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f18])).
% 0.20/0.54  fof(f18,negated_conjecture,(
% 0.20/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 0.20/0.54    inference(negated_conjecture,[],[f17])).
% 0.20/0.54  fof(f17,conjecture,(
% 0.20/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).
% 0.20/0.54  fof(f198,plain,(
% 0.20/0.54    v2_struct_0(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f197,f84])).
% 0.20/0.54  fof(f84,plain,(
% 0.20/0.54    l1_struct_0(sK2)),
% 0.20/0.54    inference(resolution,[],[f62,f54])).
% 0.20/0.54  fof(f54,plain,(
% 0.20/0.54    l1_pre_topc(sK2)),
% 0.20/0.54    inference(cnf_transformation,[],[f43])).
% 0.20/0.54  fof(f62,plain,(
% 0.20/0.54    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,axiom,(
% 0.20/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.54  fof(f197,plain,(
% 0.20/0.54    ~l1_struct_0(sK2) | v2_struct_0(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f187,f88])).
% 0.20/0.54  fof(f88,plain,(
% 0.20/0.54    v1_xboole_0(k1_xboole_0)),
% 0.20/0.54    inference(backward_demodulation,[],[f55,f85])).
% 0.20/0.54  fof(f85,plain,(
% 0.20/0.54    k1_xboole_0 = sK3),
% 0.20/0.54    inference(resolution,[],[f72,f55])).
% 0.20/0.54  fof(f72,plain,(
% 0.20/0.54    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    v1_xboole_0(sK3)),
% 0.20/0.54    inference(cnf_transformation,[],[f43])).
% 0.20/0.54  fof(f187,plain,(
% 0.20/0.54    ~v1_xboole_0(k1_xboole_0) | ~l1_struct_0(sK2) | v2_struct_0(sK2)),
% 0.20/0.54    inference(superposition,[],[f74,f182])).
% 0.20/0.54  fof(f182,plain,(
% 0.20/0.54    k1_xboole_0 = u1_struct_0(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f181,f54])).
% 0.20/0.54  % (13402)Refutation not found, incomplete strategy% (13402)------------------------------
% 0.20/0.54  % (13402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  fof(f181,plain,(
% 0.20/0.54    k1_xboole_0 = u1_struct_0(sK2) | ~l1_pre_topc(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f180,f52])).
% 0.20/0.54  fof(f180,plain,(
% 0.20/0.54    v2_struct_0(sK2) | k1_xboole_0 = u1_struct_0(sK2) | ~l1_pre_topc(sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f179,f53])).
% 0.20/0.54  fof(f53,plain,(
% 0.20/0.54    v2_pre_topc(sK2)),
% 0.20/0.54    inference(cnf_transformation,[],[f43])).
% 0.20/0.54  fof(f179,plain,(
% 0.20/0.54    ~v2_pre_topc(sK2) | v2_struct_0(sK2) | k1_xboole_0 = u1_struct_0(sK2) | ~l1_pre_topc(sK2)),
% 0.20/0.54    inference(resolution,[],[f178,f101])).
% 0.20/0.54  fof(f101,plain,(
% 0.20/0.54    sP0(k1_xboole_0,sK2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f100,f54])).
% 0.20/0.54  fof(f100,plain,(
% 0.20/0.54    ~l1_pre_topc(sK2) | sP0(k1_xboole_0,sK2)),
% 0.20/0.54    inference(resolution,[],[f96,f87])).
% 0.20/0.54  fof(f87,plain,(
% 0.20/0.54    v3_tex_2(k1_xboole_0,sK2)),
% 0.20/0.54    inference(backward_demodulation,[],[f57,f85])).
% 0.20/0.54  fof(f57,plain,(
% 0.20/0.54    v3_tex_2(sK3,sK2)),
% 0.20/0.54    inference(cnf_transformation,[],[f43])).
% 0.20/0.54  fof(f96,plain,(
% 0.20/0.54    ( ! [X1] : (~v3_tex_2(k1_xboole_0,X1) | ~l1_pre_topc(X1) | sP0(k1_xboole_0,X1)) )),
% 0.20/0.54    inference(resolution,[],[f93,f63])).
% 0.20/0.55  % (13401)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.55  fof(f63,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~sP1(X0,X1) | ~v3_tex_2(X1,X0) | sP0(X1,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f44])).
% 0.20/0.55  fof(f44,plain,(
% 0.20/0.55    ! [X0,X1] : (((v3_tex_2(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v3_tex_2(X1,X0))) | ~sP1(X0,X1))),
% 0.20/0.55    inference(nnf_transformation,[],[f39])).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    ! [X0,X1] : ((v3_tex_2(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 0.20/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.55  fof(f93,plain,(
% 0.20/0.55    ( ! [X0] : (sP1(X0,k1_xboole_0) | ~l1_pre_topc(X0)) )),
% 0.20/0.55    inference(resolution,[],[f71,f59])).
% 0.20/0.55  fof(f59,plain,(
% 0.20/0.55    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f7])).
% 0.20/0.55  fof(f7,axiom,(
% 0.20/0.55    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.55  fof(f71,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f40])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(definition_folding,[],[f23,f39,f38])).
% 0.20/0.55  fof(f38,plain,(
% 0.20/0.55    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)))),
% 0.20/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.55  % (13414)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(flattening,[],[f22])).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f15])).
% 0.20/0.55  fof(f15,axiom,(
% 0.20/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).
% 0.20/0.55  fof(f178,plain,(
% 0.20/0.55    ( ! [X0] : (~sP0(k1_xboole_0,X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k1_xboole_0 = u1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f177,f90])).
% 0.20/0.55  fof(f90,plain,(
% 0.20/0.55    ( ! [X0] : (m1_subset_1(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(resolution,[],[f75,f79])).
% 0.20/0.55  fof(f79,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f31])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,axiom,(
% 0.20/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.55  fof(f75,plain,(
% 0.20/0.55    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f51])).
% 0.20/0.55  fof(f51,plain,(
% 0.20/0.55    ! [X0] : ((! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,sK5(X0)) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(sK5(X0),X0)) | k1_xboole_0 = X0)),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f50])).
% 0.20/0.55  fof(f50,plain,(
% 0.20/0.55    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(X1,X0)) => (! [X6,X5,X4,X3,X2] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,sK5(X0)) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(sK5(X0),X0)))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.20/0.55    inference(flattening,[],[f29])).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | (~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.20/0.55    inference(ennf_transformation,[],[f11])).
% 0.20/0.55  fof(f11,axiom,(
% 0.20/0.55    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).
% 0.20/0.55  fof(f177,plain,(
% 0.20/0.55    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k1_xboole_0 = u1_struct_0(X0) | ~sP0(k1_xboole_0,X0) | ~m1_subset_1(sK5(u1_struct_0(X0)),u1_struct_0(X0))) )),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f176])).
% 0.20/0.55  fof(f176,plain,(
% 0.20/0.55    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k1_xboole_0 = u1_struct_0(X0) | ~sP0(k1_xboole_0,X0) | k1_xboole_0 = u1_struct_0(X0) | ~m1_subset_1(sK5(u1_struct_0(X0)),u1_struct_0(X0))) )),
% 0.20/0.55    inference(resolution,[],[f118,f154])).
% 0.20/0.55  fof(f154,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~v2_tex_2(k1_tarski(X0),X1) | ~sP0(k1_xboole_0,X1) | k1_xboole_0 = u1_struct_0(X1) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.20/0.55    inference(resolution,[],[f144,f80])).
% 0.20/0.55  fof(f80,plain,(
% 0.20/0.55    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f33])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0))),
% 0.20/0.55    inference(flattening,[],[f32])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    ! [X0,X1] : ((m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X1,X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f8])).
% 0.20/0.55  fof(f8,axiom,(
% 0.20/0.55    ! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).
% 0.20/0.55  fof(f144,plain,(
% 0.20/0.55    ( ! [X6,X7] : (~m1_subset_1(k1_tarski(X6),k1_zfmisc_1(u1_struct_0(X7))) | ~v2_tex_2(k1_tarski(X6),X7) | ~sP0(k1_xboole_0,X7)) )),
% 0.20/0.55    inference(forward_demodulation,[],[f143,f61])).
% 0.20/0.55  fof(f61,plain,(
% 0.20/0.55    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.20/0.55  fof(f143,plain,(
% 0.20/0.55    ( ! [X6,X7] : (~m1_subset_1(k1_tarski(X6),k1_zfmisc_1(u1_struct_0(X7))) | ~v2_tex_2(k5_xboole_0(k1_tarski(X6),k1_xboole_0),X7) | ~sP0(k1_xboole_0,X7)) )),
% 0.20/0.55    inference(forward_demodulation,[],[f142,f61])).
% 0.20/0.55  fof(f142,plain,(
% 0.20/0.55    ( ! [X6,X7] : (~m1_subset_1(k5_xboole_0(k1_tarski(X6),k1_xboole_0),k1_zfmisc_1(u1_struct_0(X7))) | ~v2_tex_2(k5_xboole_0(k1_tarski(X6),k1_xboole_0),X7) | ~sP0(k1_xboole_0,X7)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f129,f58])).
% 0.20/0.55  fof(f58,plain,(
% 0.20/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.55  fof(f129,plain,(
% 0.20/0.55    ( ! [X6,X7] : (~m1_subset_1(k5_xboole_0(k1_tarski(X6),k1_xboole_0),k1_zfmisc_1(u1_struct_0(X7))) | ~r1_tarski(k1_xboole_0,k5_xboole_0(k1_tarski(X6),k1_xboole_0)) | ~v2_tex_2(k5_xboole_0(k1_tarski(X6),k1_xboole_0),X7) | ~sP0(k1_xboole_0,X7)) )),
% 0.20/0.55    inference(extensionality_resolution,[],[f66,f91])).
% 0.20/0.55  fof(f91,plain,(
% 0.20/0.55    ( ! [X0] : (k1_xboole_0 != k5_xboole_0(k1_tarski(X0),k1_xboole_0)) )),
% 0.20/0.55    inference(superposition,[],[f83,f60])).
% 0.20/0.55  fof(f60,plain,(
% 0.20/0.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.20/0.55  fof(f83,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(k1_tarski(X0),k4_xboole_0(X1,k1_tarski(X0)))) )),
% 0.20/0.55    inference(definition_unfolding,[],[f77,f78])).
% 0.20/0.55  fof(f78,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f5])).
% 0.20/0.55  fof(f5,axiom,(
% 0.20/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.55  fof(f77,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.20/0.55  fof(f66,plain,(
% 0.20/0.55    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | X0 = X3 | ~sP0(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f49])).
% 0.20/0.55  fof(f49,plain,(
% 0.20/0.55    ! [X0,X1] : ((sP0(X0,X1) | (sK4(X0,X1) != X0 & r1_tarski(X0,sK4(X0,X1)) & v2_tex_2(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_tex_2(X0,X1)) & ((! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_tex_2(X0,X1)) | ~sP0(X0,X1)))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f47,f48])).
% 0.20/0.55  fof(f48,plain,(
% 0.20/0.55    ! [X1,X0] : (? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (sK4(X0,X1) != X0 & r1_tarski(X0,sK4(X0,X1)) & v2_tex_2(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f47,plain,(
% 0.20/0.55    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_tex_2(X0,X1)) & ((! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_tex_2(X0,X1)) | ~sP0(X0,X1)))),
% 0.20/0.55    inference(rectify,[],[f46])).
% 0.20/0.55  fof(f46,plain,(
% 0.20/0.55    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~sP0(X1,X0)))),
% 0.20/0.55    inference(flattening,[],[f45])).
% 0.20/0.55  fof(f45,plain,(
% 0.20/0.55    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~sP0(X1,X0)))),
% 0.20/0.55    inference(nnf_transformation,[],[f38])).
% 0.20/0.55  fof(f118,plain,(
% 0.20/0.55    ( ! [X0] : (v2_tex_2(k1_tarski(sK5(u1_struct_0(X0))),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k1_xboole_0 = u1_struct_0(X0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f117,f90])).
% 0.20/0.55  fof(f117,plain,(
% 0.20/0.55    ( ! [X0] : (v2_tex_2(k1_tarski(sK5(u1_struct_0(X0))),X0) | ~m1_subset_1(sK5(u1_struct_0(X0)),u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k1_xboole_0 = u1_struct_0(X0)) )),
% 0.20/0.55    inference(superposition,[],[f73,f109])).
% 0.20/0.55  fof(f109,plain,(
% 0.20/0.55    ( ! [X3] : (k1_tarski(sK5(X3)) = k6_domain_1(X3,sK5(X3)) | k1_xboole_0 = X3) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f108,f72])).
% 0.20/0.55  fof(f108,plain,(
% 0.20/0.55    ( ! [X3] : (k1_tarski(sK5(X3)) = k6_domain_1(X3,sK5(X3)) | v1_xboole_0(X3) | k1_xboole_0 = X3) )),
% 0.20/0.55    inference(resolution,[],[f81,f90])).
% 0.20/0.55  fof(f81,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k1_tarski(X1) = k6_domain_1(X0,X1) | v1_xboole_0(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f35])).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.55    inference(flattening,[],[f34])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f14])).
% 0.20/0.55  fof(f14,axiom,(
% 0.20/0.55    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.55  fof(f73,plain,(
% 0.20/0.55    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.55    inference(flattening,[],[f25])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f16])).
% 0.20/0.55  fof(f16,axiom,(
% 0.20/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).
% 0.20/0.55  fof(f74,plain,(
% 0.20/0.55    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f28])).
% 0.20/0.55  fof(f28,plain,(
% 0.20/0.55    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.55    inference(flattening,[],[f27])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f13])).
% 0.20/0.55  fof(f13,axiom,(
% 0.20/0.55    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (13394)------------------------------
% 0.20/0.55  % (13394)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (13394)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (13394)Memory used [KB]: 10874
% 0.20/0.55  % (13394)Time elapsed: 0.111 s
% 0.20/0.55  % (13394)------------------------------
% 0.20/0.55  % (13394)------------------------------
% 0.20/0.55  % (13414)Refutation not found, incomplete strategy% (13414)------------------------------
% 0.20/0.55  % (13414)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (13414)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (13414)Memory used [KB]: 6268
% 0.20/0.55  % (13414)Time elapsed: 0.139 s
% 0.20/0.55  % (13414)------------------------------
% 0.20/0.55  % (13414)------------------------------
% 0.20/0.55  % (13402)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (13402)Memory used [KB]: 1663
% 0.20/0.55  % (13402)Time elapsed: 0.124 s
% 0.20/0.55  % (13402)------------------------------
% 0.20/0.55  % (13402)------------------------------
% 0.20/0.55  % (13415)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (13415)Memory used [KB]: 6268
% 0.20/0.55  % (13415)Time elapsed: 0.119 s
% 0.20/0.55  % (13415)------------------------------
% 0.20/0.55  % (13415)------------------------------
% 0.20/0.55  % (13410)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.55  % (13387)Success in time 0.19 s
%------------------------------------------------------------------------------
