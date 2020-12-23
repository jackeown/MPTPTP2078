%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1401+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:52 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 171 expanded)
%              Number of leaves         :   15 (  61 expanded)
%              Depth                    :   20
%              Number of atoms          :  418 (1391 expanded)
%              Number of equality atoms :   46 ( 165 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (8240)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
fof(f272,plain,(
    $false ),
    inference(subsumption_resolution,[],[f271,f47])).

fof(f47,plain,(
    v3_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k1_connsp_2(sK4,sK5) != sK6
    & r1_tarski(sK6,k1_connsp_2(sK4,sK5))
    & r2_hidden(sK5,sK6)
    & v4_pre_topc(sK6,sK4)
    & v3_pre_topc(sK6,sK4)
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f10,f26,f25,f24])).

% (8252)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% (8234)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% (8236)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% (8230)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_connsp_2(X0,X1) != X2
                & r1_tarski(X2,k1_connsp_2(X0,X1))
                & r2_hidden(X1,X2)
                & v4_pre_topc(X2,X0)
                & v3_pre_topc(X2,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_connsp_2(sK4,X1) != X2
              & r1_tarski(X2,k1_connsp_2(sK4,X1))
              & r2_hidden(X1,X2)
              & v4_pre_topc(X2,sK4)
              & v3_pre_topc(X2,sK4)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4))) )
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k1_connsp_2(sK4,X1) != X2
            & r1_tarski(X2,k1_connsp_2(sK4,X1))
            & r2_hidden(X1,X2)
            & v4_pre_topc(X2,sK4)
            & v3_pre_topc(X2,sK4)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4))) )
        & m1_subset_1(X1,u1_struct_0(sK4)) )
   => ( ? [X2] :
          ( k1_connsp_2(sK4,sK5) != X2
          & r1_tarski(X2,k1_connsp_2(sK4,sK5))
          & r2_hidden(sK5,X2)
          & v4_pre_topc(X2,sK4)
          & v3_pre_topc(X2,sK4)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4))) )
      & m1_subset_1(sK5,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( k1_connsp_2(sK4,sK5) != X2
        & r1_tarski(X2,k1_connsp_2(sK4,sK5))
        & r2_hidden(sK5,X2)
        & v4_pre_topc(X2,sK4)
        & v3_pre_topc(X2,sK4)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4))) )
   => ( k1_connsp_2(sK4,sK5) != sK6
      & r1_tarski(sK6,k1_connsp_2(sK4,sK5))
      & r2_hidden(sK5,sK6)
      & v4_pre_topc(sK6,sK4)
      & v3_pre_topc(sK6,sK4)
      & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_connsp_2(X0,X1) != X2
              & r1_tarski(X2,k1_connsp_2(X0,X1))
              & r2_hidden(X1,X2)
              & v4_pre_topc(X2,X0)
              & v3_pre_topc(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_connsp_2(X0,X1) != X2
              & r1_tarski(X2,k1_connsp_2(X0,X1))
              & r2_hidden(X1,X2)
              & v4_pre_topc(X2,X0)
              & v3_pre_topc(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r1_tarski(X2,k1_connsp_2(X0,X1))
                    & r2_hidden(X1,X2)
                    & v4_pre_topc(X2,X0)
                    & v3_pre_topc(X2,X0) )
                 => k1_connsp_2(X0,X1) = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X2,k1_connsp_2(X0,X1))
                  & r2_hidden(X1,X2)
                  & v4_pre_topc(X2,X0)
                  & v3_pre_topc(X2,X0) )
               => k1_connsp_2(X0,X1) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_connsp_2)).

% (8243)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f271,plain,(
    ~ v3_pre_topc(sK6,sK4) ),
    inference(subsumption_resolution,[],[f270,f48])).

fof(f48,plain,(
    v4_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f270,plain,
    ( ~ v4_pre_topc(sK6,sK4)
    | ~ v3_pre_topc(sK6,sK4) ),
    inference(subsumption_resolution,[],[f269,f49])).

fof(f49,plain,(
    r2_hidden(sK5,sK6) ),
    inference(cnf_transformation,[],[f27])).

fof(f269,plain,
    ( ~ r2_hidden(sK5,sK6)
    | ~ v4_pre_topc(sK6,sK4)
    | ~ v3_pre_topc(sK6,sK4) ),
    inference(resolution,[],[f268,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ r2_hidden(X1,X0)
      | ~ v4_pre_topc(X0,X2)
      | ~ v3_pre_topc(X0,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ~ r2_hidden(X1,X0)
        | ~ v4_pre_topc(X0,X2)
        | ~ v3_pre_topc(X0,X2) )
      & ( ( r2_hidden(X1,X0)
          & v4_pre_topc(X0,X2)
          & v3_pre_topc(X0,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X4,X1,X0] :
      ( ( sP0(X4,X1,X0)
        | ~ r2_hidden(X1,X4)
        | ~ v4_pre_topc(X4,X0)
        | ~ v3_pre_topc(X4,X0) )
      & ( ( r2_hidden(X1,X4)
          & v4_pre_topc(X4,X0)
          & v3_pre_topc(X4,X0) )
        | ~ sP0(X4,X1,X0) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X4,X1,X0] :
      ( ( sP0(X4,X1,X0)
        | ~ r2_hidden(X1,X4)
        | ~ v4_pre_topc(X4,X0)
        | ~ v3_pre_topc(X4,X0) )
      & ( ( r2_hidden(X1,X4)
          & v4_pre_topc(X4,X0)
          & v3_pre_topc(X4,X0) )
        | ~ sP0(X4,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X4,X1,X0] :
      ( sP0(X4,X1,X0)
    <=> ( r2_hidden(X1,X4)
        & v4_pre_topc(X4,X0)
        & v3_pre_topc(X4,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f268,plain,(
    ~ sP0(sK6,sK5,sK4) ),
    inference(subsumption_resolution,[],[f263,f45])).

fof(f45,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f27])).

fof(f263,plain,
    ( ~ sP0(sK6,sK5,sK4)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(resolution,[],[f242,f83])).

fof(f83,plain,(
    ~ r1_tarski(k1_connsp_2(sK4,sK5),sK6) ),
    inference(subsumption_resolution,[],[f80,f51])).

fof(f51,plain,(
    k1_connsp_2(sK4,sK5) != sK6 ),
    inference(cnf_transformation,[],[f27])).

fof(f80,plain,
    ( k1_connsp_2(sK4,sK5) = sK6
    | ~ r1_tarski(k1_connsp_2(sK4,sK5),sK6) ),
    inference(resolution,[],[f73,f50])).

fof(f50,plain,(
    r1_tarski(sK6,k1_connsp_2(sK4,sK5)) ),
    inference(cnf_transformation,[],[f27])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

% (8239)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f242,plain,(
    ! [X2] :
      ( r1_tarski(k1_connsp_2(sK4,X2),sK6)
      | ~ sP0(sK6,X2,sK4)
      | ~ m1_subset_1(X2,u1_struct_0(sK4)) ) ),
    inference(subsumption_resolution,[],[f241,f42])).

fof(f42,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f241,plain,(
    ! [X2] :
      ( v2_struct_0(sK4)
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ sP0(sK6,X2,sK4)
      | r1_tarski(k1_connsp_2(sK4,X2),sK6) ) ),
    inference(subsumption_resolution,[],[f240,f43])).

fof(f43,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f240,plain,(
    ! [X2] :
      ( ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4)
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ sP0(sK6,X2,sK4)
      | r1_tarski(k1_connsp_2(sK4,X2),sK6) ) ),
    inference(subsumption_resolution,[],[f229,f44])).

fof(f44,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f229,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4)
      | ~ m1_subset_1(X2,u1_struct_0(sK4))
      | ~ sP0(sK6,X2,sK4)
      | r1_tarski(k1_connsp_2(sK4,X2),sK6) ) ),
    inference(resolution,[],[f186,f163])).

fof(f163,plain,(
    ! [X4,X5] :
      ( ~ sP2(X5,sK4,X4)
      | ~ sP0(sK6,X4,sK4)
      | r1_tarski(X5,sK6) ) ),
    inference(resolution,[],[f159,f46])).

fof(f46,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f27])).

fof(f159,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))
      | ~ sP0(X11,X10,X9)
      | ~ sP2(X8,X9,X10)
      | r1_tarski(X8,X11) ) ),
    inference(duplicate_literal_removal,[],[f155])).

fof(f155,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ sP2(X8,X9,X10)
      | ~ sP0(X11,X10,X9)
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))
      | r1_tarski(X8,X11)
      | ~ sP2(X8,X9,X10) ) ),
    inference(resolution,[],[f111,f107])).

fof(f107,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(X7,sK8(X4,X5,X6))
      | r1_tarski(X4,X7)
      | ~ sP2(X4,X5,X6) ) ),
    inference(superposition,[],[f68,f104])).

fof(f104,plain,(
    ! [X4,X5,X3] :
      ( k1_setfam_1(sK8(X4,X3,X5)) = X4
      | ~ sP2(X4,X3,X5) ) ),
    inference(subsumption_resolution,[],[f102,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ! [X3] :
            ( k6_setfam_1(u1_struct_0(X1),X3) != X0
            | ( ~ sP1(X1,X2,sK7(X1,X2,X3),X3)
              & m1_subset_1(sK7(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) )
      & ( ( k6_setfam_1(u1_struct_0(X1),sK8(X0,X1,X2)) = X0
          & ! [X6] :
              ( sP1(X1,X2,X6,sK8(X0,X1,X2))
              | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f31,f33,f32])).

fof(f32,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ sP1(X1,X2,X4,X3)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ sP1(X1,X2,sK7(X1,X2,X3),X3)
        & m1_subset_1(sK7(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( k6_setfam_1(u1_struct_0(X1),X5) = X0
          & ! [X6] :
              ( sP1(X1,X2,X6,X5)
              | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
     => ( k6_setfam_1(u1_struct_0(X1),sK8(X0,X1,X2)) = X0
        & ! [X6] :
            ( sP1(X1,X2,X6,sK8(X0,X1,X2))
            | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ! [X3] :
            ( k6_setfam_1(u1_struct_0(X1),X3) != X0
            | ? [X4] :
                ( ~ sP1(X1,X2,X4,X3)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) )
      & ( ? [X5] :
            ( k6_setfam_1(u1_struct_0(X1),X5) = X0
            & ! [X6] :
                ( sP1(X1,X2,X6,X5)
                | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ( sP2(X2,X0,X1)
        | ! [X3] :
            ( k6_setfam_1(u1_struct_0(X0),X3) != X2
            | ? [X4] :
                ( ~ sP1(X0,X1,X4,X3)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      & ( ? [X3] :
            ( k6_setfam_1(u1_struct_0(X0),X3) = X2
            & ! [X4] :
                ( sP1(X0,X1,X4,X3)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ sP2(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X0,X1)
    <=> ? [X3] :
          ( k6_setfam_1(u1_struct_0(X0),X3) = X2
          & ! [X4] :
              ( sP1(X0,X1,X4,X3)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f102,plain,(
    ! [X4,X5,X3] :
      ( k1_setfam_1(sK8(X4,X3,X5)) = X4
      | ~ sP2(X4,X3,X5)
      | ~ m1_subset_1(sK8(X4,X3,X5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3)))) ) ),
    inference(superposition,[],[f56,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k6_setfam_1(u1_struct_0(X1),sK8(X0,X1,X2)) = X0
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f111,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,sK8(X2,X1,X3))
      | ~ sP2(X2,X1,X3)
      | ~ sP0(X0,X3,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(resolution,[],[f55,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | ~ sP0(X2,X1,X0)
      | r2_hidden(X2,X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ( ( ~ sP0(X2,X1,X0)
            | ~ r2_hidden(X2,X3) )
          & ( sP0(X2,X1,X0)
            | r2_hidden(X2,X3) ) ) )
      & ( ( ( r2_hidden(X2,X3)
            | ~ sP0(X2,X1,X0) )
          & ( sP0(X2,X1,X0)
            | ~ r2_hidden(X2,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X4,X3] :
      ( ( sP1(X0,X1,X4,X3)
        | ( ( ~ sP0(X4,X1,X0)
            | ~ r2_hidden(X4,X3) )
          & ( sP0(X4,X1,X0)
            | r2_hidden(X4,X3) ) ) )
      & ( ( ( r2_hidden(X4,X3)
            | ~ sP0(X4,X1,X0) )
          & ( sP0(X4,X1,X0)
            | ~ r2_hidden(X4,X3) ) )
        | ~ sP1(X0,X1,X4,X3) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X4,X3] :
      ( sP1(X0,X1,X4,X3)
    <=> ( r2_hidden(X4,X3)
      <=> sP0(X4,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f55,plain,(
    ! [X6,X2,X0,X1] :
      ( sP1(X1,X2,X6,sK8(X0,X1,X2))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f186,plain,(
    ! [X0,X1] :
      ( sP2(k1_connsp_2(X1,X0),X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f178])).

fof(f178,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | sP2(k1_connsp_2(X1,X0),X1,X0) ) ),
    inference(resolution,[],[f135,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ sP3(X0,X1,k1_connsp_2(X1,X0))
      | sP2(k1_connsp_2(X1,X0),X1,X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X1,X0)
      | k1_connsp_2(X1,X0) != X2
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_connsp_2(X1,X0) = X2
          | ~ sP2(X2,X1,X0) )
        & ( sP2(X2,X1,X0)
          | k1_connsp_2(X1,X0) != X2 ) )
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X1,X0,X2] :
      ( ( ( k1_connsp_2(X0,X1) = X2
          | ~ sP2(X2,X0,X1) )
        & ( sP2(X2,X0,X1)
          | k1_connsp_2(X0,X1) != X2 ) )
      | ~ sP3(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X1,X0,X2] :
      ( ( k1_connsp_2(X0,X1) = X2
      <=> sP2(X2,X0,X1) )
      | ~ sP3(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X1,k1_connsp_2(X1,X2))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f133])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X1,k1_connsp_2(X1,X2))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f67,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_connsp_2)).

% (8246)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | sP3(X1,X0,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP3(X1,X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f12,f22,f21,f20,f19])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_connsp_2(X0,X1) = X2
              <=> ? [X3] :
                    ( k6_setfam_1(u1_struct_0(X0),X3) = X2
                    & ! [X4] :
                        ( ( r2_hidden(X4,X3)
                        <=> ( r2_hidden(X1,X4)
                            & v4_pre_topc(X4,X0)
                            & v3_pre_topc(X4,X0) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_connsp_2(X0,X1) = X2
              <=> ? [X3] :
                    ( k6_setfam_1(u1_struct_0(X0),X3) = X2
                    & ! [X4] :
                        ( ( r2_hidden(X4,X3)
                        <=> ( r2_hidden(X1,X4)
                            & v4_pre_topc(X4,X0)
                            & v3_pre_topc(X4,X0) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k1_connsp_2(X0,X1) = X2
              <=> ? [X3] :
                    ( k6_setfam_1(u1_struct_0(X0),X3) = X2
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X4,X3)
                        <=> ( r2_hidden(X1,X4)
                            & v4_pre_topc(X4,X0)
                            & v3_pre_topc(X4,X0) ) ) )
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_connsp_2)).

%------------------------------------------------------------------------------
