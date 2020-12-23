%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 388 expanded)
%              Number of leaves         :   24 ( 123 expanded)
%              Depth                    :   21
%              Number of atoms          :  408 (1727 expanded)
%              Number of equality atoms :   43 ( 129 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f548,plain,(
    $false ),
    inference(subsumption_resolution,[],[f527,f139])).

fof(f139,plain,(
    ! [X1] : ~ v1_subset_1(X1,X1) ),
    inference(subsumption_resolution,[],[f91,f136])).

fof(f136,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f69,f132])).

fof(f132,plain,(
    ! [X0] : sK6(X0) = X0 ),
    inference(subsumption_resolution,[],[f130,f70])).

fof(f70,plain,(
    ! [X0] : ~ v1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK6(X0),X0)
      & m1_subset_1(sK6(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f6,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_subset_1(sK6(X0),X0)
        & m1_subset_1(sK6(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

fof(f130,plain,(
    ! [X0] :
      ( sK6(X0) = X0
      | v1_subset_1(sK6(X0),X0) ) ),
    inference(resolution,[],[f75,f69])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f69,plain,(
    ! [X0] : m1_subset_1(sK6(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f91,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f527,plain,(
    v1_subset_1(sK3,sK3) ),
    inference(backward_demodulation,[],[f99,f502])).

fof(f502,plain,(
    sK3 = k1_zfmisc_1(sK2) ),
    inference(resolution,[],[f490,f374])).

fof(f374,plain,(
    r2_hidden(k1_xboole_0,sK3) ),
    inference(resolution,[],[f371,f62])).

fof(f62,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f371,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | r2_hidden(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f363,f109])).

fof(f109,plain,(
    ! [X0] : r1_tarski(sK4,X0) ),
    inference(resolution,[],[f85,f95])).

fof(f95,plain,(
    ! [X0] : ~ r2_hidden(X0,sK4) ),
    inference(resolution,[],[f67,f61])).

fof(f61,plain,(
    v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( v1_xboole_0(sK4)
    & r2_hidden(sK4,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK2))))
    & v13_waybel_0(sK3,k3_yellow_1(sK2))
    & v1_subset_1(sK3,u1_struct_0(k3_yellow_1(sK2)))
    & ~ v1_xboole_0(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f17,f31,f30,f29])).

% (21616)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% (21615)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( v1_xboole_0(X2)
                & r2_hidden(X2,X1) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
            & v13_waybel_0(X1,k3_yellow_1(X0))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( v1_xboole_0(X2)
              & r2_hidden(X2,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK2))))
          & v13_waybel_0(X1,k3_yellow_1(sK2))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(sK2)))
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( v1_xboole_0(X2)
            & r2_hidden(X2,X1) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK2))))
        & v13_waybel_0(X1,k3_yellow_1(sK2))
        & v1_subset_1(X1,u1_struct_0(k3_yellow_1(sK2)))
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( v1_xboole_0(X2)
          & r2_hidden(X2,sK3) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK2))))
      & v13_waybel_0(sK3,k3_yellow_1(sK2))
      & v1_subset_1(sK3,u1_struct_0(k3_yellow_1(sK2)))
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X2] :
        ( v1_xboole_0(X2)
        & r2_hidden(X2,sK3) )
   => ( v1_xboole_0(sK4)
      & r2_hidden(sK4,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( v1_xboole_0(X2)
              & r2_hidden(X2,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          & v13_waybel_0(X1,k3_yellow_1(X0))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( v1_xboole_0(X2)
              & r2_hidden(X2,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          & v13_waybel_0(X1,k3_yellow_1(X0))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
              & v13_waybel_0(X1,k3_yellow_1(X0))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ~ ( v1_xboole_0(X2)
                  & r2_hidden(X2,X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
              & v13_waybel_0(X1,k3_yellow_1(X0))
              & v2_waybel_0(X1,k3_yellow_1(X0))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ~ ( v1_xboole_0(X2)
                  & r2_hidden(X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
            & v13_waybel_0(X1,k3_yellow_1(X0))
            & v2_waybel_0(X1,k3_yellow_1(X0))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ~ ( v1_xboole_0(X2)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).

fof(f67,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK5(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f85,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK10(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK10(X0,X1),X1)
          & r2_hidden(sK10(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f48,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK10(X0,X1),X1)
        & r2_hidden(sK10(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f363,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | ~ r1_tarski(sK4,X0)
      | r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f361,f60])).

fof(f60,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f361,plain,(
    ! [X33,X32] :
      ( ~ r2_hidden(X32,sK3)
      | ~ r1_tarski(X33,sK2)
      | ~ r1_tarski(X32,X33)
      | r2_hidden(X33,sK3) ) ),
    inference(resolution,[],[f78,f174])).

fof(f174,plain,(
    sP0(sK3,sK2) ),
    inference(subsumption_resolution,[],[f173,f115])).

fof(f115,plain,(
    sP1(sK2,sK3) ),
    inference(resolution,[],[f101,f100])).

fof(f100,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(backward_demodulation,[],[f59,f98])).

fof(f98,plain,(
    ! [X1] : k1_zfmisc_1(X1) = u1_struct_0(k3_yellow_1(X1)) ),
    inference(superposition,[],[f65,f94])).

fof(f94,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f64,f63])).

fof(f63,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f64,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).

fof(f65,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK2)))) ),
    inference(cnf_transformation,[],[f32])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | sP1(X0,X1) ) ),
    inference(backward_demodulation,[],[f83,f98])).

fof(f83,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(definition_folding,[],[f24,f27,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2,X3] :
          ( r2_hidden(X3,X1)
          | ~ r2_hidden(X2,X1)
          | ~ r1_tarski(X3,X0)
          | ~ r1_tarski(X2,X3) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1)
            | ~ r1_tarski(X3,X0)
            | ~ r1_tarski(X2,X3) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1)
            | ~ r1_tarski(X3,X0)
            | ~ r1_tarski(X2,X3) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
     => ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,X1)
              & r1_tarski(X3,X0)
              & r1_tarski(X2,X3) )
           => r2_hidden(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_waybel_7)).

fof(f173,plain,
    ( sP0(sK3,sK2)
    | ~ sP1(sK2,sK3) ),
    inference(resolution,[],[f76,f58])).

fof(f58,plain,(
    v13_waybel_0(sK3,k3_yellow_1(sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | sP0(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v13_waybel_0(X1,k3_yellow_1(X0))
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v13_waybel_0(X1,k3_yellow_1(X0)) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f78,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ sP0(X0,X1)
      | ~ r2_hidden(X4,X0)
      | ~ r1_tarski(X5,X1)
      | ~ r1_tarski(X4,X5)
      | r2_hidden(X5,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ~ r2_hidden(sK9(X0,X1),X0)
          & r2_hidden(sK8(X0,X1),X0)
          & r1_tarski(sK9(X0,X1),X1)
          & r1_tarski(sK8(X0,X1),sK9(X0,X1)) ) )
      & ( ! [X4,X5] :
            ( r2_hidden(X5,X0)
            | ~ r2_hidden(X4,X0)
            | ~ r1_tarski(X5,X1)
            | ~ r1_tarski(X4,X5) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f44,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(X3,X0)
          & r2_hidden(X2,X0)
          & r1_tarski(X3,X1)
          & r1_tarski(X2,X3) )
     => ( ~ r2_hidden(sK9(X0,X1),X0)
        & r2_hidden(sK8(X0,X1),X0)
        & r1_tarski(sK9(X0,X1),X1)
        & r1_tarski(sK8(X0,X1),sK9(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2,X3] :
            ( ~ r2_hidden(X3,X0)
            & r2_hidden(X2,X0)
            & r1_tarski(X3,X1)
            & r1_tarski(X2,X3) ) )
      & ( ! [X4,X5] :
            ( r2_hidden(X5,X0)
            | ~ r2_hidden(X4,X0)
            | ~ r1_tarski(X5,X1)
            | ~ r1_tarski(X4,X5) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2,X3] :
            ( ~ r2_hidden(X3,X1)
            & r2_hidden(X2,X1)
            & r1_tarski(X3,X0)
            & r1_tarski(X2,X3) ) )
      & ( ! [X2,X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1)
            | ~ r1_tarski(X3,X0)
            | ~ r1_tarski(X2,X3) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f490,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | sK3 = k1_zfmisc_1(sK2) ) ),
    inference(resolution,[],[f489,f160])).

fof(f160,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_zfmisc_1(sK2))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f155,f84])).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f155,plain,(
    r1_tarski(sK3,k1_zfmisc_1(sK2)) ),
    inference(resolution,[],[f149,f113])).

fof(f113,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f111])).

fof(f111,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f86,f85])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK10(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f149,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_zfmisc_1(sK2))
      | r1_tarski(sK3,k1_zfmisc_1(sK2)) ) ),
    inference(resolution,[],[f148,f92])).

fof(f92,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK11(X0,X1),X0)
            | ~ r2_hidden(sK11(X0,X1),X1) )
          & ( r1_tarski(sK11(X0,X1),X0)
            | r2_hidden(sK11(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f52,f53])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK11(X0,X1),X0)
          | ~ r2_hidden(sK11(X0,X1),X1) )
        & ( r1_tarski(sK11(X0,X1),X0)
          | r2_hidden(sK11(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f148,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(k1_zfmisc_1(sK2)))
      | r1_tarski(sK3,k1_zfmisc_1(sK2)) ) ),
    inference(resolution,[],[f147,f67])).

fof(f147,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | r1_tarski(sK3,k1_zfmisc_1(sK2)) ),
    inference(resolution,[],[f105,f93])).

fof(f93,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f105,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(resolution,[],[f71,f100])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f489,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(sK2))
      | sK3 = k1_zfmisc_1(sK2) ) ),
    inference(resolution,[],[f488,f67])).

fof(f488,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK2))
    | sK3 = k1_zfmisc_1(sK2) ),
    inference(subsumption_resolution,[],[f487,f100])).

fof(f487,plain,
    ( sK3 = k1_zfmisc_1(sK2)
    | v1_xboole_0(k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(duplicate_literal_removal,[],[f484])).

fof(f484,plain,
    ( sK3 = k1_zfmisc_1(sK2)
    | v1_xboole_0(k1_zfmisc_1(sK2))
    | sK3 = k1_zfmisc_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(resolution,[],[f380,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ~ r2_hidden(sK7(X0,X1),X1)
        & m1_subset_1(sK7(X0,X1),X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f21,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & m1_subset_1(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

fof(f380,plain,
    ( r2_hidden(sK7(k1_zfmisc_1(sK2),sK3),sK3)
    | sK3 = k1_zfmisc_1(sK2)
    | v1_xboole_0(k1_zfmisc_1(sK2)) ),
    inference(resolution,[],[f371,f310])).

fof(f310,plain,
    ( r1_tarski(sK7(k1_zfmisc_1(sK2),sK3),sK2)
    | sK3 = k1_zfmisc_1(sK2)
    | v1_xboole_0(k1_zfmisc_1(sK2)) ),
    inference(resolution,[],[f207,f93])).

fof(f207,plain,
    ( r2_hidden(sK7(k1_zfmisc_1(sK2),sK3),k1_zfmisc_1(sK2))
    | v1_xboole_0(k1_zfmisc_1(sK2))
    | sK3 = k1_zfmisc_1(sK2) ),
    inference(resolution,[],[f203,f71])).

fof(f203,plain,
    ( m1_subset_1(sK7(k1_zfmisc_1(sK2),sK3),k1_zfmisc_1(sK2))
    | sK3 = k1_zfmisc_1(sK2) ),
    inference(resolution,[],[f72,f100])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(sK7(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f99,plain,(
    v1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(backward_demodulation,[],[f57,f98])).

fof(f57,plain,(
    v1_subset_1(sK3,u1_struct_0(k3_yellow_1(sK2))) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:40:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.53  % (21614)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (21640)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (21621)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (21617)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.56  % (21632)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (21618)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.56  % (21624)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.57  % (21624)Refutation not found, incomplete strategy% (21624)------------------------------
% 0.21/0.57  % (21624)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (21624)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (21624)Memory used [KB]: 10746
% 0.21/0.57  % (21624)Time elapsed: 0.158 s
% 0.21/0.57  % (21624)------------------------------
% 0.21/0.57  % (21624)------------------------------
% 0.21/0.57  % (21625)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.57  % (21634)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.57  % (21642)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.58  % (21623)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.58  % (21626)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.58  % (21641)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.59  % (21621)Refutation found. Thanks to Tanya!
% 0.21/0.59  % SZS status Theorem for theBenchmark
% 0.21/0.59  % (21633)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.59  % SZS output start Proof for theBenchmark
% 0.21/0.59  fof(f548,plain,(
% 0.21/0.59    $false),
% 0.21/0.59    inference(subsumption_resolution,[],[f527,f139])).
% 0.21/0.59  fof(f139,plain,(
% 0.21/0.59    ( ! [X1] : (~v1_subset_1(X1,X1)) )),
% 0.21/0.59    inference(subsumption_resolution,[],[f91,f136])).
% 0.21/0.59  fof(f136,plain,(
% 0.21/0.59    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.59    inference(backward_demodulation,[],[f69,f132])).
% 0.21/0.59  fof(f132,plain,(
% 0.21/0.59    ( ! [X0] : (sK6(X0) = X0) )),
% 0.21/0.59    inference(subsumption_resolution,[],[f130,f70])).
% 0.21/0.59  fof(f70,plain,(
% 0.21/0.59    ( ! [X0] : (~v1_subset_1(sK6(X0),X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f38])).
% 0.21/0.59  fof(f38,plain,(
% 0.21/0.59    ! [X0] : (~v1_subset_1(sK6(X0),X0) & m1_subset_1(sK6(X0),k1_zfmisc_1(X0)))),
% 0.21/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f6,f37])).
% 0.21/0.59  fof(f37,plain,(
% 0.21/0.59    ! [X0] : (? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (~v1_subset_1(sK6(X0),X0) & m1_subset_1(sK6(X0),k1_zfmisc_1(X0))))),
% 0.21/0.59    introduced(choice_axiom,[])).
% 0.21/0.59  fof(f6,axiom,(
% 0.21/0.59    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).
% 0.21/0.59  fof(f130,plain,(
% 0.21/0.59    ( ! [X0] : (sK6(X0) = X0 | v1_subset_1(sK6(X0),X0)) )),
% 0.21/0.59    inference(resolution,[],[f75,f69])).
% 0.21/0.59  fof(f75,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f41])).
% 0.21/0.59  fof(f41,plain,(
% 0.21/0.59    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.59    inference(nnf_transformation,[],[f22])).
% 0.21/0.59  fof(f22,plain,(
% 0.21/0.59    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.59    inference(ennf_transformation,[],[f11])).
% 0.21/0.59  fof(f11,axiom,(
% 0.21/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.21/0.59  fof(f69,plain,(
% 0.21/0.59    ( ! [X0] : (m1_subset_1(sK6(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.59    inference(cnf_transformation,[],[f38])).
% 0.21/0.59  fof(f91,plain,(
% 0.21/0.59    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | ~v1_subset_1(X1,X1)) )),
% 0.21/0.59    inference(equality_resolution,[],[f74])).
% 0.21/0.60  fof(f74,plain,(
% 0.21/0.60    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f41])).
% 0.21/0.60  fof(f527,plain,(
% 0.21/0.60    v1_subset_1(sK3,sK3)),
% 0.21/0.60    inference(backward_demodulation,[],[f99,f502])).
% 0.21/0.60  fof(f502,plain,(
% 0.21/0.60    sK3 = k1_zfmisc_1(sK2)),
% 0.21/0.60    inference(resolution,[],[f490,f374])).
% 0.21/0.60  fof(f374,plain,(
% 0.21/0.60    r2_hidden(k1_xboole_0,sK3)),
% 0.21/0.60    inference(resolution,[],[f371,f62])).
% 0.21/0.60  fof(f62,plain,(
% 0.21/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f3])).
% 0.21/0.60  fof(f3,axiom,(
% 0.21/0.60    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.60  fof(f371,plain,(
% 0.21/0.60    ( ! [X0] : (~r1_tarski(X0,sK2) | r2_hidden(X0,sK3)) )),
% 0.21/0.60    inference(subsumption_resolution,[],[f363,f109])).
% 0.21/0.60  fof(f109,plain,(
% 0.21/0.60    ( ! [X0] : (r1_tarski(sK4,X0)) )),
% 0.21/0.60    inference(resolution,[],[f85,f95])).
% 0.21/0.60  fof(f95,plain,(
% 0.21/0.60    ( ! [X0] : (~r2_hidden(X0,sK4)) )),
% 0.21/0.60    inference(resolution,[],[f67,f61])).
% 0.21/0.60  fof(f61,plain,(
% 0.21/0.60    v1_xboole_0(sK4)),
% 0.21/0.60    inference(cnf_transformation,[],[f32])).
% 0.21/0.60  fof(f32,plain,(
% 0.21/0.60    ((v1_xboole_0(sK4) & r2_hidden(sK4,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK2)))) & v13_waybel_0(sK3,k3_yellow_1(sK2)) & v1_subset_1(sK3,u1_struct_0(k3_yellow_1(sK2))) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)),
% 0.21/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f17,f31,f30,f29])).
% 0.21/0.60  % (21616)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.60  % (21615)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.60  fof(f29,plain,(
% 0.21/0.60    ? [X0] : (? [X1] : (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK2)))) & v13_waybel_0(X1,k3_yellow_1(sK2)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(sK2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK2))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f30,plain,(
% 0.21/0.60    ? [X1] : (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK2)))) & v13_waybel_0(X1,k3_yellow_1(sK2)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(sK2))) & ~v1_xboole_0(X1)) => (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK2)))) & v13_waybel_0(sK3,k3_yellow_1(sK2)) & v1_subset_1(sK3,u1_struct_0(k3_yellow_1(sK2))) & ~v1_xboole_0(sK3))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f31,plain,(
% 0.21/0.60    ? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,sK3)) => (v1_xboole_0(sK4) & r2_hidden(sK4,sK3))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f17,plain,(
% 0.21/0.60    ? [X0] : (? [X1] : (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.60    inference(flattening,[],[f16])).
% 0.21/0.60  fof(f16,plain,(
% 0.21/0.60    ? [X0] : (? [X1] : (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 0.21/0.60    inference(ennf_transformation,[],[f15])).
% 0.21/0.60  fof(f15,plain,(
% 0.21/0.60    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 0.21/0.60    inference(pure_predicate_removal,[],[f14])).
% 0.21/0.60  fof(f14,negated_conjecture,(
% 0.21/0.60    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 0.21/0.60    inference(negated_conjecture,[],[f13])).
% 0.21/0.60  fof(f13,conjecture,(
% 0.21/0.60    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).
% 0.21/0.60  fof(f67,plain,(
% 0.21/0.60    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f36])).
% 0.21/0.60  fof(f36,plain,(
% 0.21/0.60    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK5(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).
% 0.21/0.60  fof(f35,plain,(
% 0.21/0.60    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f34,plain,(
% 0.21/0.60    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.60    inference(rectify,[],[f33])).
% 0.21/0.60  fof(f33,plain,(
% 0.21/0.60    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.60    inference(nnf_transformation,[],[f1])).
% 0.21/0.60  fof(f1,axiom,(
% 0.21/0.60    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.60  fof(f85,plain,(
% 0.21/0.60    ( ! [X0,X1] : (r2_hidden(sK10(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f50])).
% 0.21/0.60  fof(f50,plain,(
% 0.21/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK10(X0,X1),X1) & r2_hidden(sK10(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f48,f49])).
% 0.21/0.60  fof(f49,plain,(
% 0.21/0.60    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK10(X0,X1),X1) & r2_hidden(sK10(X0,X1),X0)))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f48,plain,(
% 0.21/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.60    inference(rectify,[],[f47])).
% 0.21/0.60  fof(f47,plain,(
% 0.21/0.60    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.60    inference(nnf_transformation,[],[f25])).
% 0.21/0.60  fof(f25,plain,(
% 0.21/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.60    inference(ennf_transformation,[],[f2])).
% 0.21/0.60  fof(f2,axiom,(
% 0.21/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.60  fof(f363,plain,(
% 0.21/0.60    ( ! [X0] : (~r1_tarski(X0,sK2) | ~r1_tarski(sK4,X0) | r2_hidden(X0,sK3)) )),
% 0.21/0.60    inference(resolution,[],[f361,f60])).
% 0.21/0.60  fof(f60,plain,(
% 0.21/0.60    r2_hidden(sK4,sK3)),
% 0.21/0.60    inference(cnf_transformation,[],[f32])).
% 0.21/0.60  fof(f361,plain,(
% 0.21/0.60    ( ! [X33,X32] : (~r2_hidden(X32,sK3) | ~r1_tarski(X33,sK2) | ~r1_tarski(X32,X33) | r2_hidden(X33,sK3)) )),
% 0.21/0.60    inference(resolution,[],[f78,f174])).
% 0.21/0.60  fof(f174,plain,(
% 0.21/0.60    sP0(sK3,sK2)),
% 0.21/0.60    inference(subsumption_resolution,[],[f173,f115])).
% 0.21/0.60  fof(f115,plain,(
% 0.21/0.60    sP1(sK2,sK3)),
% 0.21/0.60    inference(resolution,[],[f101,f100])).
% 0.21/0.60  fof(f100,plain,(
% 0.21/0.60    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 0.21/0.60    inference(backward_demodulation,[],[f59,f98])).
% 0.21/0.60  fof(f98,plain,(
% 0.21/0.60    ( ! [X1] : (k1_zfmisc_1(X1) = u1_struct_0(k3_yellow_1(X1))) )),
% 0.21/0.60    inference(superposition,[],[f65,f94])).
% 0.21/0.60  fof(f94,plain,(
% 0.21/0.60    ( ! [X0] : (k3_yellow_1(X0) = k2_yellow_1(k1_zfmisc_1(X0))) )),
% 0.21/0.60    inference(forward_demodulation,[],[f64,f63])).
% 0.21/0.60  fof(f63,plain,(
% 0.21/0.60    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f8])).
% 0.21/0.60  fof(f8,axiom,(
% 0.21/0.60    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).
% 0.21/0.60  fof(f64,plain,(
% 0.21/0.60    ( ! [X0] : (k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f10])).
% 0.21/0.60  fof(f10,axiom,(
% 0.21/0.60    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).
% 0.21/0.60  fof(f65,plain,(
% 0.21/0.60    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.21/0.60    inference(cnf_transformation,[],[f9])).
% 0.21/0.60  fof(f9,axiom,(
% 0.21/0.60    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.21/0.60  fof(f59,plain,(
% 0.21/0.60    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK2))))),
% 0.21/0.60    inference(cnf_transformation,[],[f32])).
% 0.21/0.60  fof(f101,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | sP1(X0,X1)) )),
% 0.21/0.60    inference(backward_demodulation,[],[f83,f98])).
% 0.21/0.60  fof(f83,plain,(
% 0.21/0.60    ( ! [X0,X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f28])).
% 0.21/0.60  fof(f28,plain,(
% 0.21/0.60    ! [X0,X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 0.21/0.60    inference(definition_folding,[],[f24,f27,f26])).
% 0.21/0.60  fof(f26,plain,(
% 0.21/0.60    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2,X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3)))),
% 0.21/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.60  fof(f27,plain,(
% 0.21/0.60    ! [X0,X1] : ((v13_waybel_0(X1,k3_yellow_1(X0)) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 0.21/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.60  fof(f24,plain,(
% 0.21/0.60    ! [X0,X1] : ((v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 0.21/0.60    inference(flattening,[],[f23])).
% 0.21/0.60  fof(f23,plain,(
% 0.21/0.60    ! [X0,X1] : ((v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : (r2_hidden(X3,X1) | (~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 0.21/0.60    inference(ennf_transformation,[],[f12])).
% 0.21/0.60  fof(f12,axiom,(
% 0.21/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) => (v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : ((r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3)) => r2_hidden(X3,X1))))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_waybel_7)).
% 0.21/0.60  fof(f173,plain,(
% 0.21/0.60    sP0(sK3,sK2) | ~sP1(sK2,sK3)),
% 0.21/0.60    inference(resolution,[],[f76,f58])).
% 0.21/0.60  fof(f58,plain,(
% 0.21/0.60    v13_waybel_0(sK3,k3_yellow_1(sK2))),
% 0.21/0.60    inference(cnf_transformation,[],[f32])).
% 0.21/0.60  fof(f76,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~v13_waybel_0(X1,k3_yellow_1(X0)) | sP0(X1,X0) | ~sP1(X0,X1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f42])).
% 0.21/0.60  fof(f42,plain,(
% 0.21/0.60    ! [X0,X1] : (((v13_waybel_0(X1,k3_yellow_1(X0)) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v13_waybel_0(X1,k3_yellow_1(X0)))) | ~sP1(X0,X1))),
% 0.21/0.60    inference(nnf_transformation,[],[f27])).
% 0.21/0.60  fof(f78,plain,(
% 0.21/0.60    ( ! [X4,X0,X5,X1] : (~sP0(X0,X1) | ~r2_hidden(X4,X0) | ~r1_tarski(X5,X1) | ~r1_tarski(X4,X5) | r2_hidden(X5,X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f46])).
% 0.21/0.60  fof(f46,plain,(
% 0.21/0.60    ! [X0,X1] : ((sP0(X0,X1) | (~r2_hidden(sK9(X0,X1),X0) & r2_hidden(sK8(X0,X1),X0) & r1_tarski(sK9(X0,X1),X1) & r1_tarski(sK8(X0,X1),sK9(X0,X1)))) & (! [X4,X5] : (r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | ~r1_tarski(X5,X1) | ~r1_tarski(X4,X5)) | ~sP0(X0,X1)))),
% 0.21/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f44,f45])).
% 0.21/0.60  fof(f45,plain,(
% 0.21/0.60    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(X3,X0) & r2_hidden(X2,X0) & r1_tarski(X3,X1) & r1_tarski(X2,X3)) => (~r2_hidden(sK9(X0,X1),X0) & r2_hidden(sK8(X0,X1),X0) & r1_tarski(sK9(X0,X1),X1) & r1_tarski(sK8(X0,X1),sK9(X0,X1))))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f44,plain,(
% 0.21/0.60    ! [X0,X1] : ((sP0(X0,X1) | ? [X2,X3] : (~r2_hidden(X3,X0) & r2_hidden(X2,X0) & r1_tarski(X3,X1) & r1_tarski(X2,X3))) & (! [X4,X5] : (r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | ~r1_tarski(X5,X1) | ~r1_tarski(X4,X5)) | ~sP0(X0,X1)))),
% 0.21/0.60    inference(rectify,[],[f43])).
% 0.21/0.60  fof(f43,plain,(
% 0.21/0.60    ! [X1,X0] : ((sP0(X1,X0) | ? [X2,X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3))) & (! [X2,X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3)) | ~sP0(X1,X0)))),
% 0.21/0.60    inference(nnf_transformation,[],[f26])).
% 0.21/0.60  fof(f490,plain,(
% 0.21/0.60    ( ! [X0] : (~r2_hidden(X0,sK3) | sK3 = k1_zfmisc_1(sK2)) )),
% 0.21/0.60    inference(resolution,[],[f489,f160])).
% 0.21/0.60  fof(f160,plain,(
% 0.21/0.60    ( ! [X0] : (r2_hidden(X0,k1_zfmisc_1(sK2)) | ~r2_hidden(X0,sK3)) )),
% 0.21/0.60    inference(resolution,[],[f155,f84])).
% 0.21/0.60  fof(f84,plain,(
% 0.21/0.60    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f50])).
% 0.21/0.60  fof(f155,plain,(
% 0.21/0.60    r1_tarski(sK3,k1_zfmisc_1(sK2))),
% 0.21/0.60    inference(resolution,[],[f149,f113])).
% 0.21/0.60  fof(f113,plain,(
% 0.21/0.60    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.21/0.60    inference(duplicate_literal_removal,[],[f111])).
% 0.21/0.60  fof(f111,plain,(
% 0.21/0.60    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.21/0.60    inference(resolution,[],[f86,f85])).
% 0.21/0.60  fof(f86,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~r2_hidden(sK10(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f50])).
% 0.21/0.60  fof(f149,plain,(
% 0.21/0.60    ( ! [X0] : (~r1_tarski(X0,k1_zfmisc_1(sK2)) | r1_tarski(sK3,k1_zfmisc_1(sK2))) )),
% 0.21/0.60    inference(resolution,[],[f148,f92])).
% 0.21/0.60  fof(f92,plain,(
% 0.21/0.60    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.21/0.60    inference(equality_resolution,[],[f88])).
% 0.21/0.60  fof(f88,plain,(
% 0.21/0.60    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.60    inference(cnf_transformation,[],[f54])).
% 0.21/0.60  fof(f54,plain,(
% 0.21/0.60    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK11(X0,X1),X0) | ~r2_hidden(sK11(X0,X1),X1)) & (r1_tarski(sK11(X0,X1),X0) | r2_hidden(sK11(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f52,f53])).
% 0.21/0.60  fof(f53,plain,(
% 0.21/0.60    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK11(X0,X1),X0) | ~r2_hidden(sK11(X0,X1),X1)) & (r1_tarski(sK11(X0,X1),X0) | r2_hidden(sK11(X0,X1),X1))))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f52,plain,(
% 0.21/0.60    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.60    inference(rectify,[],[f51])).
% 0.21/0.60  fof(f51,plain,(
% 0.21/0.60    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.60    inference(nnf_transformation,[],[f4])).
% 0.21/0.60  fof(f4,axiom,(
% 0.21/0.60    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.60  fof(f148,plain,(
% 0.21/0.60    ( ! [X0] : (~r2_hidden(X0,k1_zfmisc_1(k1_zfmisc_1(sK2))) | r1_tarski(sK3,k1_zfmisc_1(sK2))) )),
% 0.21/0.60    inference(resolution,[],[f147,f67])).
% 0.21/0.60  fof(f147,plain,(
% 0.21/0.60    v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK2))) | r1_tarski(sK3,k1_zfmisc_1(sK2))),
% 0.21/0.60    inference(resolution,[],[f105,f93])).
% 0.21/0.60  fof(f93,plain,(
% 0.21/0.60    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 0.21/0.60    inference(equality_resolution,[],[f87])).
% 0.21/0.60  fof(f87,plain,(
% 0.21/0.60    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.60    inference(cnf_transformation,[],[f54])).
% 0.21/0.60  fof(f105,plain,(
% 0.21/0.60    r2_hidden(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 0.21/0.60    inference(resolution,[],[f71,f100])).
% 0.21/0.60  fof(f71,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f19])).
% 0.21/0.60  fof(f19,plain,(
% 0.21/0.60    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.60    inference(flattening,[],[f18])).
% 0.21/0.60  fof(f18,plain,(
% 0.21/0.60    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.60    inference(ennf_transformation,[],[f7])).
% 0.21/0.60  fof(f7,axiom,(
% 0.21/0.60    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.60  fof(f489,plain,(
% 0.21/0.60    ( ! [X0] : (~r2_hidden(X0,k1_zfmisc_1(sK2)) | sK3 = k1_zfmisc_1(sK2)) )),
% 0.21/0.60    inference(resolution,[],[f488,f67])).
% 0.21/0.60  fof(f488,plain,(
% 0.21/0.60    v1_xboole_0(k1_zfmisc_1(sK2)) | sK3 = k1_zfmisc_1(sK2)),
% 0.21/0.60    inference(subsumption_resolution,[],[f487,f100])).
% 0.21/0.60  fof(f487,plain,(
% 0.21/0.60    sK3 = k1_zfmisc_1(sK2) | v1_xboole_0(k1_zfmisc_1(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 0.21/0.60    inference(duplicate_literal_removal,[],[f484])).
% 0.21/0.60  fof(f484,plain,(
% 0.21/0.60    sK3 = k1_zfmisc_1(sK2) | v1_xboole_0(k1_zfmisc_1(sK2)) | sK3 = k1_zfmisc_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 0.21/0.60    inference(resolution,[],[f380,f73])).
% 0.21/0.60  fof(f73,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~r2_hidden(sK7(X0,X1),X1) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f40])).
% 0.21/0.60  fof(f40,plain,(
% 0.21/0.60    ! [X0,X1] : (X0 = X1 | (~r2_hidden(sK7(X0,X1),X1) & m1_subset_1(sK7(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f21,f39])).
% 0.21/0.60  fof(f39,plain,(
% 0.21/0.60    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & m1_subset_1(sK7(X0,X1),X0)))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f21,plain,(
% 0.21/0.60    ! [X0,X1] : (X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.60    inference(flattening,[],[f20])).
% 0.21/0.60  fof(f20,plain,(
% 0.21/0.60    ! [X0,X1] : ((X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.60    inference(ennf_transformation,[],[f5])).
% 0.21/0.60  fof(f5,axiom,(
% 0.21/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).
% 0.21/0.60  fof(f380,plain,(
% 0.21/0.60    r2_hidden(sK7(k1_zfmisc_1(sK2),sK3),sK3) | sK3 = k1_zfmisc_1(sK2) | v1_xboole_0(k1_zfmisc_1(sK2))),
% 0.21/0.60    inference(resolution,[],[f371,f310])).
% 0.21/0.60  fof(f310,plain,(
% 0.21/0.60    r1_tarski(sK7(k1_zfmisc_1(sK2),sK3),sK2) | sK3 = k1_zfmisc_1(sK2) | v1_xboole_0(k1_zfmisc_1(sK2))),
% 0.21/0.60    inference(resolution,[],[f207,f93])).
% 0.21/0.60  fof(f207,plain,(
% 0.21/0.60    r2_hidden(sK7(k1_zfmisc_1(sK2),sK3),k1_zfmisc_1(sK2)) | v1_xboole_0(k1_zfmisc_1(sK2)) | sK3 = k1_zfmisc_1(sK2)),
% 0.21/0.60    inference(resolution,[],[f203,f71])).
% 0.21/0.60  fof(f203,plain,(
% 0.21/0.60    m1_subset_1(sK7(k1_zfmisc_1(sK2),sK3),k1_zfmisc_1(sK2)) | sK3 = k1_zfmisc_1(sK2)),
% 0.21/0.60    inference(resolution,[],[f72,f100])).
% 0.21/0.60  fof(f72,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(sK7(X0,X1),X0) | X0 = X1) )),
% 0.21/0.60    inference(cnf_transformation,[],[f40])).
% 0.21/0.60  fof(f99,plain,(
% 0.21/0.60    v1_subset_1(sK3,k1_zfmisc_1(sK2))),
% 0.21/0.60    inference(backward_demodulation,[],[f57,f98])).
% 0.21/0.60  fof(f57,plain,(
% 0.21/0.60    v1_subset_1(sK3,u1_struct_0(k3_yellow_1(sK2)))),
% 0.21/0.60    inference(cnf_transformation,[],[f32])).
% 0.21/0.60  % SZS output end Proof for theBenchmark
% 1.66/0.60  % (21621)------------------------------
% 1.66/0.60  % (21621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.60  % (21621)Termination reason: Refutation
% 1.66/0.60  
% 1.66/0.60  % (21621)Memory used [KB]: 6908
% 1.66/0.60  % (21621)Time elapsed: 0.153 s
% 1.66/0.60  % (21621)------------------------------
% 1.66/0.60  % (21621)------------------------------
% 1.66/0.61  % (21622)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.66/0.61  % (21613)Success in time 0.24 s
%------------------------------------------------------------------------------
