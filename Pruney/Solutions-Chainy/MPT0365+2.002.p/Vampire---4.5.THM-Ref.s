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
% DateTime   : Thu Dec  3 12:45:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 276 expanded)
%              Number of leaves         :   17 (  85 expanded)
%              Depth                    :   18
%              Number of atoms          :  283 (1164 expanded)
%              Number of equality atoms :   35 ( 215 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f276,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f110,f120,f150,f275])).

fof(f275,plain,(
    ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f274])).

% (27831)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
fof(f274,plain,
    ( $false
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f273,f71])).

fof(f71,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f64,f58])).

fof(f58,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f64,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f62,f37])).

fof(f37,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f62,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f32,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

% (27828)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( sK1 != k3_subset_1(sK0,sK2)
    & r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2))
    & r1_xboole_0(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f22,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k3_subset_1(X0,X2) != X1
            & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
            & r1_xboole_0(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( sK1 != k3_subset_1(sK0,X2)
          & r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,X2))
          & r1_xboole_0(sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] :
        ( sK1 != k3_subset_1(sK0,X2)
        & r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,X2))
        & r1_xboole_0(sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( sK1 != k3_subset_1(sK0,sK2)
      & r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2))
      & r1_xboole_0(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
          & r1_xboole_0(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
          & r1_xboole_0(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ( r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
                & r1_xboole_0(X1,X2) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ( r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
              & r1_xboole_0(X1,X2) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_subset_1)).

fof(f273,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f272,f34])).

fof(f34,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f272,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | ~ r1_tarski(sK1,sK0)
    | ~ spl4_8 ),
    inference(resolution,[],[f270,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f270,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f269,f174])).

fof(f174,plain,(
    sK1 != k4_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f36,f67])).

fof(f67,plain,(
    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f33,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f36,plain,(
    sK1 != k3_subset_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f269,plain,
    ( sK1 = k4_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl4_8 ),
    inference(resolution,[],[f252,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

% (27822)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f252,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f248,f172])).

fof(f172,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,sK2),sK2)
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f162,f67])).

fof(f162,plain,
    ( r1_xboole_0(k3_subset_1(sK0,sK2),sK2)
    | ~ spl4_8 ),
    inference(resolution,[],[f158,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f158,plain,
    ( r1_xboole_0(sK2,k3_subset_1(sK0,sK2))
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f132,f152])).

fof(f152,plain,
    ( sK2 = k4_xboole_0(sK0,sK1)
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f61,f119])).

fof(f119,plain,
    ( k3_subset_1(sK0,sK1) = sK2
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl4_8
  <=> k3_subset_1(sK0,sK1) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f61,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f32,f44])).

fof(f132,plain,(
    r1_xboole_0(k4_xboole_0(sK0,sK1),k3_subset_1(sK0,sK2)) ),
    inference(backward_demodulation,[],[f35,f61])).

fof(f35,plain,(
    r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f248,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),sK1)
    | ~ r1_xboole_0(k4_xboole_0(sK0,sK2),sK2)
    | ~ spl4_8 ),
    inference(resolution,[],[f155,f178])).

fof(f178,plain,(
    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f176,f33])).

fof(f176,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f43,f67])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f155,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | r1_tarski(X0,sK1)
        | ~ r1_xboole_0(X0,sK2) )
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f153,f32])).

fof(f153,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,sK2)
        | r1_tarski(X0,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) )
    | ~ spl4_8 ),
    inference(superposition,[],[f45,f119])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,k3_subset_1(X0,X2))
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(X1,X2)
              | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

fof(f150,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | spl4_7 ),
    inference(subsumption_resolution,[],[f148,f83])).

fof(f83,plain,(
    r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f70,f58])).

fof(f70,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f68,f37])).

fof(f68,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f33,f38])).

fof(f148,plain,
    ( ~ r1_tarski(sK2,sK0)
    | spl4_7 ),
    inference(subsumption_resolution,[],[f147,f59])).

fof(f59,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f34,f42])).

fof(f147,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | ~ r1_tarski(sK2,sK0)
    | spl4_7 ),
    inference(resolution,[],[f130,f54])).

fof(f130,plain,
    ( ~ r1_tarski(sK2,k4_xboole_0(sK0,sK1))
    | spl4_7 ),
    inference(backward_demodulation,[],[f115,f61])).

fof(f115,plain,
    ( ~ r1_tarski(sK2,k3_subset_1(sK0,sK1))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl4_7
  <=> r1_tarski(sK2,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f120,plain,
    ( ~ spl4_7
    | spl4_8
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f111,f93,f117,f113])).

fof(f93,plain,
    ( spl4_4
  <=> r1_tarski(k3_subset_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f111,plain,
    ( k3_subset_1(sK0,sK1) = sK2
    | ~ r1_tarski(sK2,k3_subset_1(sK0,sK1))
    | ~ spl4_4 ),
    inference(resolution,[],[f95,f49])).

fof(f95,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f110,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f109])).

fof(f109,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f107,f32])).

fof(f107,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl4_3 ),
    inference(resolution,[],[f91,f43])).

fof(f91,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl4_3
  <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f96,plain,
    ( ~ spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f87,f93,f89])).

fof(f87,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK2)
    | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f85,f33])).

fof(f85,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f35,f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:44:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (27817)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (27818)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.51  % (27820)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  % (27832)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.51  % (27824)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.51  % (27817)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.52  % (27829)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (27816)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.52  % (27840)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f276,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f96,f110,f120,f150,f275])).
% 0.20/0.52  fof(f275,plain,(
% 0.20/0.52    ~spl4_8),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f274])).
% 0.20/0.52  % (27831)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.52  fof(f274,plain,(
% 0.20/0.52    $false | ~spl4_8),
% 0.20/0.52    inference(subsumption_resolution,[],[f273,f71])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    r1_tarski(sK1,sK0)),
% 0.20/0.52    inference(resolution,[],[f64,f58])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.52    inference(rectify,[],[f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.52    inference(nnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.52    inference(subsumption_resolution,[],[f62,f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.20/0.52    inference(resolution,[],[f32,f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.20/0.52    inference(nnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  % (27828)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    (sK1 != k3_subset_1(sK0,sK2) & r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)) & r1_xboole_0(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f22,f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (sK1 != k3_subset_1(sK0,X2) & r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,X2)) & r1_xboole_0(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ? [X2] : (sK1 != k3_subset_1(sK0,X2) & r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,X2)) & r1_xboole_0(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (sK1 != k3_subset_1(sK0,sK2) & r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)) & r1_xboole_0(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(flattening,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ? [X0,X1] : (? [X2] : ((k3_subset_1(X0,X2) != X1 & (r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2)) => k3_subset_1(X0,X2) = X1)))),
% 0.20/0.52    inference(negated_conjecture,[],[f10])).
% 0.20/0.52  fof(f10,conjecture,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2)) => k3_subset_1(X0,X2) = X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_subset_1)).
% 0.20/0.52  fof(f273,plain,(
% 0.20/0.52    ~r1_tarski(sK1,sK0) | ~spl4_8),
% 0.20/0.52    inference(subsumption_resolution,[],[f272,f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    r1_xboole_0(sK1,sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f272,plain,(
% 0.20/0.52    ~r1_xboole_0(sK1,sK2) | ~r1_tarski(sK1,sK0) | ~spl4_8),
% 0.20/0.52    inference(resolution,[],[f270,f54])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.52    inference(flattening,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).
% 0.20/0.52  fof(f270,plain,(
% 0.20/0.52    ~r1_tarski(sK1,k4_xboole_0(sK0,sK2)) | ~spl4_8),
% 0.20/0.52    inference(subsumption_resolution,[],[f269,f174])).
% 0.20/0.52  fof(f174,plain,(
% 0.20/0.52    sK1 != k4_xboole_0(sK0,sK2)),
% 0.20/0.52    inference(superposition,[],[f36,f67])).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 0.20/0.52    inference(resolution,[],[f33,f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    sK1 != k3_subset_1(sK0,sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f269,plain,(
% 0.20/0.52    sK1 = k4_xboole_0(sK0,sK2) | ~r1_tarski(sK1,k4_xboole_0(sK0,sK2)) | ~spl4_8),
% 0.20/0.52    inference(resolution,[],[f252,f49])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f27])).
% 0.20/0.52  % (27822)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.52    inference(flattening,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.52    inference(nnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.52  fof(f252,plain,(
% 0.20/0.52    r1_tarski(k4_xboole_0(sK0,sK2),sK1) | ~spl4_8),
% 0.20/0.52    inference(subsumption_resolution,[],[f248,f172])).
% 0.20/0.52  fof(f172,plain,(
% 0.20/0.52    r1_xboole_0(k4_xboole_0(sK0,sK2),sK2) | ~spl4_8),
% 0.20/0.52    inference(backward_demodulation,[],[f162,f67])).
% 0.20/0.52  fof(f162,plain,(
% 0.20/0.52    r1_xboole_0(k3_subset_1(sK0,sK2),sK2) | ~spl4_8),
% 0.20/0.52    inference(resolution,[],[f158,f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.52  fof(f158,plain,(
% 0.20/0.52    r1_xboole_0(sK2,k3_subset_1(sK0,sK2)) | ~spl4_8),
% 0.20/0.52    inference(backward_demodulation,[],[f132,f152])).
% 0.20/0.52  fof(f152,plain,(
% 0.20/0.52    sK2 = k4_xboole_0(sK0,sK1) | ~spl4_8),
% 0.20/0.52    inference(backward_demodulation,[],[f61,f119])).
% 0.20/0.52  fof(f119,plain,(
% 0.20/0.52    k3_subset_1(sK0,sK1) = sK2 | ~spl4_8),
% 0.20/0.52    inference(avatar_component_clause,[],[f117])).
% 0.20/0.52  fof(f117,plain,(
% 0.20/0.52    spl4_8 <=> k3_subset_1(sK0,sK1) = sK2),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.20/0.52    inference(resolution,[],[f32,f44])).
% 0.20/0.52  fof(f132,plain,(
% 0.20/0.52    r1_xboole_0(k4_xboole_0(sK0,sK1),k3_subset_1(sK0,sK2))),
% 0.20/0.52    inference(backward_demodulation,[],[f35,f61])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2))),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f248,plain,(
% 0.20/0.52    r1_tarski(k4_xboole_0(sK0,sK2),sK1) | ~r1_xboole_0(k4_xboole_0(sK0,sK2),sK2) | ~spl4_8),
% 0.20/0.52    inference(resolution,[],[f155,f178])).
% 0.20/0.52  fof(f178,plain,(
% 0.20/0.52    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))),
% 0.20/0.52    inference(subsumption_resolution,[],[f176,f33])).
% 0.20/0.52  fof(f176,plain,(
% 0.20/0.52    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.52    inference(superposition,[],[f43,f67])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.20/0.52  fof(f155,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | r1_tarski(X0,sK1) | ~r1_xboole_0(X0,sK2)) ) | ~spl4_8),
% 0.20/0.52    inference(subsumption_resolution,[],[f153,f32])).
% 0.20/0.52  fof(f153,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_xboole_0(X0,sK2) | r1_tarski(X0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) ) | ~spl4_8),
% 0.20/0.52    inference(superposition,[],[f45,f119])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,k3_subset_1(X0,X2)) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : (((r1_xboole_0(X1,k3_subset_1(X0,X2)) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(nnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).
% 0.20/0.52  fof(f150,plain,(
% 0.20/0.52    spl4_7),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f149])).
% 0.20/0.52  fof(f149,plain,(
% 0.20/0.52    $false | spl4_7),
% 0.20/0.52    inference(subsumption_resolution,[],[f148,f83])).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    r1_tarski(sK2,sK0)),
% 0.20/0.52    inference(resolution,[],[f70,f58])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.52    inference(subsumption_resolution,[],[f68,f37])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    r2_hidden(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.20/0.52    inference(resolution,[],[f33,f38])).
% 0.20/0.52  fof(f148,plain,(
% 0.20/0.52    ~r1_tarski(sK2,sK0) | spl4_7),
% 0.20/0.52    inference(subsumption_resolution,[],[f147,f59])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    r1_xboole_0(sK2,sK1)),
% 0.20/0.52    inference(resolution,[],[f34,f42])).
% 0.20/0.52  fof(f147,plain,(
% 0.20/0.52    ~r1_xboole_0(sK2,sK1) | ~r1_tarski(sK2,sK0) | spl4_7),
% 0.20/0.52    inference(resolution,[],[f130,f54])).
% 0.20/0.52  fof(f130,plain,(
% 0.20/0.52    ~r1_tarski(sK2,k4_xboole_0(sK0,sK1)) | spl4_7),
% 0.20/0.52    inference(backward_demodulation,[],[f115,f61])).
% 0.20/0.52  fof(f115,plain,(
% 0.20/0.52    ~r1_tarski(sK2,k3_subset_1(sK0,sK1)) | spl4_7),
% 0.20/0.52    inference(avatar_component_clause,[],[f113])).
% 0.20/0.52  fof(f113,plain,(
% 0.20/0.52    spl4_7 <=> r1_tarski(sK2,k3_subset_1(sK0,sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.52  fof(f120,plain,(
% 0.20/0.52    ~spl4_7 | spl4_8 | ~spl4_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f111,f93,f117,f113])).
% 0.20/0.52  fof(f93,plain,(
% 0.20/0.52    spl4_4 <=> r1_tarski(k3_subset_1(sK0,sK1),sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.52  fof(f111,plain,(
% 0.20/0.52    k3_subset_1(sK0,sK1) = sK2 | ~r1_tarski(sK2,k3_subset_1(sK0,sK1)) | ~spl4_4),
% 0.20/0.52    inference(resolution,[],[f95,f49])).
% 0.20/0.52  fof(f95,plain,(
% 0.20/0.52    r1_tarski(k3_subset_1(sK0,sK1),sK2) | ~spl4_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f93])).
% 0.20/0.52  fof(f110,plain,(
% 0.20/0.52    spl4_3),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f109])).
% 0.20/0.52  fof(f109,plain,(
% 0.20/0.52    $false | spl4_3),
% 0.20/0.52    inference(subsumption_resolution,[],[f107,f32])).
% 0.20/0.52  fof(f107,plain,(
% 0.20/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl4_3),
% 0.20/0.52    inference(resolution,[],[f91,f43])).
% 0.20/0.52  fof(f91,plain,(
% 0.20/0.52    ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | spl4_3),
% 0.20/0.52    inference(avatar_component_clause,[],[f89])).
% 0.20/0.52  fof(f89,plain,(
% 0.20/0.52    spl4_3 <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.52  fof(f96,plain,(
% 0.20/0.52    ~spl4_3 | spl4_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f87,f93,f89])).
% 0.20/0.52  fof(f87,plain,(
% 0.20/0.52    r1_tarski(k3_subset_1(sK0,sK1),sK2) | ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.20/0.52    inference(subsumption_resolution,[],[f85,f33])).
% 0.20/0.52  fof(f85,plain,(
% 0.20/0.52    r1_tarski(k3_subset_1(sK0,sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.20/0.52    inference(resolution,[],[f35,f45])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (27817)------------------------------
% 0.20/0.52  % (27817)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (27817)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (27817)Memory used [KB]: 10746
% 0.20/0.52  % (27817)Time elapsed: 0.095 s
% 0.20/0.52  % (27817)------------------------------
% 0.20/0.52  % (27817)------------------------------
% 0.20/0.52  % (27819)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.52  % (27815)Success in time 0.164 s
%------------------------------------------------------------------------------
