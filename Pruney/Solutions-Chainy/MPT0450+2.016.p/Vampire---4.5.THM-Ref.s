%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:19 EST 2020

% Result     : Theorem 1.75s
% Output     : Refutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 254 expanded)
%              Number of leaves         :   17 (  81 expanded)
%              Depth                    :   16
%              Number of atoms          :  256 ( 791 expanded)
%              Number of equality atoms :   32 ( 162 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f242,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f80,f92,f97,f241])).

fof(f241,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f224,f91])).

fof(f91,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl3_4
  <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f224,plain,(
    ! [X2,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X2,X2,X2,X1)),X1) ),
    inference(superposition,[],[f48,f219])).

% (27759)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f219,plain,(
    ! [X0,X1] : k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) ),
    inference(duplicate_literal_removal,[],[f213])).

fof(f213,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))))
      | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) ) ),
    inference(resolution,[],[f108,f128])).

fof(f128,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK2(X2,X3,X3),X2)
      | k1_setfam_1(k2_enumset1(X2,X2,X2,X3)) = X3 ) ),
    inference(subsumption_resolution,[],[f125,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1,X1),X1)
      | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X1 ) ),
    inference(factoring,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f43,f46])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f33,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f34,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f34,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f125,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK2(X2,X3,X3),X3)
      | ~ r2_hidden(sK2(X2,X3,X3),X2)
      | k1_setfam_1(k2_enumset1(X2,X2,X2,X3)) = X3 ) ),
    inference(duplicate_literal_removal,[],[f120])).

fof(f120,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK2(X2,X3,X3),X3)
      | ~ r2_hidden(sK2(X2,X3,X3),X2)
      | k1_setfam_1(k2_enumset1(X2,X2,X2,X3)) = X3
      | k1_setfam_1(k2_enumset1(X2,X2,X2,X3)) = X3 ) ),
    inference(resolution,[],[f50,f102])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f44,f46])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f108,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK2(X3,k1_setfam_1(k2_enumset1(X4,X4,X4,X5)),k1_setfam_1(k2_enumset1(X4,X4,X4,X5))),X5)
      | k1_setfam_1(k2_enumset1(X4,X4,X4,X5)) = k1_setfam_1(k2_enumset1(X3,X3,X3,k1_setfam_1(k2_enumset1(X4,X4,X4,X5)))) ) ),
    inference(resolution,[],[f102,f57])).

fof(f57,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f40,f46])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f32,f46])).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f97,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f96])).

fof(f96,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f95,f27])).

fof(f27,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).

fof(f95,plain,
    ( ~ v1_relat_1(sK0)
    | spl3_3 ),
    inference(resolution,[],[f93,f59])).

fof(f59,plain,(
    ! [X0,X1] : m1_subset_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f48,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f93,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl3_3 ),
    inference(resolution,[],[f87,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f87,plain,
    ( ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl3_3
  <=> v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f92,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_2 ),
    inference(avatar_split_clause,[],[f83,f70,f89,f85])).

fof(f70,plain,
    ( spl3_2
  <=> r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f83,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1)
    | ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))
    | spl3_2 ),
    inference(subsumption_resolution,[],[f82,f28])).

fof(f28,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f82,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))
    | spl3_2 ),
    inference(resolution,[],[f72,f30])).

% (27764)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (27774)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% (27760)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% (27765)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (27775)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% (27752)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% (27766)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (27754)Refutation not found, incomplete strategy% (27754)------------------------------
% (27754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27754)Termination reason: Refutation not found, incomplete strategy

% (27754)Memory used [KB]: 10618
% (27754)Time elapsed: 0.184 s
% (27754)------------------------------
% (27754)------------------------------
% (27770)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (27766)Refutation not found, incomplete strategy% (27766)------------------------------
% (27766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27766)Termination reason: Refutation not found, incomplete strategy

% (27766)Memory used [KB]: 10746
% (27766)Time elapsed: 0.193 s
% (27766)------------------------------
% (27766)------------------------------
% (27757)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(f72,plain,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f80,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f78,f27])).

fof(f78,plain,
    ( ~ v1_relat_1(sK0)
    | spl3_1 ),
    inference(resolution,[],[f77,f59])).

fof(f77,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl3_1 ),
    inference(resolution,[],[f76,f31])).

fof(f76,plain,
    ( ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))
    | spl3_1 ),
    inference(subsumption_resolution,[],[f75,f27])).

fof(f75,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))
    | spl3_1 ),
    inference(subsumption_resolution,[],[f74,f48])).

fof(f74,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))
    | spl3_1 ),
    inference(resolution,[],[f68,f30])).

fof(f68,plain,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl3_1
  <=> r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f73,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f64,f70,f66])).

fof(f64,plain,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK1))
    | ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK0)) ),
    inference(resolution,[],[f49,f47])).

fof(f47,plain,(
    ~ r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK1)))) ),
    inference(definition_unfolding,[],[f29,f46,f46])).

fof(f29,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f46])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:52:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.56  % (27755)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % (27753)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.56  % (27763)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.56  % (27755)Refutation not found, incomplete strategy% (27755)------------------------------
% 0.21/0.56  % (27755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (27755)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (27755)Memory used [KB]: 10618
% 0.21/0.56  % (27755)Time elapsed: 0.125 s
% 0.21/0.56  % (27755)------------------------------
% 0.21/0.56  % (27755)------------------------------
% 0.21/0.57  % (27769)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.57  % (27771)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.57  % (27763)Refutation not found, incomplete strategy% (27763)------------------------------
% 0.21/0.57  % (27763)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (27763)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (27763)Memory used [KB]: 10618
% 0.21/0.57  % (27763)Time elapsed: 0.136 s
% 0.21/0.57  % (27763)------------------------------
% 0.21/0.57  % (27763)------------------------------
% 0.21/0.57  % (27761)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.58  % (27750)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.59  % (27754)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.59  % (27747)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.75/0.59  % (27773)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.75/0.59  % (27762)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.75/0.59  % (27768)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.75/0.59  % (27756)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.75/0.59  % (27749)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.75/0.59  % (27767)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.75/0.60  % (27756)Refutation not found, incomplete strategy% (27756)------------------------------
% 1.75/0.60  % (27756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.60  % (27756)Termination reason: Refutation not found, incomplete strategy
% 1.75/0.60  
% 1.75/0.60  % (27756)Memory used [KB]: 10618
% 1.75/0.60  % (27756)Time elapsed: 0.172 s
% 1.75/0.60  % (27756)------------------------------
% 1.75/0.60  % (27756)------------------------------
% 1.75/0.60  % (27758)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.75/0.60  % (27767)Refutation not found, incomplete strategy% (27767)------------------------------
% 1.75/0.60  % (27767)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.60  % (27767)Termination reason: Refutation not found, incomplete strategy
% 1.75/0.60  
% 1.75/0.60  % (27767)Memory used [KB]: 1663
% 1.75/0.60  % (27767)Time elapsed: 0.128 s
% 1.75/0.60  % (27767)------------------------------
% 1.75/0.60  % (27767)------------------------------
% 1.75/0.60  % (27746)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.75/0.60  % (27748)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.75/0.60  % (27751)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.75/0.60  % (27748)Refutation not found, incomplete strategy% (27748)------------------------------
% 1.75/0.60  % (27748)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.60  % (27748)Termination reason: Refutation not found, incomplete strategy
% 1.75/0.60  
% 1.75/0.60  % (27748)Memory used [KB]: 10618
% 1.75/0.60  % (27748)Time elapsed: 0.169 s
% 1.75/0.60  % (27748)------------------------------
% 1.75/0.60  % (27748)------------------------------
% 1.75/0.60  % (27772)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.75/0.60  % (27749)Refutation found. Thanks to Tanya!
% 1.75/0.60  % SZS status Theorem for theBenchmark
% 1.75/0.60  % SZS output start Proof for theBenchmark
% 1.75/0.60  fof(f242,plain,(
% 1.75/0.60    $false),
% 1.75/0.60    inference(avatar_sat_refutation,[],[f73,f80,f92,f97,f241])).
% 1.75/0.60  fof(f241,plain,(
% 1.75/0.60    spl3_4),
% 1.75/0.60    inference(avatar_contradiction_clause,[],[f236])).
% 1.75/0.60  fof(f236,plain,(
% 1.75/0.60    $false | spl3_4),
% 1.75/0.60    inference(resolution,[],[f224,f91])).
% 1.75/0.60  fof(f91,plain,(
% 1.75/0.60    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) | spl3_4),
% 1.75/0.60    inference(avatar_component_clause,[],[f89])).
% 1.75/0.60  fof(f89,plain,(
% 1.75/0.60    spl3_4 <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1)),
% 1.75/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.75/0.60  fof(f224,plain,(
% 1.75/0.60    ( ! [X2,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X2,X2,X2,X1)),X1)) )),
% 1.75/0.60    inference(superposition,[],[f48,f219])).
% 1.75/0.60  % (27759)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.75/0.60  fof(f219,plain,(
% 1.75/0.60    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))))) )),
% 1.75/0.60    inference(duplicate_literal_removal,[],[f213])).
% 1.75/0.60  fof(f213,plain,(
% 1.75/0.60    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))))) )),
% 1.75/0.60    inference(resolution,[],[f108,f128])).
% 1.75/0.60  fof(f128,plain,(
% 1.75/0.60    ( ! [X2,X3] : (~r2_hidden(sK2(X2,X3,X3),X2) | k1_setfam_1(k2_enumset1(X2,X2,X2,X3)) = X3) )),
% 1.75/0.60    inference(subsumption_resolution,[],[f125,f102])).
% 1.75/0.60  fof(f102,plain,(
% 1.75/0.60    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,X1),X1) | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X1) )),
% 1.75/0.60    inference(factoring,[],[f51])).
% 1.75/0.60  fof(f51,plain,(
% 1.75/0.60    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X1) | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2) )),
% 1.75/0.60    inference(definition_unfolding,[],[f43,f46])).
% 1.75/0.60  fof(f46,plain,(
% 1.75/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 1.75/0.60    inference(definition_unfolding,[],[f33,f45])).
% 1.75/0.60  fof(f45,plain,(
% 1.75/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.75/0.60    inference(definition_unfolding,[],[f34,f37])).
% 1.75/0.60  fof(f37,plain,(
% 1.75/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.75/0.60    inference(cnf_transformation,[],[f5])).
% 1.75/0.60  fof(f5,axiom,(
% 1.75/0.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.75/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.75/0.60  fof(f34,plain,(
% 1.75/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.75/0.60    inference(cnf_transformation,[],[f4])).
% 1.75/0.60  fof(f4,axiom,(
% 1.75/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.75/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.75/0.60  fof(f33,plain,(
% 1.75/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.75/0.60    inference(cnf_transformation,[],[f6])).
% 1.75/0.60  fof(f6,axiom,(
% 1.75/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.75/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.75/0.60  fof(f43,plain,(
% 1.75/0.60    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.75/0.60    inference(cnf_transformation,[],[f26])).
% 1.75/0.60  fof(f26,plain,(
% 1.75/0.60    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.75/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).
% 1.75/0.60  fof(f25,plain,(
% 1.75/0.60    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.75/0.60    introduced(choice_axiom,[])).
% 1.75/0.60  fof(f24,plain,(
% 1.75/0.60    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.75/0.60    inference(rectify,[],[f23])).
% 1.75/0.61  fof(f23,plain,(
% 1.75/0.61    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.75/0.61    inference(flattening,[],[f22])).
% 1.75/0.61  fof(f22,plain,(
% 1.75/0.61    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.75/0.61    inference(nnf_transformation,[],[f1])).
% 1.75/0.61  fof(f1,axiom,(
% 1.75/0.61    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.75/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.75/0.61  fof(f125,plain,(
% 1.75/0.61    ( ! [X2,X3] : (~r2_hidden(sK2(X2,X3,X3),X3) | ~r2_hidden(sK2(X2,X3,X3),X2) | k1_setfam_1(k2_enumset1(X2,X2,X2,X3)) = X3) )),
% 1.75/0.61    inference(duplicate_literal_removal,[],[f120])).
% 1.75/0.61  fof(f120,plain,(
% 1.75/0.61    ( ! [X2,X3] : (~r2_hidden(sK2(X2,X3,X3),X3) | ~r2_hidden(sK2(X2,X3,X3),X2) | k1_setfam_1(k2_enumset1(X2,X2,X2,X3)) = X3 | k1_setfam_1(k2_enumset1(X2,X2,X2,X3)) = X3) )),
% 1.75/0.61    inference(resolution,[],[f50,f102])).
% 1.75/0.61  fof(f50,plain,(
% 1.75/0.61    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X2) | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X2) )),
% 1.75/0.61    inference(definition_unfolding,[],[f44,f46])).
% 1.75/0.61  fof(f44,plain,(
% 1.75/0.61    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.75/0.61    inference(cnf_transformation,[],[f26])).
% 1.75/0.61  fof(f108,plain,(
% 1.75/0.61    ( ! [X4,X5,X3] : (r2_hidden(sK2(X3,k1_setfam_1(k2_enumset1(X4,X4,X4,X5)),k1_setfam_1(k2_enumset1(X4,X4,X4,X5))),X5) | k1_setfam_1(k2_enumset1(X4,X4,X4,X5)) = k1_setfam_1(k2_enumset1(X3,X3,X3,k1_setfam_1(k2_enumset1(X4,X4,X4,X5))))) )),
% 1.75/0.61    inference(resolution,[],[f102,f57])).
% 1.75/0.61  fof(f57,plain,(
% 1.75/0.61    ( ! [X4,X0,X1] : (~r2_hidden(X4,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | r2_hidden(X4,X1)) )),
% 1.75/0.61    inference(equality_resolution,[],[f54])).
% 1.75/0.61  fof(f54,plain,(
% 1.75/0.61    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) != X2) )),
% 1.75/0.61    inference(definition_unfolding,[],[f40,f46])).
% 1.75/0.61  fof(f40,plain,(
% 1.75/0.61    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.75/0.61    inference(cnf_transformation,[],[f26])).
% 1.75/0.61  fof(f48,plain,(
% 1.75/0.61    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 1.75/0.61    inference(definition_unfolding,[],[f32,f46])).
% 1.75/0.61  fof(f32,plain,(
% 1.75/0.61    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.75/0.61    inference(cnf_transformation,[],[f2])).
% 1.75/0.61  fof(f2,axiom,(
% 1.75/0.61    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.75/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.75/0.61  fof(f97,plain,(
% 1.75/0.61    spl3_3),
% 1.75/0.61    inference(avatar_contradiction_clause,[],[f96])).
% 1.75/0.61  fof(f96,plain,(
% 1.75/0.61    $false | spl3_3),
% 1.75/0.61    inference(subsumption_resolution,[],[f95,f27])).
% 1.75/0.61  fof(f27,plain,(
% 1.75/0.61    v1_relat_1(sK0)),
% 1.75/0.61    inference(cnf_transformation,[],[f20])).
% 1.75/0.61  fof(f20,plain,(
% 1.75/0.61    (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 1.75/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f19,f18])).
% 1.75/0.61  fof(f18,plain,(
% 1.75/0.61    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 1.75/0.61    introduced(choice_axiom,[])).
% 1.75/0.61  fof(f19,plain,(
% 1.75/0.61    ? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) & v1_relat_1(sK1))),
% 1.75/0.61    introduced(choice_axiom,[])).
% 1.75/0.61  fof(f12,plain,(
% 1.75/0.61    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.75/0.61    inference(ennf_transformation,[],[f11])).
% 1.75/0.61  fof(f11,negated_conjecture,(
% 1.75/0.61    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 1.75/0.61    inference(negated_conjecture,[],[f10])).
% 1.75/0.61  fof(f10,conjecture,(
% 1.75/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 1.75/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).
% 1.75/0.61  fof(f95,plain,(
% 1.75/0.61    ~v1_relat_1(sK0) | spl3_3),
% 1.75/0.61    inference(resolution,[],[f93,f59])).
% 1.75/0.61  fof(f59,plain,(
% 1.75/0.61    ( ! [X0,X1] : (m1_subset_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_zfmisc_1(X0))) )),
% 1.75/0.61    inference(resolution,[],[f48,f36])).
% 1.75/0.61  fof(f36,plain,(
% 1.75/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.75/0.61    inference(cnf_transformation,[],[f21])).
% 1.75/0.61  fof(f21,plain,(
% 1.75/0.61    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.75/0.61    inference(nnf_transformation,[],[f7])).
% 1.75/0.61  fof(f7,axiom,(
% 1.75/0.61    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.75/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.75/0.61  fof(f93,plain,(
% 1.75/0.61    ( ! [X0] : (~m1_subset_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl3_3),
% 1.75/0.61    inference(resolution,[],[f87,f31])).
% 1.75/0.61  fof(f31,plain,(
% 1.75/0.61    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.75/0.61    inference(cnf_transformation,[],[f15])).
% 1.75/0.61  fof(f15,plain,(
% 1.75/0.61    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.75/0.61    inference(ennf_transformation,[],[f8])).
% 1.75/0.61  fof(f8,axiom,(
% 1.75/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.75/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.75/0.61  fof(f87,plain,(
% 1.75/0.61    ~v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) | spl3_3),
% 1.75/0.61    inference(avatar_component_clause,[],[f85])).
% 1.75/0.61  fof(f85,plain,(
% 1.75/0.61    spl3_3 <=> v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 1.75/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.75/0.61  fof(f92,plain,(
% 1.75/0.61    ~spl3_3 | ~spl3_4 | spl3_2),
% 1.75/0.61    inference(avatar_split_clause,[],[f83,f70,f89,f85])).
% 1.75/0.61  fof(f70,plain,(
% 1.75/0.61    spl3_2 <=> r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK1))),
% 1.75/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.75/0.61  fof(f83,plain,(
% 1.75/0.61    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) | ~v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) | spl3_2),
% 1.75/0.61    inference(subsumption_resolution,[],[f82,f28])).
% 1.75/0.61  fof(f28,plain,(
% 1.75/0.61    v1_relat_1(sK1)),
% 1.75/0.61    inference(cnf_transformation,[],[f20])).
% 1.75/0.61  fof(f82,plain,(
% 1.75/0.61    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) | spl3_2),
% 1.75/0.61    inference(resolution,[],[f72,f30])).
% 1.75/0.61  % (27764)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.75/0.61  % (27774)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.75/0.61  % (27760)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.90/0.61  % (27765)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.90/0.61  % (27775)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.90/0.61  % (27752)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.90/0.61  % (27766)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.90/0.61  % (27754)Refutation not found, incomplete strategy% (27754)------------------------------
% 1.90/0.61  % (27754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.61  % (27754)Termination reason: Refutation not found, incomplete strategy
% 1.90/0.61  
% 1.90/0.61  % (27754)Memory used [KB]: 10618
% 1.90/0.61  % (27754)Time elapsed: 0.184 s
% 1.90/0.61  % (27754)------------------------------
% 1.90/0.61  % (27754)------------------------------
% 1.90/0.61  % (27770)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.90/0.61  % (27766)Refutation not found, incomplete strategy% (27766)------------------------------
% 1.90/0.61  % (27766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.61  % (27766)Termination reason: Refutation not found, incomplete strategy
% 1.90/0.61  
% 1.90/0.61  % (27766)Memory used [KB]: 10746
% 1.90/0.61  % (27766)Time elapsed: 0.193 s
% 1.90/0.61  % (27766)------------------------------
% 1.90/0.61  % (27766)------------------------------
% 1.90/0.61  % (27757)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 2.02/0.62  fof(f30,plain,(
% 2.02/0.62    ( ! [X0,X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.02/0.62    inference(cnf_transformation,[],[f14])).
% 2.02/0.62  fof(f14,plain,(
% 2.02/0.62    ! [X0] : (! [X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.02/0.62    inference(flattening,[],[f13])).
% 2.02/0.62  fof(f13,plain,(
% 2.02/0.62    ! [X0] : (! [X1] : ((r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.02/0.62    inference(ennf_transformation,[],[f9])).
% 2.02/0.62  fof(f9,axiom,(
% 2.02/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 2.02/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).
% 2.02/0.62  fof(f72,plain,(
% 2.02/0.62    ~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK1)) | spl3_2),
% 2.02/0.62    inference(avatar_component_clause,[],[f70])).
% 2.02/0.62  fof(f80,plain,(
% 2.02/0.62    spl3_1),
% 2.02/0.62    inference(avatar_contradiction_clause,[],[f79])).
% 2.02/0.62  fof(f79,plain,(
% 2.02/0.62    $false | spl3_1),
% 2.02/0.62    inference(subsumption_resolution,[],[f78,f27])).
% 2.02/0.62  fof(f78,plain,(
% 2.02/0.62    ~v1_relat_1(sK0) | spl3_1),
% 2.02/0.62    inference(resolution,[],[f77,f59])).
% 2.02/0.62  fof(f77,plain,(
% 2.02/0.62    ( ! [X0] : (~m1_subset_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl3_1),
% 2.02/0.62    inference(resolution,[],[f76,f31])).
% 2.02/0.62  fof(f76,plain,(
% 2.02/0.62    ~v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) | spl3_1),
% 2.02/0.62    inference(subsumption_resolution,[],[f75,f27])).
% 2.02/0.62  fof(f75,plain,(
% 2.02/0.62    ~v1_relat_1(sK0) | ~v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) | spl3_1),
% 2.02/0.62    inference(subsumption_resolution,[],[f74,f48])).
% 2.02/0.62  fof(f74,plain,(
% 2.02/0.62    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) | spl3_1),
% 2.02/0.62    inference(resolution,[],[f68,f30])).
% 2.02/0.62  fof(f68,plain,(
% 2.02/0.62    ~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK0)) | spl3_1),
% 2.02/0.62    inference(avatar_component_clause,[],[f66])).
% 2.02/0.62  fof(f66,plain,(
% 2.02/0.62    spl3_1 <=> r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK0))),
% 2.02/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.02/0.62  fof(f73,plain,(
% 2.02/0.62    ~spl3_1 | ~spl3_2),
% 2.02/0.62    inference(avatar_split_clause,[],[f64,f70,f66])).
% 2.02/0.62  fof(f64,plain,(
% 2.02/0.62    ~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK1)) | ~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k3_relat_1(sK0))),
% 2.02/0.62    inference(resolution,[],[f49,f47])).
% 2.02/0.62  fof(f47,plain,(
% 2.02/0.62    ~r1_tarski(k3_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK1))))),
% 2.02/0.62    inference(definition_unfolding,[],[f29,f46,f46])).
% 2.02/0.62  fof(f29,plain,(
% 2.02/0.62    ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))),
% 2.02/0.62    inference(cnf_transformation,[],[f20])).
% 2.02/0.62  fof(f49,plain,(
% 2.02/0.62    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.02/0.62    inference(definition_unfolding,[],[f38,f46])).
% 2.02/0.62  fof(f38,plain,(
% 2.02/0.62    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.02/0.62    inference(cnf_transformation,[],[f17])).
% 2.02/0.62  fof(f17,plain,(
% 2.02/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 2.02/0.62    inference(flattening,[],[f16])).
% 2.02/0.62  fof(f16,plain,(
% 2.02/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 2.02/0.62    inference(ennf_transformation,[],[f3])).
% 2.02/0.62  fof(f3,axiom,(
% 2.02/0.62    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 2.02/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 2.02/0.62  % SZS output end Proof for theBenchmark
% 2.02/0.62  % (27749)------------------------------
% 2.02/0.62  % (27749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.02/0.62  % (27749)Termination reason: Refutation
% 2.02/0.62  
% 2.02/0.62  % (27749)Memory used [KB]: 10874
% 2.02/0.62  % (27749)Time elapsed: 0.174 s
% 2.02/0.62  % (27749)------------------------------
% 2.02/0.62  % (27749)------------------------------
% 2.02/0.63  % (27745)Success in time 0.255 s
%------------------------------------------------------------------------------
