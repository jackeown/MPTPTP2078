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
% DateTime   : Thu Dec  3 13:05:16 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 154 expanded)
%              Number of leaves         :   14 (  44 expanded)
%              Depth                    :   16
%              Number of atoms          :  238 ( 518 expanded)
%              Number of equality atoms :  103 ( 228 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f156,plain,(
    $false ),
    inference(subsumption_resolution,[],[f153,f47])).

fof(f47,plain,(
    sK4 != k1_funct_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( sK4 != k1_funct_1(sK6,sK5)
    & r2_hidden(sK5,sK3)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
    & v1_funct_2(sK6,sK3,k1_tarski(sK4))
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f15,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( sK4 != k1_funct_1(sK6,sK5)
      & r2_hidden(sK5,sK3)
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
      & v1_funct_2(sK6,sK3,k1_tarski(sK4))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f12])).

% (15216)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

fof(f153,plain,(
    sK4 = k1_funct_1(sK6,sK5) ),
    inference(resolution,[],[f147,f46])).

fof(f46,plain,(
    r2_hidden(sK5,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f147,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | sK4 = k1_funct_1(sK6,X0) ) ),
    inference(duplicate_literal_removal,[],[f145])).

fof(f145,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | sK4 = k1_funct_1(sK6,X0)
      | sK4 = k1_funct_1(sK6,X0) ) ),
    inference(resolution,[],[f144,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k3_enumset1(X0,X0,X0,X0,X2))
      | X0 = X1
      | X1 = X2 ) ),
    inference(resolution,[],[f57,f90])).

fof(f90,plain,(
    ! [X0,X1] : sP0(X1,X0,k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k3_enumset1(X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f63,f80])).

fof(f80,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f56,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f56,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f21])).

fof(f21,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | X1 = X4
      | ~ r2_hidden(X4,X2)
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( sK7(X0,X1,X2) != X0
              & sK7(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( sK7(X0,X1,X2) = X0
            | sK7(X0,X1,X2) = X1
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK7(X0,X1,X2) != X0
            & sK7(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( sK7(X0,X1,X2) = X0
          | sK7(X0,X1,X2) = X1
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ( X0 != X3
                & X1 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X0 = X3
              | X1 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f144,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK6,X0),k3_enumset1(sK4,sK4,sK4,sK4,sK4))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f143,f43])).

fof(f43,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f27])).

fof(f143,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | r2_hidden(k1_funct_1(sK6,X0),k3_enumset1(sK4,sK4,sK4,sK4,sK4))
      | ~ v1_funct_1(sK6) ) ),
    inference(subsumption_resolution,[],[f142,f83])).

fof(f83,plain,(
    v1_funct_2(sK6,sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(definition_unfolding,[],[f44,f81])).

fof(f81,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f49,f80])).

fof(f49,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f44,plain,(
    v1_funct_2(sK6,sK3,k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f27])).

% (15226)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
fof(f142,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | r2_hidden(k1_funct_1(sK6,X0),k3_enumset1(sK4,sK4,sK4,sK4,sK4))
      | ~ v1_funct_2(sK6,sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
      | ~ v1_funct_1(sK6) ) ),
    inference(subsumption_resolution,[],[f141,f115])).

fof(f115,plain,(
    ! [X0] : k1_xboole_0 != k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(subsumption_resolution,[],[f114,f102])).

fof(f102,plain,(
    ! [X0,X1] : r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(resolution,[],[f90,f89])).

fof(f89,plain,(
    ! [X4,X2,X0] :
      ( ~ sP0(X0,X4,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f114,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0))
      | k1_xboole_0 != k3_enumset1(X0,X0,X0,X0,X0) ) ),
    inference(forward_demodulation,[],[f113,f51])).

fof(f51,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f113,plain,(
    ! [X0] :
      ( k1_xboole_0 != k3_enumset1(X0,X0,X0,X0,X0)
      | ~ r2_hidden(X0,k2_relat_1(k6_relat_1(k3_enumset1(X0,X0,X0,X0,X0)))) ) ),
    inference(subsumption_resolution,[],[f112,f48])).

fof(f48,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

% (15216)Refutation not found, incomplete strategy% (15216)------------------------------
% (15216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15216)Termination reason: Refutation not found, incomplete strategy

% (15216)Memory used [KB]: 10746
% (15216)Time elapsed: 0.134 s
% (15216)------------------------------
% (15216)------------------------------
fof(f112,plain,(
    ! [X0] :
      ( k1_xboole_0 != k3_enumset1(X0,X0,X0,X0,X0)
      | ~ r2_hidden(X0,k2_relat_1(k6_relat_1(k3_enumset1(X0,X0,X0,X0,X0))))
      | ~ v1_relat_1(k6_relat_1(k3_enumset1(X0,X0,X0,X0,X0))) ) ),
    inference(superposition,[],[f85,f101])).

fof(f101,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f100,f50])).

fof(f50,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f100,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f99,f51])).

fof(f99,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f52,f48])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,k3_enumset1(X0,X0,X0,X0,X0))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f54,f81])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k2_relat_1(X1))
          | k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0 )
        & ( k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0
          | ~ r2_hidden(X0,k2_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

% (15213)Refutation not found, incomplete strategy% (15213)------------------------------
% (15213)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

% (15229)Refutation not found, incomplete strategy% (15229)------------------------------
% (15229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f141,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_enumset1(sK4,sK4,sK4,sK4,sK4)
      | ~ r2_hidden(X0,sK3)
      | r2_hidden(k1_funct_1(sK6,X0),k3_enumset1(sK4,sK4,sK4,sK4,sK4))
      | ~ v1_funct_2(sK6,sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4))
      | ~ v1_funct_1(sK6) ) ),
    inference(resolution,[],[f66,f82])).

% (15220)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
fof(f82,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))) ),
    inference(definition_unfolding,[],[f45,f81])).

fof(f45,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | r2_hidden(k1_funct_1(X3,X2),X1)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

% (15210)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:11:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (826769409)
% 0.14/0.37  ipcrm: permission denied for id (826867715)
% 0.14/0.37  ipcrm: permission denied for id (826933253)
% 0.14/0.37  ipcrm: permission denied for id (826966022)
% 0.14/0.38  ipcrm: permission denied for id (827064329)
% 0.14/0.38  ipcrm: permission denied for id (827129867)
% 0.14/0.38  ipcrm: permission denied for id (827162637)
% 0.14/0.38  ipcrm: permission denied for id (827228174)
% 0.14/0.38  ipcrm: permission denied for id (827260943)
% 0.14/0.38  ipcrm: permission denied for id (827293712)
% 0.14/0.39  ipcrm: permission denied for id (827326481)
% 0.14/0.39  ipcrm: permission denied for id (827359250)
% 0.14/0.39  ipcrm: permission denied for id (827392019)
% 0.14/0.39  ipcrm: permission denied for id (827424789)
% 0.14/0.39  ipcrm: permission denied for id (827490327)
% 0.14/0.40  ipcrm: permission denied for id (827555865)
% 0.14/0.40  ipcrm: permission denied for id (827654172)
% 0.14/0.40  ipcrm: permission denied for id (827686941)
% 0.14/0.40  ipcrm: permission denied for id (827719710)
% 0.21/0.41  ipcrm: permission denied for id (827883556)
% 0.21/0.41  ipcrm: permission denied for id (827981864)
% 0.21/0.42  ipcrm: permission denied for id (828047402)
% 0.21/0.42  ipcrm: permission denied for id (828178478)
% 0.21/0.42  ipcrm: permission denied for id (828244016)
% 0.21/0.43  ipcrm: permission denied for id (828309555)
% 0.21/0.43  ipcrm: permission denied for id (828342324)
% 0.21/0.43  ipcrm: permission denied for id (828375093)
% 0.21/0.43  ipcrm: permission denied for id (828506168)
% 0.21/0.44  ipcrm: permission denied for id (828604474)
% 0.21/0.44  ipcrm: permission denied for id (828670011)
% 0.21/0.44  ipcrm: permission denied for id (828702780)
% 0.21/0.44  ipcrm: permission denied for id (828735549)
% 0.21/0.44  ipcrm: permission denied for id (828768318)
% 0.21/0.45  ipcrm: permission denied for id (828932164)
% 0.21/0.45  ipcrm: permission denied for id (829063240)
% 0.21/0.45  ipcrm: permission denied for id (829096010)
% 0.21/0.46  ipcrm: permission denied for id (829161548)
% 0.21/0.46  ipcrm: permission denied for id (829227086)
% 0.21/0.47  ipcrm: permission denied for id (829423700)
% 0.21/0.47  ipcrm: permission denied for id (829456469)
% 0.21/0.47  ipcrm: permission denied for id (829522008)
% 0.21/0.47  ipcrm: permission denied for id (829554778)
% 0.21/0.47  ipcrm: permission denied for id (829587547)
% 0.21/0.48  ipcrm: permission denied for id (829751393)
% 0.21/0.48  ipcrm: permission denied for id (829849700)
% 0.21/0.49  ipcrm: permission denied for id (829980776)
% 0.21/0.50  ipcrm: permission denied for id (830111853)
% 0.21/0.50  ipcrm: permission denied for id (830144622)
% 0.21/0.50  ipcrm: permission denied for id (830177391)
% 0.21/0.50  ipcrm: permission denied for id (830210160)
% 0.21/0.51  ipcrm: permission denied for id (830406774)
% 0.21/0.51  ipcrm: permission denied for id (830439543)
% 0.21/0.51  ipcrm: permission denied for id (830505081)
% 0.21/0.51  ipcrm: permission denied for id (830636157)
% 0.21/0.52  ipcrm: permission denied for id (830668926)
% 1.00/0.65  % (15201)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.20/0.66  % (15209)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.20/0.67  % (15207)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.20/0.67  % (15218)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.20/0.67  % (15203)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.20/0.67  % (15205)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.20/0.67  % (15202)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.20/0.68  % (15224)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.20/0.68  % (15198)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.20/0.68  % (15224)Refutation not found, incomplete strategy% (15224)------------------------------
% 1.20/0.68  % (15224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.69  % (15224)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.69  
% 1.20/0.69  % (15224)Memory used [KB]: 10618
% 1.20/0.69  % (15224)Time elapsed: 0.109 s
% 1.20/0.69  % (15224)------------------------------
% 1.20/0.69  % (15224)------------------------------
% 1.20/0.69  % (15206)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.20/0.69  % (15227)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.20/0.69  % (15227)Refutation not found, incomplete strategy% (15227)------------------------------
% 1.20/0.69  % (15227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.69  % (15227)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.69  
% 1.20/0.69  % (15227)Memory used [KB]: 6140
% 1.20/0.69  % (15227)Time elapsed: 0.121 s
% 1.20/0.69  % (15227)------------------------------
% 1.20/0.69  % (15227)------------------------------
% 1.20/0.69  % (15219)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.20/0.69  % (15225)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.20/0.69  % (15211)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.20/0.69  % (15199)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.20/0.70  % (15218)Refutation not found, incomplete strategy% (15218)------------------------------
% 1.20/0.70  % (15218)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.70  % (15218)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.70  
% 1.20/0.70  % (15218)Memory used [KB]: 1918
% 1.20/0.70  % (15218)Time elapsed: 0.111 s
% 1.20/0.70  % (15218)------------------------------
% 1.20/0.70  % (15218)------------------------------
% 1.20/0.70  % (15205)Refutation found. Thanks to Tanya!
% 1.20/0.70  % SZS status Theorem for theBenchmark
% 1.20/0.70  % (15213)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.20/0.70  % (15229)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.20/0.70  % SZS output start Proof for theBenchmark
% 1.20/0.70  fof(f156,plain,(
% 1.20/0.70    $false),
% 1.20/0.70    inference(subsumption_resolution,[],[f153,f47])).
% 1.20/0.70  fof(f47,plain,(
% 1.20/0.70    sK4 != k1_funct_1(sK6,sK5)),
% 1.20/0.70    inference(cnf_transformation,[],[f27])).
% 1.20/0.70  fof(f27,plain,(
% 1.20/0.70    sK4 != k1_funct_1(sK6,sK5) & r2_hidden(sK5,sK3) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4)))) & v1_funct_2(sK6,sK3,k1_tarski(sK4)) & v1_funct_1(sK6)),
% 1.20/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f15,f26])).
% 1.20/0.70  fof(f26,plain,(
% 1.20/0.70    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (sK4 != k1_funct_1(sK6,sK5) & r2_hidden(sK5,sK3) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4)))) & v1_funct_2(sK6,sK3,k1_tarski(sK4)) & v1_funct_1(sK6))),
% 1.20/0.70    introduced(choice_axiom,[])).
% 1.20/0.70  fof(f15,plain,(
% 1.20/0.70    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 1.20/0.70    inference(flattening,[],[f14])).
% 1.20/0.70  fof(f14,plain,(
% 1.20/0.70    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 1.20/0.70    inference(ennf_transformation,[],[f13])).
% 1.20/0.70  fof(f13,negated_conjecture,(
% 1.20/0.70    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.20/0.70    inference(negated_conjecture,[],[f12])).
% 1.20/0.70  % (15216)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.20/0.70  fof(f12,conjecture,(
% 1.20/0.70    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.20/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).
% 1.20/0.70  fof(f153,plain,(
% 1.20/0.70    sK4 = k1_funct_1(sK6,sK5)),
% 1.20/0.70    inference(resolution,[],[f147,f46])).
% 1.20/0.70  fof(f46,plain,(
% 1.20/0.70    r2_hidden(sK5,sK3)),
% 1.20/0.70    inference(cnf_transformation,[],[f27])).
% 1.20/0.70  fof(f147,plain,(
% 1.20/0.70    ( ! [X0] : (~r2_hidden(X0,sK3) | sK4 = k1_funct_1(sK6,X0)) )),
% 1.20/0.70    inference(duplicate_literal_removal,[],[f145])).
% 1.20/0.70  fof(f145,plain,(
% 1.20/0.70    ( ! [X0] : (~r2_hidden(X0,sK3) | sK4 = k1_funct_1(sK6,X0) | sK4 = k1_funct_1(sK6,X0)) )),
% 1.20/0.70    inference(resolution,[],[f144,f105])).
% 1.20/0.70  fof(f105,plain,(
% 1.20/0.70    ( ! [X2,X0,X1] : (~r2_hidden(X1,k3_enumset1(X0,X0,X0,X0,X2)) | X0 = X1 | X1 = X2) )),
% 1.20/0.70    inference(resolution,[],[f57,f90])).
% 1.20/0.70  fof(f90,plain,(
% 1.20/0.70    ( ! [X0,X1] : (sP0(X1,X0,k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.20/0.70    inference(equality_resolution,[],[f87])).
% 1.20/0.70  fof(f87,plain,(
% 1.20/0.70    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k3_enumset1(X0,X0,X0,X0,X1) != X2) )),
% 1.20/0.70    inference(definition_unfolding,[],[f63,f80])).
% 1.20/0.70  fof(f80,plain,(
% 1.20/0.70    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.20/0.70    inference(definition_unfolding,[],[f53,f79])).
% 1.20/0.70  fof(f79,plain,(
% 1.20/0.70    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.20/0.70    inference(definition_unfolding,[],[f56,f65])).
% 1.20/0.70  fof(f65,plain,(
% 1.20/0.70    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.20/0.70    inference(cnf_transformation,[],[f5])).
% 1.20/0.70  fof(f5,axiom,(
% 1.20/0.70    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.20/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.20/0.70  fof(f56,plain,(
% 1.20/0.70    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.20/0.70    inference(cnf_transformation,[],[f4])).
% 1.20/0.70  fof(f4,axiom,(
% 1.20/0.70    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.20/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.20/0.70  fof(f53,plain,(
% 1.20/0.70    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.20/0.70    inference(cnf_transformation,[],[f3])).
% 1.20/0.70  fof(f3,axiom,(
% 1.20/0.70    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.20/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.20/0.70  fof(f63,plain,(
% 1.20/0.70    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 1.20/0.70    inference(cnf_transformation,[],[f34])).
% 1.20/0.70  fof(f34,plain,(
% 1.20/0.70    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 1.20/0.70    inference(nnf_transformation,[],[f22])).
% 1.20/0.70  fof(f22,plain,(
% 1.20/0.70    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.20/0.70    inference(definition_folding,[],[f1,f21])).
% 1.20/0.70  fof(f21,plain,(
% 1.20/0.70    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.20/0.70    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.20/0.70  fof(f1,axiom,(
% 1.20/0.70    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.20/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.20/0.70  fof(f57,plain,(
% 1.20/0.70    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | X1 = X4 | ~r2_hidden(X4,X2) | X0 = X4) )),
% 1.20/0.70    inference(cnf_transformation,[],[f33])).
% 1.20/0.70  fof(f33,plain,(
% 1.20/0.70    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((sK7(X0,X1,X2) != X0 & sK7(X0,X1,X2) != X1) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sK7(X0,X1,X2) = X0 | sK7(X0,X1,X2) = X1 | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.20/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f31,f32])).
% 1.20/0.70  fof(f32,plain,(
% 1.20/0.70    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK7(X0,X1,X2) != X0 & sK7(X0,X1,X2) != X1) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sK7(X0,X1,X2) = X0 | sK7(X0,X1,X2) = X1 | r2_hidden(sK7(X0,X1,X2),X2))))),
% 1.20/0.70    introduced(choice_axiom,[])).
% 1.20/0.70  fof(f31,plain,(
% 1.20/0.70    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.20/0.70    inference(rectify,[],[f30])).
% 1.20/0.70  fof(f30,plain,(
% 1.20/0.70    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.20/0.70    inference(flattening,[],[f29])).
% 1.20/0.70  fof(f29,plain,(
% 1.20/0.70    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.20/0.70    inference(nnf_transformation,[],[f21])).
% 1.20/0.70  fof(f144,plain,(
% 1.20/0.70    ( ! [X0] : (r2_hidden(k1_funct_1(sK6,X0),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) | ~r2_hidden(X0,sK3)) )),
% 1.20/0.70    inference(subsumption_resolution,[],[f143,f43])).
% 1.20/0.70  fof(f43,plain,(
% 1.20/0.70    v1_funct_1(sK6)),
% 1.20/0.70    inference(cnf_transformation,[],[f27])).
% 1.20/0.70  fof(f143,plain,(
% 1.20/0.70    ( ! [X0] : (~r2_hidden(X0,sK3) | r2_hidden(k1_funct_1(sK6,X0),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) | ~v1_funct_1(sK6)) )),
% 1.20/0.70    inference(subsumption_resolution,[],[f142,f83])).
% 1.20/0.70  fof(f83,plain,(
% 1.20/0.70    v1_funct_2(sK6,sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4))),
% 1.20/0.70    inference(definition_unfolding,[],[f44,f81])).
% 1.20/0.70  fof(f81,plain,(
% 1.20/0.70    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.20/0.70    inference(definition_unfolding,[],[f49,f80])).
% 1.20/0.70  fof(f49,plain,(
% 1.20/0.70    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.20/0.70    inference(cnf_transformation,[],[f2])).
% 1.20/0.70  fof(f2,axiom,(
% 1.20/0.70    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.20/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.20/0.70  fof(f44,plain,(
% 1.20/0.70    v1_funct_2(sK6,sK3,k1_tarski(sK4))),
% 1.20/0.70    inference(cnf_transformation,[],[f27])).
% 1.20/0.70  % (15226)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.20/0.70  fof(f142,plain,(
% 1.20/0.70    ( ! [X0] : (~r2_hidden(X0,sK3) | r2_hidden(k1_funct_1(sK6,X0),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) | ~v1_funct_2(sK6,sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) | ~v1_funct_1(sK6)) )),
% 1.20/0.70    inference(subsumption_resolution,[],[f141,f115])).
% 1.20/0.70  fof(f115,plain,(
% 1.20/0.70    ( ! [X0] : (k1_xboole_0 != k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.20/0.70    inference(subsumption_resolution,[],[f114,f102])).
% 1.20/0.70  fof(f102,plain,(
% 1.20/0.70    ( ! [X0,X1] : (r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.20/0.70    inference(resolution,[],[f90,f89])).
% 1.20/0.70  fof(f89,plain,(
% 1.20/0.70    ( ! [X4,X2,X0] : (~sP0(X0,X4,X2) | r2_hidden(X4,X2)) )),
% 1.20/0.70    inference(equality_resolution,[],[f58])).
% 1.20/0.70  fof(f58,plain,(
% 1.20/0.70    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | ~sP0(X0,X1,X2)) )),
% 1.20/0.70    inference(cnf_transformation,[],[f33])).
% 1.20/0.70  fof(f114,plain,(
% 1.20/0.70    ( ! [X0] : (~r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) | k1_xboole_0 != k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.20/0.70    inference(forward_demodulation,[],[f113,f51])).
% 1.20/0.70  fof(f51,plain,(
% 1.20/0.70    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.20/0.70    inference(cnf_transformation,[],[f9])).
% 1.20/0.70  fof(f9,axiom,(
% 1.20/0.70    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.20/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.20/0.70  fof(f113,plain,(
% 1.20/0.70    ( ! [X0] : (k1_xboole_0 != k3_enumset1(X0,X0,X0,X0,X0) | ~r2_hidden(X0,k2_relat_1(k6_relat_1(k3_enumset1(X0,X0,X0,X0,X0))))) )),
% 1.20/0.70    inference(subsumption_resolution,[],[f112,f48])).
% 1.20/0.70  fof(f48,plain,(
% 1.20/0.70    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.20/0.70    inference(cnf_transformation,[],[f7])).
% 1.20/0.70  fof(f7,axiom,(
% 1.20/0.70    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.20/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.20/0.70  % (15216)Refutation not found, incomplete strategy% (15216)------------------------------
% 1.20/0.70  % (15216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.70  % (15216)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.70  
% 1.20/0.70  % (15216)Memory used [KB]: 10746
% 1.20/0.70  % (15216)Time elapsed: 0.134 s
% 1.20/0.70  % (15216)------------------------------
% 1.20/0.70  % (15216)------------------------------
% 1.20/0.70  fof(f112,plain,(
% 1.20/0.70    ( ! [X0] : (k1_xboole_0 != k3_enumset1(X0,X0,X0,X0,X0) | ~r2_hidden(X0,k2_relat_1(k6_relat_1(k3_enumset1(X0,X0,X0,X0,X0)))) | ~v1_relat_1(k6_relat_1(k3_enumset1(X0,X0,X0,X0,X0)))) )),
% 1.20/0.70    inference(superposition,[],[f85,f101])).
% 1.20/0.70  fof(f101,plain,(
% 1.20/0.70    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),X0) = X0) )),
% 1.20/0.70    inference(forward_demodulation,[],[f100,f50])).
% 1.20/0.70  fof(f50,plain,(
% 1.20/0.70    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.20/0.70    inference(cnf_transformation,[],[f9])).
% 1.20/0.70  fof(f100,plain,(
% 1.20/0.70    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)) )),
% 1.20/0.70    inference(forward_demodulation,[],[f99,f51])).
% 1.20/0.70  fof(f99,plain,(
% 1.20/0.70    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0)))) )),
% 1.20/0.70    inference(resolution,[],[f52,f48])).
% 1.20/0.70  fof(f52,plain,(
% 1.20/0.70    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 1.20/0.70    inference(cnf_transformation,[],[f16])).
% 1.20/0.70  fof(f16,plain,(
% 1.20/0.70    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.20/0.70    inference(ennf_transformation,[],[f8])).
% 1.20/0.70  fof(f8,axiom,(
% 1.20/0.70    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.20/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 1.20/0.70  fof(f85,plain,(
% 1.20/0.70    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,k3_enumset1(X0,X0,X0,X0,X0)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.20/0.70    inference(definition_unfolding,[],[f54,f81])).
% 1.20/0.70  fof(f54,plain,(
% 1.20/0.70    ( ! [X0,X1] : (k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.20/0.70    inference(cnf_transformation,[],[f28])).
% 1.20/0.70  fof(f28,plain,(
% 1.20/0.70    ! [X0,X1] : (((r2_hidden(X0,k2_relat_1(X1)) | k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0) & (k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 | ~r2_hidden(X0,k2_relat_1(X1)))) | ~v1_relat_1(X1))),
% 1.20/0.70    inference(nnf_transformation,[],[f17])).
% 1.20/0.70  fof(f17,plain,(
% 1.20/0.70    ! [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0) | ~v1_relat_1(X1))),
% 1.20/0.70    inference(ennf_transformation,[],[f10])).
% 1.20/0.70  % (15213)Refutation not found, incomplete strategy% (15213)------------------------------
% 1.20/0.70  % (15213)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.70  fof(f10,axiom,(
% 1.20/0.70    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0))),
% 1.20/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).
% 1.20/0.70  % (15229)Refutation not found, incomplete strategy% (15229)------------------------------
% 1.20/0.70  % (15229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.70  fof(f141,plain,(
% 1.20/0.70    ( ! [X0] : (k1_xboole_0 = k3_enumset1(sK4,sK4,sK4,sK4,sK4) | ~r2_hidden(X0,sK3) | r2_hidden(k1_funct_1(sK6,X0),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) | ~v1_funct_2(sK6,sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) | ~v1_funct_1(sK6)) )),
% 1.20/0.70    inference(resolution,[],[f66,f82])).
% 1.20/0.70  % (15220)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.20/0.70  fof(f82,plain,(
% 1.20/0.70    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k3_enumset1(sK4,sK4,sK4,sK4,sK4))))),
% 1.20/0.70    inference(definition_unfolding,[],[f45,f81])).
% 1.20/0.70  fof(f45,plain,(
% 1.20/0.70    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))),
% 1.20/0.70    inference(cnf_transformation,[],[f27])).
% 1.20/0.70  fof(f66,plain,(
% 1.20/0.70    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | r2_hidden(k1_funct_1(X3,X2),X1) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.20/0.70    inference(cnf_transformation,[],[f19])).
% 1.20/0.70  fof(f19,plain,(
% 1.20/0.70    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.20/0.70    inference(flattening,[],[f18])).
% 1.20/0.70  fof(f18,plain,(
% 1.20/0.70    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.20/0.70    inference(ennf_transformation,[],[f11])).
% 1.20/0.70  % (15210)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.20/0.70  fof(f11,axiom,(
% 1.20/0.70    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 1.20/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).
% 1.20/0.70  % SZS output end Proof for theBenchmark
% 1.20/0.70  % (15205)------------------------------
% 1.20/0.70  % (15205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.70  % (15205)Termination reason: Refutation
% 1.20/0.70  
% 1.20/0.70  % (15205)Memory used [KB]: 10746
% 1.20/0.70  % (15205)Time elapsed: 0.127 s
% 1.20/0.70  % (15205)------------------------------
% 1.20/0.70  % (15205)------------------------------
% 1.20/0.71  % (15064)Success in time 0.344 s
%------------------------------------------------------------------------------
