%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:05 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 330 expanded)
%              Number of leaves         :   28 ( 103 expanded)
%              Depth                    :   17
%              Number of atoms          :  323 ( 819 expanded)
%              Number of equality atoms :   98 ( 306 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f215,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f129,f132,f148,f174,f212])).

fof(f212,plain,
    ( ~ spl8_1
    | ~ spl8_3 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f210,f53])).

fof(f53,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f210,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f198,f54])).

fof(f54,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f198,plain,
    ( ~ v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(backward_demodulation,[],[f158,f184])).

fof(f184,plain,
    ( k1_xboole_0 = sK6
    | ~ spl8_3 ),
    inference(resolution,[],[f143,f59])).

fof(f59,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( sP0(sK7(X0),X0)
        & r2_hidden(sK7(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f32,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP0(X1,X0)
          & r2_hidden(X1,X0) )
     => ( sP0(sK7(X0),X0)
        & r2_hidden(sK7(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP0(X1,X0)
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(definition_folding,[],[f22,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ! [X2,X3,X4] :
          ( k3_mcart_1(X2,X3,X4) != X1
          | ( ~ r2_hidden(X3,X0)
            & ~ r2_hidden(X2,X0) ) )
      | ~ sP0(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f143,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK6)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl8_3
  <=> ! [X0] : ~ r2_hidden(X0,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f158,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK6))
    | ~ spl8_1 ),
    inference(superposition,[],[f91,f124])).

fof(f124,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_relat_1(sK6)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl8_1
  <=> k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_relat_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f91,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f61,f87])).

fof(f87,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f62,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f64,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f76,f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f80,f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f81,f82])).

fof(f82,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f64,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f62,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f61,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_xboole_0)).

fof(f174,plain,
    ( ~ spl8_1
    | ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f172,f156])).

fof(f156,plain,
    ( r2_hidden(sK4,k1_relat_1(sK6))
    | ~ spl8_1
    | ~ spl8_4 ),
    inference(backward_demodulation,[],[f147,f124])).

fof(f147,plain,
    ( r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl8_4
  <=> r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f172,plain,
    ( ~ r2_hidden(sK4,k1_relat_1(sK6))
    | ~ spl8_1 ),
    inference(resolution,[],[f171,f52])).

fof(f52,plain,(
    ~ r2_hidden(k1_funct_1(sK6,sK4),sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ~ r2_hidden(k1_funct_1(sK6,sK4),sK5)
    & k1_xboole_0 != sK5
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK4),sK5)))
    & v1_funct_2(sK6,k1_tarski(sK4),sK5)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f21,f37])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK6,sK4),sK5)
      & k1_xboole_0 != sK5
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK4),sK5)))
      & v1_funct_2(sK6,k1_tarski(sK4),sK5)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

fof(f171,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK6,X0),sK5)
        | ~ r2_hidden(X0,k1_relat_1(sK6)) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f170,f48])).

fof(f48,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f170,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK6))
        | r2_hidden(k1_funct_1(sK6,X0),sK5)
        | ~ v1_funct_1(sK6) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f169,f150])).

fof(f150,plain,
    ( v1_funct_2(sK6,k1_relat_1(sK6),sK5)
    | ~ spl8_1 ),
    inference(backward_demodulation,[],[f90,f124])).

fof(f90,plain,(
    v1_funct_2(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) ),
    inference(definition_unfolding,[],[f49,f88])).

fof(f88,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f56,f87])).

fof(f56,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f49,plain,(
    v1_funct_2(sK6,k1_tarski(sK4),sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f169,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK6))
        | r2_hidden(k1_funct_1(sK6,X0),sK5)
        | ~ v1_funct_2(sK6,k1_relat_1(sK6),sK5)
        | ~ v1_funct_1(sK6) )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f168,f51])).

fof(f51,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f38])).

fof(f168,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK5
        | ~ r2_hidden(X0,k1_relat_1(sK6))
        | r2_hidden(k1_funct_1(sK6,X0),sK5)
        | ~ v1_funct_2(sK6,k1_relat_1(sK6),sK5)
        | ~ v1_funct_1(sK6) )
    | ~ spl8_1 ),
    inference(resolution,[],[f79,f149])).

fof(f149,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5)))
    | ~ spl8_1 ),
    inference(backward_demodulation,[],[f89,f124])).

fof(f89,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5))) ),
    inference(definition_unfolding,[],[f50,f88])).

fof(f50,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK4),sK5))) ),
    inference(cnf_transformation,[],[f38])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | r2_hidden(k1_funct_1(X3,X2),X1)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(f148,plain,
    ( spl8_3
    | spl8_4 ),
    inference(avatar_split_clause,[],[f140,f145,f142])).

% (19422)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (19420)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (19400)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% (19426)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (19427)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% (19421)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (19421)Refutation not found, incomplete strategy% (19421)------------------------------
% (19421)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19421)Termination reason: Refutation not found, incomplete strategy

% (19421)Memory used [KB]: 10746
% (19421)Time elapsed: 0.149 s
% (19421)------------------------------
% (19421)------------------------------
% (19425)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% (19411)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (19412)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (19416)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (19405)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% (19418)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (19416)Refutation not found, incomplete strategy% (19416)------------------------------
% (19416)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19416)Termination reason: Refutation not found, incomplete strategy

% (19416)Memory used [KB]: 10618
% (19416)Time elapsed: 0.151 s
% (19416)------------------------------
% (19416)------------------------------
% (19415)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f140,plain,(
    ! [X0] :
      ( r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
      | ~ r2_hidden(X0,sK6) ) ),
    inference(duplicate_literal_removal,[],[f138])).

fof(f138,plain,(
    ! [X0] :
      ( r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
      | ~ r2_hidden(X0,sK6)
      | ~ r2_hidden(X0,sK6) ) ),
    inference(superposition,[],[f104,f137])).

fof(f137,plain,(
    ! [X0] :
      ( k1_mcart_1(X0) = sK4
      | ~ r2_hidden(X0,sK6) ) ),
    inference(duplicate_literal_removal,[],[f133])).

fof(f133,plain,(
    ! [X0] :
      ( k1_mcart_1(X0) = sK4
      | k1_mcart_1(X0) = sK4
      | ~ r2_hidden(X0,sK6) ) ),
    inference(resolution,[],[f93,f102])).

fof(f102,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5))
      | ~ r2_hidden(X0,sK6) ) ),
    inference(resolution,[],[f63,f89])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),X3))
      | k1_mcart_1(X0) = X1
      | k1_mcart_1(X0) = X2 ) ),
    inference(definition_unfolding,[],[f77,f87])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(X0) = X2
      | k1_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k2_mcart_1(X0),X3)
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) )
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))
     => ( r2_hidden(k2_mcart_1(X0),X3)
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).

% (19399)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f104,plain,(
    ! [X1] :
      ( r2_hidden(k1_mcart_1(X1),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
      | ~ r2_hidden(X1,sK6) ) ),
    inference(resolution,[],[f102,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f132,plain,(
    ~ spl8_2 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f130,f51])).

fof(f130,plain,
    ( k1_xboole_0 = sK5
    | ~ spl8_2 ),
    inference(resolution,[],[f128,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f128,plain,
    ( sP1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl8_2
  <=> sP1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f129,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f120,f126,f122])).

fof(f120,plain,
    ( sP1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5)
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_relat_1(sK6) ),
    inference(subsumption_resolution,[],[f119,f90])).

fof(f119,plain,
    ( ~ v1_funct_2(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5)
    | sP1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5)
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_relat_1(sK6) ),
    inference(resolution,[],[f113,f89])).

fof(f113,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | sP1(X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(subsumption_resolution,[],[f111,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X2,X1,X0)
        & sP2(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f27,f35,f34,f33])).

fof(f34,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP3(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f111,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | sP1(X3,X4)
      | ~ sP2(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f70,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:43:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (19409)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.43  % (19409)Refutation not found, incomplete strategy% (19409)------------------------------
% 0.20/0.43  % (19409)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (19409)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.43  
% 0.20/0.43  % (19409)Memory used [KB]: 10618
% 0.20/0.43  % (19409)Time elapsed: 0.005 s
% 0.20/0.43  % (19409)------------------------------
% 0.20/0.43  % (19409)------------------------------
% 0.20/0.49  % (19438)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 0.20/0.52  % (19404)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (19408)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (19410)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (19413)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.29/0.52  % (19403)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.29/0.54  % (19402)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.29/0.54  % (19428)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.29/0.54  % (19429)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.29/0.54  % (19401)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.29/0.54  % (19430)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.29/0.54  % (19428)Refutation not found, incomplete strategy% (19428)------------------------------
% 1.29/0.54  % (19428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (19428)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (19428)Memory used [KB]: 10746
% 1.29/0.54  % (19428)Time elapsed: 0.140 s
% 1.29/0.54  % (19428)------------------------------
% 1.29/0.54  % (19428)------------------------------
% 1.29/0.54  % (19429)Refutation found. Thanks to Tanya!
% 1.29/0.54  % SZS status Theorem for theBenchmark
% 1.29/0.54  % SZS output start Proof for theBenchmark
% 1.29/0.54  fof(f215,plain,(
% 1.29/0.54    $false),
% 1.29/0.54    inference(avatar_sat_refutation,[],[f129,f132,f148,f174,f212])).
% 1.29/0.54  fof(f212,plain,(
% 1.29/0.54    ~spl8_1 | ~spl8_3),
% 1.29/0.54    inference(avatar_contradiction_clause,[],[f211])).
% 1.29/0.54  fof(f211,plain,(
% 1.29/0.54    $false | (~spl8_1 | ~spl8_3)),
% 1.29/0.54    inference(subsumption_resolution,[],[f210,f53])).
% 1.29/0.54  fof(f53,plain,(
% 1.29/0.54    v1_xboole_0(k1_xboole_0)),
% 1.29/0.54    inference(cnf_transformation,[],[f1])).
% 1.29/0.54  fof(f1,axiom,(
% 1.29/0.54    v1_xboole_0(k1_xboole_0)),
% 1.29/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.29/0.54  fof(f210,plain,(
% 1.29/0.54    ~v1_xboole_0(k1_xboole_0) | (~spl8_1 | ~spl8_3)),
% 1.29/0.54    inference(forward_demodulation,[],[f198,f54])).
% 1.29/0.54  fof(f54,plain,(
% 1.29/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.29/0.54    inference(cnf_transformation,[],[f11])).
% 1.29/0.54  fof(f11,axiom,(
% 1.29/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.29/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.29/0.54  fof(f198,plain,(
% 1.29/0.54    ~v1_xboole_0(k1_relat_1(k1_xboole_0)) | (~spl8_1 | ~spl8_3)),
% 1.29/0.54    inference(backward_demodulation,[],[f158,f184])).
% 1.29/0.54  fof(f184,plain,(
% 1.29/0.54    k1_xboole_0 = sK6 | ~spl8_3),
% 1.29/0.54    inference(resolution,[],[f143,f59])).
% 1.29/0.54  fof(f59,plain,(
% 1.29/0.54    ( ! [X0] : (r2_hidden(sK7(X0),X0) | k1_xboole_0 = X0) )),
% 1.29/0.54    inference(cnf_transformation,[],[f42])).
% 1.29/0.54  fof(f42,plain,(
% 1.29/0.54    ! [X0] : ((sP0(sK7(X0),X0) & r2_hidden(sK7(X0),X0)) | k1_xboole_0 = X0)),
% 1.29/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f32,f41])).
% 1.29/0.54  fof(f41,plain,(
% 1.29/0.54    ! [X0] : (? [X1] : (sP0(X1,X0) & r2_hidden(X1,X0)) => (sP0(sK7(X0),X0) & r2_hidden(sK7(X0),X0)))),
% 1.29/0.54    introduced(choice_axiom,[])).
% 1.29/0.54  fof(f32,plain,(
% 1.29/0.54    ! [X0] : (? [X1] : (sP0(X1,X0) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.29/0.54    inference(definition_folding,[],[f22,f31])).
% 1.29/0.54  fof(f31,plain,(
% 1.29/0.54    ! [X1,X0] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) | ~sP0(X1,X0))),
% 1.29/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.29/0.54  fof(f22,plain,(
% 1.29/0.54    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.29/0.54    inference(ennf_transformation,[],[f15])).
% 1.29/0.54  fof(f15,axiom,(
% 1.29/0.54    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.29/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).
% 1.29/0.54  fof(f143,plain,(
% 1.29/0.54    ( ! [X0] : (~r2_hidden(X0,sK6)) ) | ~spl8_3),
% 1.29/0.54    inference(avatar_component_clause,[],[f142])).
% 1.29/0.54  fof(f142,plain,(
% 1.29/0.54    spl8_3 <=> ! [X0] : ~r2_hidden(X0,sK6)),
% 1.29/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.29/0.54  fof(f158,plain,(
% 1.29/0.54    ~v1_xboole_0(k1_relat_1(sK6)) | ~spl8_1),
% 1.29/0.54    inference(superposition,[],[f91,f124])).
% 1.29/0.54  fof(f124,plain,(
% 1.29/0.54    k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_relat_1(sK6) | ~spl8_1),
% 1.29/0.54    inference(avatar_component_clause,[],[f122])).
% 1.29/0.54  fof(f122,plain,(
% 1.29/0.54    spl8_1 <=> k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_relat_1(sK6)),
% 1.29/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.29/0.54  fof(f91,plain,(
% 1.29/0.54    ( ! [X0,X1] : (~v1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.29/0.54    inference(definition_unfolding,[],[f61,f87])).
% 1.29/0.54  fof(f87,plain,(
% 1.29/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.29/0.54    inference(definition_unfolding,[],[f62,f86])).
% 1.29/0.54  fof(f86,plain,(
% 1.29/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.29/0.54    inference(definition_unfolding,[],[f64,f85])).
% 1.29/0.54  fof(f85,plain,(
% 1.29/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.29/0.54    inference(definition_unfolding,[],[f76,f84])).
% 1.29/0.54  fof(f84,plain,(
% 1.29/0.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.29/0.54    inference(definition_unfolding,[],[f80,f83])).
% 1.29/0.54  fof(f83,plain,(
% 1.29/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.29/0.54    inference(definition_unfolding,[],[f81,f82])).
% 1.29/0.54  fof(f82,plain,(
% 1.29/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f8])).
% 1.29/0.54  fof(f8,axiom,(
% 1.29/0.54    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.29/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.29/0.54  fof(f81,plain,(
% 1.29/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f7])).
% 1.29/0.54  fof(f7,axiom,(
% 1.29/0.54    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.29/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.29/0.54  fof(f80,plain,(
% 1.29/0.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f6])).
% 1.29/0.54  fof(f6,axiom,(
% 1.29/0.54    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.29/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.29/0.54  fof(f76,plain,(
% 1.29/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f5])).
% 1.29/0.54  fof(f5,axiom,(
% 1.29/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.29/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.29/0.54  fof(f64,plain,(
% 1.29/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f4])).
% 1.29/0.54  fof(f4,axiom,(
% 1.29/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.29/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.29/0.54  fof(f62,plain,(
% 1.29/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f3])).
% 1.29/0.54  fof(f3,axiom,(
% 1.29/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.29/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.29/0.54  fof(f61,plain,(
% 1.29/0.54    ( ! [X0,X1] : (~v1_xboole_0(k2_tarski(X0,X1))) )),
% 1.29/0.54    inference(cnf_transformation,[],[f9])).
% 1.29/0.54  fof(f9,axiom,(
% 1.29/0.54    ! [X0,X1] : ~v1_xboole_0(k2_tarski(X0,X1))),
% 1.29/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_xboole_0)).
% 1.29/0.54  fof(f174,plain,(
% 1.29/0.54    ~spl8_1 | ~spl8_4),
% 1.29/0.54    inference(avatar_contradiction_clause,[],[f173])).
% 1.29/0.54  fof(f173,plain,(
% 1.29/0.54    $false | (~spl8_1 | ~spl8_4)),
% 1.29/0.54    inference(subsumption_resolution,[],[f172,f156])).
% 1.29/0.54  fof(f156,plain,(
% 1.29/0.54    r2_hidden(sK4,k1_relat_1(sK6)) | (~spl8_1 | ~spl8_4)),
% 1.29/0.54    inference(backward_demodulation,[],[f147,f124])).
% 1.29/0.54  fof(f147,plain,(
% 1.29/0.54    r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) | ~spl8_4),
% 1.29/0.54    inference(avatar_component_clause,[],[f145])).
% 1.29/0.54  fof(f145,plain,(
% 1.29/0.54    spl8_4 <=> r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),
% 1.29/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.29/0.54  fof(f172,plain,(
% 1.29/0.54    ~r2_hidden(sK4,k1_relat_1(sK6)) | ~spl8_1),
% 1.29/0.54    inference(resolution,[],[f171,f52])).
% 1.29/0.54  fof(f52,plain,(
% 1.29/0.54    ~r2_hidden(k1_funct_1(sK6,sK4),sK5)),
% 1.29/0.54    inference(cnf_transformation,[],[f38])).
% 1.29/0.54  fof(f38,plain,(
% 1.29/0.54    ~r2_hidden(k1_funct_1(sK6,sK4),sK5) & k1_xboole_0 != sK5 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK4),sK5))) & v1_funct_2(sK6,k1_tarski(sK4),sK5) & v1_funct_1(sK6)),
% 1.29/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f21,f37])).
% 1.29/0.54  fof(f37,plain,(
% 1.29/0.54    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK6,sK4),sK5) & k1_xboole_0 != sK5 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK4),sK5))) & v1_funct_2(sK6,k1_tarski(sK4),sK5) & v1_funct_1(sK6))),
% 1.29/0.54    introduced(choice_axiom,[])).
% 1.29/0.54  fof(f21,plain,(
% 1.29/0.54    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 1.29/0.54    inference(flattening,[],[f20])).
% 1.29/0.54  fof(f20,plain,(
% 1.29/0.54    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 1.29/0.54    inference(ennf_transformation,[],[f19])).
% 1.29/0.54  fof(f19,negated_conjecture,(
% 1.29/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 1.29/0.54    inference(negated_conjecture,[],[f18])).
% 1.29/0.54  fof(f18,conjecture,(
% 1.29/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 1.29/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).
% 1.29/0.54  fof(f171,plain,(
% 1.29/0.54    ( ! [X0] : (r2_hidden(k1_funct_1(sK6,X0),sK5) | ~r2_hidden(X0,k1_relat_1(sK6))) ) | ~spl8_1),
% 1.29/0.54    inference(subsumption_resolution,[],[f170,f48])).
% 1.29/0.54  fof(f48,plain,(
% 1.29/0.54    v1_funct_1(sK6)),
% 1.29/0.54    inference(cnf_transformation,[],[f38])).
% 1.29/0.54  fof(f170,plain,(
% 1.29/0.54    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK6)) | r2_hidden(k1_funct_1(sK6,X0),sK5) | ~v1_funct_1(sK6)) ) | ~spl8_1),
% 1.29/0.54    inference(subsumption_resolution,[],[f169,f150])).
% 1.29/0.54  fof(f150,plain,(
% 1.29/0.54    v1_funct_2(sK6,k1_relat_1(sK6),sK5) | ~spl8_1),
% 1.29/0.54    inference(backward_demodulation,[],[f90,f124])).
% 1.29/0.54  fof(f90,plain,(
% 1.29/0.54    v1_funct_2(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5)),
% 1.29/0.54    inference(definition_unfolding,[],[f49,f88])).
% 1.29/0.54  fof(f88,plain,(
% 1.29/0.54    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.29/0.54    inference(definition_unfolding,[],[f56,f87])).
% 1.29/0.54  fof(f56,plain,(
% 1.29/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f2])).
% 1.29/0.54  fof(f2,axiom,(
% 1.29/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.29/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.29/0.54  fof(f49,plain,(
% 1.29/0.54    v1_funct_2(sK6,k1_tarski(sK4),sK5)),
% 1.29/0.54    inference(cnf_transformation,[],[f38])).
% 1.29/0.54  fof(f169,plain,(
% 1.29/0.54    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK6)) | r2_hidden(k1_funct_1(sK6,X0),sK5) | ~v1_funct_2(sK6,k1_relat_1(sK6),sK5) | ~v1_funct_1(sK6)) ) | ~spl8_1),
% 1.29/0.54    inference(subsumption_resolution,[],[f168,f51])).
% 1.29/0.54  fof(f51,plain,(
% 1.29/0.54    k1_xboole_0 != sK5),
% 1.29/0.54    inference(cnf_transformation,[],[f38])).
% 1.29/0.54  fof(f168,plain,(
% 1.29/0.54    ( ! [X0] : (k1_xboole_0 = sK5 | ~r2_hidden(X0,k1_relat_1(sK6)) | r2_hidden(k1_funct_1(sK6,X0),sK5) | ~v1_funct_2(sK6,k1_relat_1(sK6),sK5) | ~v1_funct_1(sK6)) ) | ~spl8_1),
% 1.29/0.54    inference(resolution,[],[f79,f149])).
% 1.29/0.54  fof(f149,plain,(
% 1.29/0.54    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK5))) | ~spl8_1),
% 1.29/0.54    inference(backward_demodulation,[],[f89,f124])).
% 1.29/0.54  fof(f89,plain,(
% 1.29/0.54    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5)))),
% 1.29/0.54    inference(definition_unfolding,[],[f50,f88])).
% 1.29/0.54  fof(f50,plain,(
% 1.29/0.54    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK4),sK5)))),
% 1.29/0.54    inference(cnf_transformation,[],[f38])).
% 1.29/0.54  fof(f79,plain,(
% 1.29/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | r2_hidden(k1_funct_1(X3,X2),X1) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.29/0.54    inference(cnf_transformation,[],[f30])).
% 1.29/0.54  fof(f30,plain,(
% 1.29/0.54    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.29/0.54    inference(flattening,[],[f29])).
% 1.29/0.54  fof(f29,plain,(
% 1.29/0.54    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.29/0.54    inference(ennf_transformation,[],[f17])).
% 1.29/0.54  fof(f17,axiom,(
% 1.29/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 1.29/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
% 1.29/0.54  fof(f148,plain,(
% 1.29/0.54    spl8_3 | spl8_4),
% 1.29/0.54    inference(avatar_split_clause,[],[f140,f145,f142])).
% 1.29/0.54  % (19422)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.40/0.54  % (19420)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.40/0.54  % (19400)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.40/0.55  % (19426)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.40/0.55  % (19427)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.40/0.55  % (19421)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.40/0.55  % (19421)Refutation not found, incomplete strategy% (19421)------------------------------
% 1.40/0.55  % (19421)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (19421)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (19421)Memory used [KB]: 10746
% 1.40/0.55  % (19421)Time elapsed: 0.149 s
% 1.40/0.55  % (19421)------------------------------
% 1.40/0.55  % (19421)------------------------------
% 1.40/0.55  % (19425)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.40/0.55  % (19411)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.40/0.55  % (19412)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.40/0.56  % (19416)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.40/0.56  % (19405)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.40/0.56  % (19418)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.40/0.56  % (19416)Refutation not found, incomplete strategy% (19416)------------------------------
% 1.40/0.56  % (19416)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (19416)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.56  
% 1.40/0.56  % (19416)Memory used [KB]: 10618
% 1.40/0.56  % (19416)Time elapsed: 0.151 s
% 1.40/0.56  % (19416)------------------------------
% 1.40/0.56  % (19416)------------------------------
% 1.40/0.56  % (19415)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.40/0.56  fof(f140,plain,(
% 1.40/0.56    ( ! [X0] : (r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) | ~r2_hidden(X0,sK6)) )),
% 1.40/0.56    inference(duplicate_literal_removal,[],[f138])).
% 1.40/0.56  fof(f138,plain,(
% 1.40/0.56    ( ! [X0] : (r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) | ~r2_hidden(X0,sK6) | ~r2_hidden(X0,sK6)) )),
% 1.40/0.56    inference(superposition,[],[f104,f137])).
% 1.40/0.56  fof(f137,plain,(
% 1.40/0.56    ( ! [X0] : (k1_mcart_1(X0) = sK4 | ~r2_hidden(X0,sK6)) )),
% 1.40/0.56    inference(duplicate_literal_removal,[],[f133])).
% 1.40/0.56  fof(f133,plain,(
% 1.40/0.56    ( ! [X0] : (k1_mcart_1(X0) = sK4 | k1_mcart_1(X0) = sK4 | ~r2_hidden(X0,sK6)) )),
% 1.40/0.56    inference(resolution,[],[f93,f102])).
% 1.40/0.56  fof(f102,plain,(
% 1.40/0.56    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5)) | ~r2_hidden(X0,sK6)) )),
% 1.40/0.56    inference(resolution,[],[f63,f89])).
% 1.40/0.56  fof(f63,plain,(
% 1.40/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f23])).
% 1.40/0.56  fof(f23,plain,(
% 1.40/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.40/0.56    inference(ennf_transformation,[],[f10])).
% 1.40/0.56  fof(f10,axiom,(
% 1.40/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.40/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.40/0.56  fof(f93,plain,(
% 1.40/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),X3)) | k1_mcart_1(X0) = X1 | k1_mcart_1(X0) = X2) )),
% 1.40/0.56    inference(definition_unfolding,[],[f77,f87])).
% 1.40/0.56  fof(f77,plain,(
% 1.40/0.56    ( ! [X2,X0,X3,X1] : (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1 | ~r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))) )),
% 1.40/0.56    inference(cnf_transformation,[],[f28])).
% 1.40/0.56  fof(f28,plain,(
% 1.40/0.56    ! [X0,X1,X2,X3] : ((r2_hidden(k2_mcart_1(X0),X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)) | ~r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)))),
% 1.40/0.56    inference(ennf_transformation,[],[f14])).
% 1.40/0.56  fof(f14,axiom,(
% 1.40/0.56    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) => (r2_hidden(k2_mcart_1(X0),X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 1.40/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).
% 1.40/0.56  % (19399)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.40/0.56  fof(f104,plain,(
% 1.40/0.56    ( ! [X1] : (r2_hidden(k1_mcart_1(X1),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) | ~r2_hidden(X1,sK6)) )),
% 1.40/0.56    inference(resolution,[],[f102,f65])).
% 1.40/0.56  fof(f65,plain,(
% 1.40/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f24])).
% 1.40/0.56  fof(f24,plain,(
% 1.40/0.56    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.40/0.56    inference(ennf_transformation,[],[f13])).
% 1.40/0.56  fof(f13,axiom,(
% 1.40/0.56    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.40/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.40/0.56  fof(f132,plain,(
% 1.40/0.56    ~spl8_2),
% 1.40/0.56    inference(avatar_contradiction_clause,[],[f131])).
% 1.40/0.56  fof(f131,plain,(
% 1.40/0.56    $false | ~spl8_2),
% 1.40/0.56    inference(subsumption_resolution,[],[f130,f51])).
% 1.40/0.56  fof(f130,plain,(
% 1.40/0.56    k1_xboole_0 = sK5 | ~spl8_2),
% 1.40/0.56    inference(resolution,[],[f128,f72])).
% 1.40/0.56  fof(f72,plain,(
% 1.40/0.56    ( ! [X0,X1] : (~sP1(X0,X1) | k1_xboole_0 = X1) )),
% 1.40/0.56    inference(cnf_transformation,[],[f47])).
% 1.40/0.56  fof(f47,plain,(
% 1.40/0.56    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 1.40/0.56    inference(nnf_transformation,[],[f33])).
% 1.40/0.56  fof(f33,plain,(
% 1.40/0.56    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 1.40/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.40/0.56  fof(f128,plain,(
% 1.40/0.56    sP1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) | ~spl8_2),
% 1.40/0.56    inference(avatar_component_clause,[],[f126])).
% 1.40/0.56  fof(f126,plain,(
% 1.40/0.56    spl8_2 <=> sP1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5)),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.40/0.56  fof(f129,plain,(
% 1.40/0.56    spl8_1 | spl8_2),
% 1.40/0.56    inference(avatar_split_clause,[],[f120,f126,f122])).
% 1.40/0.56  fof(f120,plain,(
% 1.40/0.56    sP1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_relat_1(sK6)),
% 1.40/0.56    inference(subsumption_resolution,[],[f119,f90])).
% 1.40/0.56  fof(f119,plain,(
% 1.40/0.56    ~v1_funct_2(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) | sP1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_relat_1(sK6)),
% 1.40/0.56    inference(resolution,[],[f113,f89])).
% 1.40/0.56  fof(f113,plain,(
% 1.40/0.56    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | sP1(X3,X4) | k1_relat_1(X5) = X3) )),
% 1.40/0.56    inference(subsumption_resolution,[],[f111,f74])).
% 1.40/0.56  fof(f74,plain,(
% 1.40/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X0,X2,X1)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f36])).
% 1.40/0.56  fof(f36,plain,(
% 1.40/0.56    ! [X0,X1,X2] : ((sP3(X2,X1,X0) & sP2(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.56    inference(definition_folding,[],[f27,f35,f34,f33])).
% 1.40/0.56  fof(f34,plain,(
% 1.40/0.56    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 1.40/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.40/0.56  fof(f35,plain,(
% 1.40/0.56    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP3(X2,X1,X0))),
% 1.40/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.40/0.56  fof(f27,plain,(
% 1.40/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.56    inference(flattening,[],[f26])).
% 1.40/0.56  fof(f26,plain,(
% 1.40/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.56    inference(ennf_transformation,[],[f16])).
% 1.40/0.56  fof(f16,axiom,(
% 1.40/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.40/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.40/0.56  fof(f111,plain,(
% 1.40/0.56    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | sP1(X3,X4) | ~sP2(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 1.40/0.56    inference(superposition,[],[f70,f67])).
% 1.40/0.56  fof(f67,plain,(
% 1.40/0.56    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.40/0.56    inference(cnf_transformation,[],[f25])).
% 1.40/0.56  fof(f25,plain,(
% 1.40/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.56    inference(ennf_transformation,[],[f12])).
% 1.40/0.56  fof(f12,axiom,(
% 1.40/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.40/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.40/0.56  fof(f70,plain,(
% 1.40/0.56    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP1(X0,X2) | ~sP2(X0,X1,X2)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f46])).
% 1.40/0.56  fof(f46,plain,(
% 1.40/0.56    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP1(X0,X2) | ~sP2(X0,X1,X2))),
% 1.40/0.56    inference(rectify,[],[f45])).
% 1.40/0.56  fof(f45,plain,(
% 1.40/0.56    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 1.40/0.56    inference(nnf_transformation,[],[f34])).
% 1.40/0.56  % SZS output end Proof for theBenchmark
% 1.40/0.56  % (19429)------------------------------
% 1.40/0.56  % (19429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (19429)Termination reason: Refutation
% 1.40/0.56  
% 1.40/0.56  % (19429)Memory used [KB]: 6268
% 1.40/0.56  % (19429)Time elapsed: 0.140 s
% 1.40/0.56  % (19429)------------------------------
% 1.40/0.56  % (19429)------------------------------
% 1.40/0.56  % (19407)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.40/0.57  % (19397)Success in time 0.204 s
%------------------------------------------------------------------------------
