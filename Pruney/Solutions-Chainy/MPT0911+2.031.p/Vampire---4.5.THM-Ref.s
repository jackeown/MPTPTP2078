%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:33 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 327 expanded)
%              Number of leaves         :   16 (  87 expanded)
%              Depth                    :   20
%              Number of atoms          :  337 (2157 expanded)
%              Number of equality atoms :  180 (1288 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f239,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f123,f238])).

fof(f238,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f237])).

fof(f237,plain,
    ( $false
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f236,f168])).

fof(f168,plain,(
    m1_subset_1(k2_mcart_1(sK4),sK2) ),
    inference(subsumption_resolution,[],[f167,f56])).

fof(f56,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f31,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f31,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK3 = X7
                | k3_mcart_1(X5,X6,X7) != sK4
                | ~ m1_subset_1(X7,sK2) )
            | ~ m1_subset_1(X6,sK1) )
        | ~ m1_subset_1(X5,sK0) )
    & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k7_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X7
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK3 = X7
                  | k3_mcart_1(X5,X6,X7) != sK4
                  | ~ m1_subset_1(X7,sK2) )
              | ~ m1_subset_1(X6,sK1) )
          | ~ m1_subset_1(X5,sK0) )
      & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

% (13689)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (13676)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% (13699)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% (13692)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% (13696)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (13692)Refutation not found, incomplete strategy% (13692)------------------------------
% (13692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (13692)Termination reason: Refutation not found, incomplete strategy

% (13692)Memory used [KB]: 10746
% (13692)Time elapsed: 0.149 s
% (13692)------------------------------
% (13692)------------------------------
% (13691)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (13691)Refutation not found, incomplete strategy% (13691)------------------------------
% (13691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (13691)Termination reason: Refutation not found, incomplete strategy

% (13691)Memory used [KB]: 1791
% (13691)Time elapsed: 0.150 s
% (13691)------------------------------
% (13691)------------------------------
% (13688)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f16,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X7 ) ) ) )
         => ( k7_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X7 ) ) ) )
       => ( k7_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_mcart_1)).

fof(f167,plain,
    ( m1_subset_1(k2_mcart_1(sK4),sK2)
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(superposition,[],[f66,f82])).

fof(f82,plain,(
    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
    inference(subsumption_resolution,[],[f81,f33])).

fof(f33,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f28])).

fof(f81,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f80,f34])).

fof(f34,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f28])).

fof(f80,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f72,f35])).

fof(f35,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f28])).

fof(f72,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f56,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f51,f42])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f54,f42])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_mcart_1)).

fof(f236,plain,
    ( ~ m1_subset_1(k2_mcart_1(sK4),sK2)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f235,f166])).

fof(f166,plain,(
    sK3 != k2_mcart_1(sK4) ),
    inference(superposition,[],[f36,f82])).

fof(f36,plain,(
    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f235,plain,
    ( sK3 = k2_mcart_1(sK4)
    | ~ m1_subset_1(k2_mcart_1(sK4),sK2)
    | ~ spl5_1 ),
    inference(trivial_inequality_removal,[],[f234])).

fof(f234,plain,
    ( sK4 != sK4
    | sK3 = k2_mcart_1(sK4)
    | ~ m1_subset_1(k2_mcart_1(sK4),sK2)
    | ~ spl5_1 ),
    inference(superposition,[],[f233,f155])).

fof(f155,plain,
    ( sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f154,f38])).

fof(f38,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f154,plain,
    ( sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4))
    | ~ v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl5_1 ),
    inference(resolution,[],[f86,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f86,plain,
    ( r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl5_1
  <=> r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f233,plain,
    ( ! [X0] :
        ( sK4 != k4_tarski(k1_mcart_1(sK4),X0)
        | sK3 = X0
        | ~ m1_subset_1(X0,sK2) )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f232,f170])).

fof(f170,plain,(
    m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) ),
    inference(subsumption_resolution,[],[f169,f56])).

fof(f169,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(superposition,[],[f64,f76])).

fof(f76,plain,(
    k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f75,f33])).

fof(f75,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f74,f34])).

fof(f74,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f70,f35])).

fof(f70,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f56,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f49,f42])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f52,f42])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_mcart_1)).

fof(f232,plain,
    ( ! [X0] :
        ( sK4 != k4_tarski(k1_mcart_1(sK4),X0)
        | sK3 = X0
        | ~ m1_subset_1(X0,sK2)
        | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f231,f183])).

fof(f183,plain,(
    m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) ),
    inference(subsumption_resolution,[],[f182,f56])).

fof(f182,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(superposition,[],[f65,f79])).

fof(f79,plain,(
    k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f78,f33])).

fof(f78,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f77,f34])).

fof(f77,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f71,f35])).

fof(f71,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f56,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f50,f42])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f53,f42])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_mcart_1)).

fof(f231,plain,
    ( ! [X0] :
        ( sK4 != k4_tarski(k1_mcart_1(sK4),X0)
        | sK3 = X0
        | ~ m1_subset_1(X0,sK2)
        | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)
        | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) )
    | ~ spl5_1 ),
    inference(superposition,[],[f55,f197])).

fof(f197,plain,
    ( k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f196,f38])).

fof(f196,plain,
    ( k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl5_1 ),
    inference(resolution,[],[f152,f39])).

fof(f152,plain,
    ( r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))
    | ~ spl5_1 ),
    inference(resolution,[],[f86,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f55,plain,(
    ! [X6,X7,X5] :
      ( sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK3 = X7
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(definition_unfolding,[],[f32,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f32,plain,(
    ! [X6,X7,X5] :
      ( sK3 = X7
      | k3_mcart_1(X5,X6,X7) != sK4
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f123,plain,(
    ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f121,f33])).

fof(f121,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f120,f34])).

fof(f120,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f110,f35])).

fof(f110,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl5_2 ),
    inference(trivial_inequality_removal,[],[f101])).

fof(f101,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl5_2 ),
    inference(superposition,[],[f60,f92])).

fof(f92,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl5_2 ),
    inference(resolution,[],[f90,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f90,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl5_2
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f45,f42])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

fof(f91,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f73,f88,f84])).

fof(f73,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f56,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:53:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.51  % (13671)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (13693)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (13672)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (13677)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (13693)Refutation not found, incomplete strategy% (13693)------------------------------
% 0.20/0.52  % (13693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (13683)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (13693)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (13693)Memory used [KB]: 1791
% 0.20/0.52  % (13693)Time elapsed: 0.074 s
% 0.20/0.52  % (13693)------------------------------
% 0.20/0.52  % (13693)------------------------------
% 0.20/0.52  % (13675)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (13680)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (13670)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (13685)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (13690)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (13670)Refutation not found, incomplete strategy% (13670)------------------------------
% 0.20/0.53  % (13670)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.53  % (13694)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.37/0.53  % (13679)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.37/0.53  % (13672)Refutation not found, incomplete strategy% (13672)------------------------------
% 1.37/0.53  % (13672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.53  % (13672)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.53  
% 1.37/0.53  % (13672)Memory used [KB]: 10746
% 1.37/0.53  % (13672)Time elapsed: 0.112 s
% 1.37/0.53  % (13672)------------------------------
% 1.37/0.53  % (13672)------------------------------
% 1.37/0.53  % (13686)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.37/0.53  % (13674)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.37/0.53  % (13681)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.37/0.53  % (13697)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.37/0.53  % (13682)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.37/0.53  % (13695)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.37/0.54  % (13678)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.37/0.54  % (13690)Refutation not found, incomplete strategy% (13690)------------------------------
% 1.37/0.54  % (13690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (13690)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.54  
% 1.37/0.54  % (13690)Memory used [KB]: 10746
% 1.37/0.54  % (13690)Time elapsed: 0.135 s
% 1.37/0.54  % (13690)------------------------------
% 1.37/0.54  % (13690)------------------------------
% 1.37/0.54  % (13687)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.37/0.54  % (13673)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.37/0.54  % (13687)Refutation not found, incomplete strategy% (13687)------------------------------
% 1.37/0.54  % (13687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (13687)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.54  
% 1.37/0.54  % (13687)Memory used [KB]: 10618
% 1.37/0.54  % (13687)Time elapsed: 0.125 s
% 1.37/0.54  % (13687)------------------------------
% 1.37/0.54  % (13687)------------------------------
% 1.37/0.54  % (13670)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.54  
% 1.37/0.54  % (13670)Memory used [KB]: 1663
% 1.37/0.54  % (13670)Time elapsed: 0.123 s
% 1.37/0.54  % (13670)------------------------------
% 1.37/0.54  % (13670)------------------------------
% 1.37/0.54  % (13678)Refutation found. Thanks to Tanya!
% 1.37/0.54  % SZS status Theorem for theBenchmark
% 1.37/0.54  % SZS output start Proof for theBenchmark
% 1.37/0.54  fof(f239,plain,(
% 1.37/0.54    $false),
% 1.37/0.54    inference(avatar_sat_refutation,[],[f91,f123,f238])).
% 1.37/0.54  fof(f238,plain,(
% 1.37/0.54    ~spl5_1),
% 1.37/0.54    inference(avatar_contradiction_clause,[],[f237])).
% 1.37/0.54  fof(f237,plain,(
% 1.37/0.54    $false | ~spl5_1),
% 1.37/0.54    inference(subsumption_resolution,[],[f236,f168])).
% 1.37/0.54  fof(f168,plain,(
% 1.37/0.54    m1_subset_1(k2_mcart_1(sK4),sK2)),
% 1.37/0.54    inference(subsumption_resolution,[],[f167,f56])).
% 1.37/0.54  fof(f56,plain,(
% 1.37/0.54    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.37/0.54    inference(definition_unfolding,[],[f31,f42])).
% 1.37/0.54  fof(f42,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f5])).
% 1.37/0.54  fof(f5,axiom,(
% 1.37/0.54    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.37/0.54  fof(f31,plain,(
% 1.37/0.54    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.37/0.54    inference(cnf_transformation,[],[f28])).
% 1.37/0.54  fof(f28,plain,(
% 1.37/0.54    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.37/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f27])).
% 1.37/0.54  fof(f27,plain,(
% 1.37/0.54    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)))),
% 1.37/0.54    introduced(choice_axiom,[])).
% 1.37/0.54  % (13689)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.37/0.54  % (13676)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.49/0.54  % (13699)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.49/0.54  % (13692)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.49/0.55  % (13696)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.49/0.55  % (13692)Refutation not found, incomplete strategy% (13692)------------------------------
% 1.49/0.55  % (13692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.55  % (13692)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.55  
% 1.49/0.55  % (13692)Memory used [KB]: 10746
% 1.49/0.55  % (13692)Time elapsed: 0.149 s
% 1.49/0.55  % (13692)------------------------------
% 1.49/0.55  % (13692)------------------------------
% 1.49/0.55  % (13691)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.49/0.55  % (13691)Refutation not found, incomplete strategy% (13691)------------------------------
% 1.49/0.55  % (13691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.55  % (13691)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.55  
% 1.49/0.55  % (13691)Memory used [KB]: 1791
% 1.49/0.55  % (13691)Time elapsed: 0.150 s
% 1.49/0.55  % (13691)------------------------------
% 1.49/0.55  % (13691)------------------------------
% 1.49/0.55  % (13688)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.49/0.55  fof(f16,plain,(
% 1.49/0.55    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.49/0.55    inference(flattening,[],[f15])).
% 1.49/0.55  fof(f15,plain,(
% 1.49/0.55    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.49/0.55    inference(ennf_transformation,[],[f14])).
% 1.49/0.55  fof(f14,negated_conjecture,(
% 1.49/0.55    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.49/0.55    inference(negated_conjecture,[],[f13])).
% 1.49/0.55  fof(f13,conjecture,(
% 1.49/0.55    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_mcart_1)).
% 1.49/0.55  fof(f167,plain,(
% 1.49/0.55    m1_subset_1(k2_mcart_1(sK4),sK2) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.49/0.55    inference(superposition,[],[f66,f82])).
% 1.49/0.55  fof(f82,plain,(
% 1.49/0.55    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)),
% 1.49/0.55    inference(subsumption_resolution,[],[f81,f33])).
% 1.49/0.55  fof(f33,plain,(
% 1.49/0.55    k1_xboole_0 != sK0),
% 1.49/0.55    inference(cnf_transformation,[],[f28])).
% 1.49/0.55  fof(f81,plain,(
% 1.49/0.55    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK0),
% 1.49/0.55    inference(subsumption_resolution,[],[f80,f34])).
% 1.49/0.55  fof(f34,plain,(
% 1.49/0.55    k1_xboole_0 != sK1),
% 1.49/0.55    inference(cnf_transformation,[],[f28])).
% 1.49/0.55  fof(f80,plain,(
% 1.49/0.55    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.49/0.55    inference(subsumption_resolution,[],[f72,f35])).
% 1.49/0.55  fof(f35,plain,(
% 1.49/0.55    k1_xboole_0 != sK2),
% 1.49/0.55    inference(cnf_transformation,[],[f28])).
% 1.49/0.55  fof(f72,plain,(
% 1.49/0.55    k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.49/0.55    inference(resolution,[],[f56,f61])).
% 1.49/0.55  fof(f61,plain,(
% 1.49/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.49/0.55    inference(definition_unfolding,[],[f51,f42])).
% 1.49/0.55  fof(f51,plain,(
% 1.49/0.55    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.49/0.55    inference(cnf_transformation,[],[f23])).
% 1.49/0.55  fof(f23,plain,(
% 1.49/0.55    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.49/0.55    inference(ennf_transformation,[],[f12])).
% 1.49/0.55  fof(f12,axiom,(
% 1.49/0.55    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 1.49/0.55  fof(f66,plain,(
% 1.49/0.55    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 1.49/0.55    inference(definition_unfolding,[],[f54,f42])).
% 1.49/0.55  fof(f54,plain,(
% 1.49/0.55    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f26])).
% 1.49/0.55  fof(f26,plain,(
% 1.49/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 1.49/0.55    inference(ennf_transformation,[],[f8])).
% 1.49/0.55  fof(f8,axiom,(
% 1.49/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_mcart_1)).
% 1.49/0.55  fof(f236,plain,(
% 1.49/0.55    ~m1_subset_1(k2_mcart_1(sK4),sK2) | ~spl5_1),
% 1.49/0.55    inference(subsumption_resolution,[],[f235,f166])).
% 1.49/0.55  fof(f166,plain,(
% 1.49/0.55    sK3 != k2_mcart_1(sK4)),
% 1.49/0.55    inference(superposition,[],[f36,f82])).
% 1.49/0.55  fof(f36,plain,(
% 1.49/0.55    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)),
% 1.49/0.55    inference(cnf_transformation,[],[f28])).
% 1.49/0.55  fof(f235,plain,(
% 1.49/0.55    sK3 = k2_mcart_1(sK4) | ~m1_subset_1(k2_mcart_1(sK4),sK2) | ~spl5_1),
% 1.49/0.55    inference(trivial_inequality_removal,[],[f234])).
% 1.49/0.55  fof(f234,plain,(
% 1.49/0.55    sK4 != sK4 | sK3 = k2_mcart_1(sK4) | ~m1_subset_1(k2_mcart_1(sK4),sK2) | ~spl5_1),
% 1.49/0.55    inference(superposition,[],[f233,f155])).
% 1.49/0.55  fof(f155,plain,(
% 1.49/0.55    sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | ~spl5_1),
% 1.49/0.55    inference(subsumption_resolution,[],[f154,f38])).
% 1.49/0.55  fof(f38,plain,(
% 1.49/0.55    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f3])).
% 1.49/0.55  fof(f3,axiom,(
% 1.49/0.55    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.49/0.55  fof(f154,plain,(
% 1.49/0.55    sK4 = k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) | ~v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl5_1),
% 1.49/0.55    inference(resolution,[],[f86,f39])).
% 1.49/0.55  fof(f39,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~v1_relat_1(X1)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f19])).
% 1.49/0.55  fof(f19,plain,(
% 1.49/0.55    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 1.49/0.55    inference(flattening,[],[f18])).
% 1.49/0.55  fof(f18,plain,(
% 1.49/0.55    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 1.49/0.55    inference(ennf_transformation,[],[f10])).
% 1.49/0.55  fof(f10,axiom,(
% 1.49/0.55    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).
% 1.49/0.55  fof(f86,plain,(
% 1.49/0.55    r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl5_1),
% 1.49/0.55    inference(avatar_component_clause,[],[f84])).
% 1.49/0.55  fof(f84,plain,(
% 1.49/0.55    spl5_1 <=> r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.49/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.49/0.55  fof(f233,plain,(
% 1.49/0.55    ( ! [X0] : (sK4 != k4_tarski(k1_mcart_1(sK4),X0) | sK3 = X0 | ~m1_subset_1(X0,sK2)) ) | ~spl5_1),
% 1.49/0.55    inference(subsumption_resolution,[],[f232,f170])).
% 1.49/0.55  fof(f170,plain,(
% 1.49/0.55    m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)),
% 1.49/0.55    inference(subsumption_resolution,[],[f169,f56])).
% 1.49/0.55  fof(f169,plain,(
% 1.49/0.55    m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.49/0.55    inference(superposition,[],[f64,f76])).
% 1.49/0.55  fof(f76,plain,(
% 1.49/0.55    k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))),
% 1.49/0.55    inference(subsumption_resolution,[],[f75,f33])).
% 1.49/0.55  fof(f75,plain,(
% 1.49/0.55    k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK0),
% 1.49/0.55    inference(subsumption_resolution,[],[f74,f34])).
% 1.49/0.55  fof(f74,plain,(
% 1.49/0.55    k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.49/0.55    inference(subsumption_resolution,[],[f70,f35])).
% 1.49/0.55  fof(f70,plain,(
% 1.49/0.55    k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.49/0.55    inference(resolution,[],[f56,f63])).
% 1.49/0.55  fof(f63,plain,(
% 1.49/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.49/0.55    inference(definition_unfolding,[],[f49,f42])).
% 1.49/0.55  fof(f49,plain,(
% 1.49/0.55    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.49/0.55    inference(cnf_transformation,[],[f23])).
% 1.49/0.55  fof(f64,plain,(
% 1.49/0.55    ( ! [X2,X0,X3,X1] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 1.49/0.55    inference(definition_unfolding,[],[f52,f42])).
% 1.49/0.55  fof(f52,plain,(
% 1.49/0.55    ( ! [X2,X0,X3,X1] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f24])).
% 1.49/0.55  fof(f24,plain,(
% 1.49/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 1.49/0.55    inference(ennf_transformation,[],[f6])).
% 1.49/0.55  fof(f6,axiom,(
% 1.49/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_mcart_1)).
% 1.49/0.55  fof(f232,plain,(
% 1.49/0.55    ( ! [X0] : (sK4 != k4_tarski(k1_mcart_1(sK4),X0) | sK3 = X0 | ~m1_subset_1(X0,sK2) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)) ) | ~spl5_1),
% 1.49/0.55    inference(subsumption_resolution,[],[f231,f183])).
% 1.49/0.55  fof(f183,plain,(
% 1.49/0.55    m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1)),
% 1.49/0.55    inference(subsumption_resolution,[],[f182,f56])).
% 1.49/0.55  fof(f182,plain,(
% 1.49/0.55    m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.49/0.55    inference(superposition,[],[f65,f79])).
% 1.49/0.55  fof(f79,plain,(
% 1.49/0.55    k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))),
% 1.49/0.55    inference(subsumption_resolution,[],[f78,f33])).
% 1.49/0.55  fof(f78,plain,(
% 1.49/0.55    k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK0),
% 1.49/0.55    inference(subsumption_resolution,[],[f77,f34])).
% 1.49/0.55  fof(f77,plain,(
% 1.49/0.55    k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.49/0.55    inference(subsumption_resolution,[],[f71,f35])).
% 1.49/0.55  fof(f71,plain,(
% 1.49/0.55    k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.49/0.55    inference(resolution,[],[f56,f62])).
% 1.49/0.55  fof(f62,plain,(
% 1.49/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.49/0.55    inference(definition_unfolding,[],[f50,f42])).
% 1.49/0.55  fof(f50,plain,(
% 1.49/0.55    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.49/0.55    inference(cnf_transformation,[],[f23])).
% 1.49/0.55  fof(f65,plain,(
% 1.49/0.55    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 1.49/0.55    inference(definition_unfolding,[],[f53,f42])).
% 1.49/0.55  fof(f53,plain,(
% 1.49/0.55    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f25])).
% 1.49/0.55  fof(f25,plain,(
% 1.49/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 1.49/0.55    inference(ennf_transformation,[],[f7])).
% 1.49/0.55  fof(f7,axiom,(
% 1.49/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_mcart_1)).
% 1.49/0.55  fof(f231,plain,(
% 1.49/0.55    ( ! [X0] : (sK4 != k4_tarski(k1_mcart_1(sK4),X0) | sK3 = X0 | ~m1_subset_1(X0,sK2) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0)) ) | ~spl5_1),
% 1.49/0.55    inference(superposition,[],[f55,f197])).
% 1.49/0.55  fof(f197,plain,(
% 1.49/0.55    k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) | ~spl5_1),
% 1.49/0.55    inference(subsumption_resolution,[],[f196,f38])).
% 1.49/0.55  fof(f196,plain,(
% 1.49/0.55    k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl5_1),
% 1.49/0.55    inference(resolution,[],[f152,f39])).
% 1.49/0.55  fof(f152,plain,(
% 1.49/0.55    r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) | ~spl5_1),
% 1.49/0.55    inference(resolution,[],[f86,f43])).
% 1.49/0.55  fof(f43,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f22])).
% 1.49/0.55  fof(f22,plain,(
% 1.49/0.55    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.49/0.55    inference(ennf_transformation,[],[f9])).
% 1.49/0.55  fof(f9,axiom,(
% 1.49/0.55    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.49/0.55  fof(f55,plain,(
% 1.49/0.55    ( ! [X6,X7,X5] : (sK4 != k4_tarski(k4_tarski(X5,X6),X7) | sK3 = X7 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 1.49/0.55    inference(definition_unfolding,[],[f32,f41])).
% 1.49/0.55  fof(f41,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f4])).
% 1.49/0.55  fof(f4,axiom,(
% 1.49/0.55    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.49/0.55  fof(f32,plain,(
% 1.49/0.55    ( ! [X6,X7,X5] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f28])).
% 1.49/0.55  fof(f123,plain,(
% 1.49/0.55    ~spl5_2),
% 1.49/0.55    inference(avatar_contradiction_clause,[],[f122])).
% 1.49/0.55  fof(f122,plain,(
% 1.49/0.55    $false | ~spl5_2),
% 1.49/0.55    inference(subsumption_resolution,[],[f121,f33])).
% 1.49/0.55  fof(f121,plain,(
% 1.49/0.55    k1_xboole_0 = sK0 | ~spl5_2),
% 1.49/0.55    inference(subsumption_resolution,[],[f120,f34])).
% 1.49/0.55  fof(f120,plain,(
% 1.49/0.55    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl5_2),
% 1.49/0.55    inference(subsumption_resolution,[],[f110,f35])).
% 1.49/0.55  fof(f110,plain,(
% 1.49/0.55    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl5_2),
% 1.49/0.55    inference(trivial_inequality_removal,[],[f101])).
% 1.49/0.55  fof(f101,plain,(
% 1.49/0.55    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl5_2),
% 1.49/0.55    inference(superposition,[],[f60,f92])).
% 1.49/0.55  fof(f92,plain,(
% 1.49/0.55    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl5_2),
% 1.49/0.55    inference(resolution,[],[f90,f37])).
% 1.49/0.55  fof(f37,plain,(
% 1.49/0.55    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.49/0.55    inference(cnf_transformation,[],[f17])).
% 1.49/0.55  fof(f17,plain,(
% 1.49/0.55    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.49/0.55    inference(ennf_transformation,[],[f1])).
% 1.49/0.55  fof(f1,axiom,(
% 1.49/0.55    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.49/0.55  fof(f90,plain,(
% 1.49/0.55    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl5_2),
% 1.49/0.55    inference(avatar_component_clause,[],[f88])).
% 1.49/0.55  fof(f88,plain,(
% 1.49/0.55    spl5_2 <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.49/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.49/0.55  fof(f60,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.49/0.55    inference(definition_unfolding,[],[f45,f42])).
% 1.49/0.55  fof(f45,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.49/0.55    inference(cnf_transformation,[],[f30])).
% 1.49/0.55  fof(f30,plain,(
% 1.49/0.55    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.49/0.55    inference(flattening,[],[f29])).
% 1.49/0.55  fof(f29,plain,(
% 1.49/0.55    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | (k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.49/0.55    inference(nnf_transformation,[],[f11])).
% 1.49/0.55  fof(f11,axiom,(
% 1.49/0.55    ! [X0,X1,X2] : ((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).
% 1.49/0.55  fof(f91,plain,(
% 1.49/0.55    spl5_1 | spl5_2),
% 1.49/0.55    inference(avatar_split_clause,[],[f73,f88,f84])).
% 1.49/0.55  fof(f73,plain,(
% 1.49/0.55    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.49/0.55    inference(resolution,[],[f56,f40])).
% 1.49/0.55  fof(f40,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f21])).
% 1.49/0.55  fof(f21,plain,(
% 1.49/0.55    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.49/0.55    inference(flattening,[],[f20])).
% 1.49/0.55  fof(f20,plain,(
% 1.49/0.55    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.49/0.55    inference(ennf_transformation,[],[f2])).
% 1.49/0.55  fof(f2,axiom,(
% 1.49/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.49/0.55  % SZS output end Proof for theBenchmark
% 1.49/0.55  % (13678)------------------------------
% 1.49/0.55  % (13678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.55  % (13678)Termination reason: Refutation
% 1.49/0.55  
% 1.49/0.55  % (13678)Memory used [KB]: 10746
% 1.49/0.55  % (13678)Time elapsed: 0.142 s
% 1.49/0.55  % (13678)------------------------------
% 1.49/0.55  % (13678)------------------------------
% 1.49/0.56  % (13669)Success in time 0.2 s
%------------------------------------------------------------------------------
