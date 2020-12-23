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
% DateTime   : Thu Dec  3 13:07:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 353 expanded)
%              Number of leaves         :   24 ( 140 expanded)
%              Depth                    :   17
%              Number of atoms          :  400 (3026 expanded)
%              Number of equality atoms :   41 (  51 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f747,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f141,f142,f151,f214,f226,f584,f599,f691])).

fof(f691,plain,(
    ~ spl8_14 ),
    inference(avatar_contradiction_clause,[],[f690])).

fof(f690,plain,
    ( $false
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f614,f88])).

fof(f88,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f614,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_14 ),
    inference(backward_demodulation,[],[f80,f225])).

fof(f225,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl8_14
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f80,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,
    ( ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
      | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) )
    & ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
      | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) )
    & m1_subset_1(sK4,k1_zfmisc_1(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f60,f65,f64,f63,f62,f61])).

fof(f61,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ( ~ r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                          | ~ r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                        & ( r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                          | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                        & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                    & m1_subset_1(X3,k1_zfmisc_1(X0)) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4))
                        | ~ r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4) )
                      & ( r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4))
                        | r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
              & v1_funct_2(X2,sK0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ( ~ r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4))
                      | ~ r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4) )
                    & ( r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4))
                      | r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4) )
                    & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
            & v1_funct_2(X2,sK0,X1)
            & v1_funct_1(X2) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ~ r1_tarski(X3,k8_relset_1(sK0,sK1,X2,X4))
                    | ~ r1_tarski(k7_relset_1(sK0,sK1,X2,X3),X4) )
                  & ( r1_tarski(X3,k8_relset_1(sK0,sK1,X2,X4))
                    | r1_tarski(k7_relset_1(sK0,sK1,X2,X3),X4) )
                  & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
              & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X2,sK0,sK1)
          & v1_funct_1(X2) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

% (16627)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f63,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ( ~ r1_tarski(X3,k8_relset_1(sK0,sK1,X2,X4))
                  | ~ r1_tarski(k7_relset_1(sK0,sK1,X2,X3),X4) )
                & ( r1_tarski(X3,k8_relset_1(sK0,sK1,X2,X4))
                  | r1_tarski(k7_relset_1(sK0,sK1,X2,X3),X4) )
                & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
            & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X2,sK0,sK1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ( ~ r1_tarski(X3,k8_relset_1(sK0,sK1,sK2,X4))
                | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,X3),X4) )
              & ( r1_tarski(X3,k8_relset_1(sK0,sK1,sK2,X4))
                | r1_tarski(k7_relset_1(sK0,sK1,sK2,X3),X4) )
              & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
          & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ( ~ r1_tarski(X3,k8_relset_1(sK0,sK1,sK2,X4))
              | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,X3),X4) )
            & ( r1_tarski(X3,k8_relset_1(sK0,sK1,sK2,X4))
              | r1_tarski(k7_relset_1(sK0,sK1,sK2,X3),X4) )
            & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
        & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
   => ( ? [X4] :
          ( ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,X4))
            | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X4) )
          & ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,X4))
            | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X4) )
          & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK3,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,
    ( ? [X4] :
        ( ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,X4))
          | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X4) )
        & ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,X4))
          | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X4) )
        & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
   => ( ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
        | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) )
      & ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
        | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) )
      & m1_subset_1(sK4,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                        | ~ r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                      & ( r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                        | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                        | ~ r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                      & ( r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                        | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                      <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                      <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X2,X0,X1)
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(X1))
                       => ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                        <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f29])).

fof(f29,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(X1))
                     => ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                      <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_2)).

fof(f599,plain,
    ( ~ spl8_1
    | spl8_2
    | ~ spl8_13 ),
    inference(avatar_contradiction_clause,[],[f598])).

fof(f598,plain,
    ( $false
    | ~ spl8_1
    | spl8_2
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f597,f152])).

fof(f152,plain,(
    r1_tarski(sK3,sK0) ),
    inference(resolution,[],[f84,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f84,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f66])).

fof(f597,plain,
    ( ~ r1_tarski(sK3,sK0)
    | ~ spl8_1
    | spl8_2
    | ~ spl8_13 ),
    inference(forward_demodulation,[],[f596,f248])).

fof(f248,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl8_13 ),
    inference(backward_demodulation,[],[f215,f221])).

fof(f221,plain,
    ( sK0 = k8_relset_1(sK0,sK1,sK2,sK1)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl8_13
  <=> sK0 = k8_relset_1(sK0,sK1,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f215,plain,(
    k1_relat_1(sK2) = k8_relset_1(sK0,sK1,sK2,sK1) ),
    inference(forward_demodulation,[],[f206,f203])).

fof(f203,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f83,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f83,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f66])).

fof(f206,plain,(
    k1_relset_1(sK0,sK1,sK2) = k8_relset_1(sK0,sK1,sK2,sK1) ),
    inference(resolution,[],[f83,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f596,plain,
    ( ~ r1_tarski(sK3,k1_relat_1(sK2))
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f595,f202])).

fof(f202,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f83,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f595,plain,
    ( ~ r1_tarski(sK3,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f594,f81])).

fof(f81,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f66])).

fof(f594,plain,
    ( ~ r1_tarski(sK3,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f588,f585])).

fof(f585,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | spl8_2 ),
    inference(forward_demodulation,[],[f140,f209])).

fof(f209,plain,(
    ! [X1] : k8_relset_1(sK0,sK1,sK2,X1) = k10_relat_1(sK2,X1) ),
    inference(resolution,[],[f83,f125])).

fof(f125,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

% (16639)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f140,plain,
    ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | spl8_2 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl8_2
  <=> r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f588,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ r1_tarski(sK3,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_1 ),
    inference(resolution,[],[f586,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

fof(f586,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl8_1 ),
    inference(forward_demodulation,[],[f135,f208])).

fof(f208,plain,(
    ! [X0] : k7_relset_1(sK0,sK1,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(resolution,[],[f83,f124])).

fof(f124,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f135,plain,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl8_1
  <=> r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f584,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f583])).

fof(f583,plain,
    ( $false
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f577,f227])).

fof(f227,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | spl8_1 ),
    inference(backward_demodulation,[],[f136,f208])).

fof(f136,plain,
    ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f134])).

fof(f577,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(resolution,[],[f316,f405])).

fof(f405,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4)))
    | ~ spl8_2 ),
    inference(resolution,[],[f255,f202])).

fof(f255,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | r1_tarski(k9_relat_1(X1,sK3),k9_relat_1(X1,k10_relat_1(sK2,sK4))) )
    | ~ spl8_2 ),
    inference(resolution,[],[f229,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

fof(f229,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl8_2 ),
    inference(backward_demodulation,[],[f139,f209])).

fof(f139,plain,
    ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f138])).

fof(f316,plain,
    ( ! [X2,X1] :
        ( ~ r1_tarski(X1,k9_relat_1(sK2,k10_relat_1(sK2,X2)))
        | r1_tarski(X1,X2) )
    | ~ spl8_4 ),
    inference(resolution,[],[f150,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f150,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl8_4
  <=> ! [X0] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f226,plain,
    ( spl8_13
    | spl8_14 ),
    inference(avatar_split_clause,[],[f217,f223,f219])).

fof(f217,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k8_relset_1(sK0,sK1,sK2,sK1) ),
    inference(subsumption_resolution,[],[f216,f81])).

fof(f216,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k8_relset_1(sK0,sK1,sK2,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f207,f82])).

fof(f82,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f207,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k8_relset_1(sK0,sK1,sK2,sK1)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f83,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k8_relset_1(X0,X1,X2,X1) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).

fof(f214,plain,(
    spl8_3 ),
    inference(avatar_contradiction_clause,[],[f213])).

fof(f213,plain,
    ( $false
    | spl8_3 ),
    inference(subsumption_resolution,[],[f202,f147])).

fof(f147,plain,
    ( ~ v1_relat_1(sK2)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl8_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f151,plain,
    ( ~ spl8_3
    | spl8_4 ),
    inference(avatar_split_clause,[],[f143,f149,f145])).

fof(f143,plain,(
    ! [X0] :
      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f81,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

% (16649)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f142,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f86,f138,f134])).

fof(f86,plain,
    ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f66])).

fof(f141,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f87,f138,f134])).

fof(f87,plain,
    ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f66])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:25:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (16631)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.49  % (16647)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.50  % (16624)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (16644)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.50  % (16625)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.50  % (16628)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (16632)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (16626)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (16636)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (16640)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (16652)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (16650)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.52  % (16646)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (16635)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (16638)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (16634)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (16632)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (16648)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.30/0.53  % (16629)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.30/0.53  % (16642)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.30/0.53  % (16630)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.30/0.53  % (16653)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.30/0.53  % SZS output start Proof for theBenchmark
% 1.30/0.53  fof(f747,plain,(
% 1.30/0.53    $false),
% 1.30/0.53    inference(avatar_sat_refutation,[],[f141,f142,f151,f214,f226,f584,f599,f691])).
% 1.30/0.53  fof(f691,plain,(
% 1.30/0.53    ~spl8_14),
% 1.30/0.53    inference(avatar_contradiction_clause,[],[f690])).
% 1.30/0.53  fof(f690,plain,(
% 1.30/0.53    $false | ~spl8_14),
% 1.30/0.53    inference(subsumption_resolution,[],[f614,f88])).
% 1.30/0.53  fof(f88,plain,(
% 1.30/0.53    v1_xboole_0(k1_xboole_0)),
% 1.30/0.53    inference(cnf_transformation,[],[f3])).
% 1.30/0.53  fof(f3,axiom,(
% 1.30/0.53    v1_xboole_0(k1_xboole_0)),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.30/0.53  fof(f614,plain,(
% 1.30/0.53    ~v1_xboole_0(k1_xboole_0) | ~spl8_14),
% 1.30/0.53    inference(backward_demodulation,[],[f80,f225])).
% 1.30/0.53  fof(f225,plain,(
% 1.30/0.53    k1_xboole_0 = sK1 | ~spl8_14),
% 1.30/0.53    inference(avatar_component_clause,[],[f223])).
% 1.30/0.53  fof(f223,plain,(
% 1.30/0.53    spl8_14 <=> k1_xboole_0 = sK1),
% 1.30/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 1.30/0.53  fof(f80,plain,(
% 1.30/0.53    ~v1_xboole_0(sK1)),
% 1.30/0.53    inference(cnf_transformation,[],[f66])).
% 1.30/0.53  fof(f66,plain,(
% 1.30/0.53    (((((~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)) & (r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)) & m1_subset_1(sK4,k1_zfmisc_1(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 1.30/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f60,f65,f64,f63,f62,f61])).
% 1.30/0.53  fof(f61,plain,(
% 1.30/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4)) | r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) & v1_funct_2(X2,sK0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  fof(f62,plain,(
% 1.30/0.53    ? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4)) | r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) & v1_funct_2(X2,sK0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK0,sK1,X2,X4)) | ~r1_tarski(k7_relset_1(sK0,sK1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK0,sK1,X2,X4)) | r1_tarski(k7_relset_1(sK0,sK1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X2,sK0,sK1) & v1_funct_1(X2)) & ~v1_xboole_0(sK1))),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  % (16627)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.30/0.53  fof(f63,plain,(
% 1.30/0.53    ? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK0,sK1,X2,X4)) | ~r1_tarski(k7_relset_1(sK0,sK1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK0,sK1,X2,X4)) | r1_tarski(k7_relset_1(sK0,sK1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X2,sK0,sK1) & v1_funct_1(X2)) => (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK0,sK1,sK2,X4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK0,sK1,sK2,X4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  fof(f64,plain,(
% 1.30/0.53    ? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK0,sK1,sK2,X4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK0,sK1,sK2,X4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(X3,k1_zfmisc_1(sK0))) => (? [X4] : ((~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,X4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X4)) & (r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,X4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(sK0)))),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  fof(f65,plain,(
% 1.30/0.53    ? [X4] : ((~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,X4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X4)) & (r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,X4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK1))) => ((~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)) & (r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)) & m1_subset_1(sK4,k1_zfmisc_1(sK1)))),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  fof(f60,plain,(
% 1.30/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.30/0.53    inference(flattening,[],[f59])).
% 1.30/0.53  fof(f59,plain,(
% 1.30/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.30/0.53    inference(nnf_transformation,[],[f33])).
% 1.30/0.53  fof(f33,plain,(
% 1.30/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.30/0.53    inference(flattening,[],[f32])).
% 1.30/0.53  fof(f32,plain,(
% 1.30/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.30/0.53    inference(ennf_transformation,[],[f30])).
% 1.30/0.53  fof(f30,negated_conjecture,(
% 1.30/0.53    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 1.30/0.53    inference(negated_conjecture,[],[f29])).
% 1.30/0.53  fof(f29,conjecture,(
% 1.30/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_2)).
% 1.30/0.53  fof(f599,plain,(
% 1.30/0.53    ~spl8_1 | spl8_2 | ~spl8_13),
% 1.30/0.53    inference(avatar_contradiction_clause,[],[f598])).
% 1.30/0.53  fof(f598,plain,(
% 1.30/0.53    $false | (~spl8_1 | spl8_2 | ~spl8_13)),
% 1.30/0.53    inference(subsumption_resolution,[],[f597,f152])).
% 1.30/0.53  fof(f152,plain,(
% 1.30/0.53    r1_tarski(sK3,sK0)),
% 1.30/0.53    inference(resolution,[],[f84,f107])).
% 1.30/0.53  fof(f107,plain,(
% 1.30/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f76])).
% 1.30/0.53  fof(f76,plain,(
% 1.30/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.30/0.53    inference(nnf_transformation,[],[f14])).
% 1.30/0.53  fof(f14,axiom,(
% 1.30/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.30/0.53  fof(f84,plain,(
% 1.30/0.53    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 1.30/0.53    inference(cnf_transformation,[],[f66])).
% 1.30/0.53  fof(f597,plain,(
% 1.30/0.53    ~r1_tarski(sK3,sK0) | (~spl8_1 | spl8_2 | ~spl8_13)),
% 1.30/0.53    inference(forward_demodulation,[],[f596,f248])).
% 1.30/0.53  fof(f248,plain,(
% 1.30/0.53    sK0 = k1_relat_1(sK2) | ~spl8_13),
% 1.30/0.53    inference(backward_demodulation,[],[f215,f221])).
% 1.30/0.53  fof(f221,plain,(
% 1.30/0.53    sK0 = k8_relset_1(sK0,sK1,sK2,sK1) | ~spl8_13),
% 1.30/0.53    inference(avatar_component_clause,[],[f219])).
% 1.30/0.53  fof(f219,plain,(
% 1.30/0.53    spl8_13 <=> sK0 = k8_relset_1(sK0,sK1,sK2,sK1)),
% 1.30/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 1.30/0.53  fof(f215,plain,(
% 1.30/0.53    k1_relat_1(sK2) = k8_relset_1(sK0,sK1,sK2,sK1)),
% 1.30/0.53    inference(forward_demodulation,[],[f206,f203])).
% 1.30/0.53  fof(f203,plain,(
% 1.30/0.53    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 1.30/0.53    inference(resolution,[],[f83,f115])).
% 1.30/0.53  fof(f115,plain,(
% 1.30/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f47])).
% 1.30/0.53  fof(f47,plain,(
% 1.30/0.53    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.53    inference(ennf_transformation,[],[f24])).
% 1.30/0.53  fof(f24,axiom,(
% 1.30/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.30/0.53  fof(f83,plain,(
% 1.30/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.30/0.53    inference(cnf_transformation,[],[f66])).
% 1.30/0.53  fof(f206,plain,(
% 1.30/0.53    k1_relset_1(sK0,sK1,sK2) = k8_relset_1(sK0,sK1,sK2,sK1)),
% 1.30/0.53    inference(resolution,[],[f83,f118])).
% 1.30/0.53  fof(f118,plain,(
% 1.30/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f49])).
% 1.30/0.53  fof(f49,plain,(
% 1.30/0.53    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.53    inference(ennf_transformation,[],[f27])).
% 1.30/0.53  fof(f27,axiom,(
% 1.30/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 1.30/0.53  fof(f596,plain,(
% 1.30/0.53    ~r1_tarski(sK3,k1_relat_1(sK2)) | (~spl8_1 | spl8_2)),
% 1.30/0.53    inference(subsumption_resolution,[],[f595,f202])).
% 1.30/0.53  fof(f202,plain,(
% 1.30/0.53    v1_relat_1(sK2)),
% 1.30/0.53    inference(resolution,[],[f83,f114])).
% 1.30/0.53  fof(f114,plain,(
% 1.30/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f46])).
% 1.30/0.53  fof(f46,plain,(
% 1.30/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.53    inference(ennf_transformation,[],[f22])).
% 1.30/0.53  fof(f22,axiom,(
% 1.30/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.30/0.53  fof(f595,plain,(
% 1.30/0.53    ~r1_tarski(sK3,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl8_1 | spl8_2)),
% 1.30/0.53    inference(subsumption_resolution,[],[f594,f81])).
% 1.30/0.53  fof(f81,plain,(
% 1.30/0.53    v1_funct_1(sK2)),
% 1.30/0.53    inference(cnf_transformation,[],[f66])).
% 1.30/0.53  fof(f594,plain,(
% 1.30/0.53    ~r1_tarski(sK3,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl8_1 | spl8_2)),
% 1.30/0.53    inference(subsumption_resolution,[],[f588,f585])).
% 1.30/0.53  fof(f585,plain,(
% 1.30/0.53    ~r1_tarski(sK3,k10_relat_1(sK2,sK4)) | spl8_2),
% 1.30/0.53    inference(forward_demodulation,[],[f140,f209])).
% 1.30/0.53  fof(f209,plain,(
% 1.30/0.53    ( ! [X1] : (k8_relset_1(sK0,sK1,sK2,X1) = k10_relat_1(sK2,X1)) )),
% 1.30/0.53    inference(resolution,[],[f83,f125])).
% 1.30/0.53  fof(f125,plain,(
% 1.30/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f58])).
% 1.30/0.53  fof(f58,plain,(
% 1.30/0.53    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.53    inference(ennf_transformation,[],[f26])).
% 1.30/0.53  fof(f26,axiom,(
% 1.30/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 1.30/0.53  % (16639)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.30/0.53  fof(f140,plain,(
% 1.30/0.53    ~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | spl8_2),
% 1.30/0.53    inference(avatar_component_clause,[],[f138])).
% 1.30/0.53  fof(f138,plain,(
% 1.30/0.53    spl8_2 <=> r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))),
% 1.30/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.30/0.53  fof(f588,plain,(
% 1.30/0.53    r1_tarski(sK3,k10_relat_1(sK2,sK4)) | ~r1_tarski(sK3,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl8_1),
% 1.30/0.53    inference(resolution,[],[f586,f121])).
% 1.30/0.53  fof(f121,plain,(
% 1.30/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k9_relat_1(X2,X0),X1) | r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f53])).
% 1.30/0.53  fof(f53,plain,(
% 1.30/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.30/0.53    inference(flattening,[],[f52])).
% 1.30/0.53  fof(f52,plain,(
% 1.30/0.53    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.30/0.53    inference(ennf_transformation,[],[f21])).
% 1.30/0.53  fof(f21,axiom,(
% 1.30/0.53    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).
% 1.30/0.53  fof(f586,plain,(
% 1.30/0.53    r1_tarski(k9_relat_1(sK2,sK3),sK4) | ~spl8_1),
% 1.30/0.53    inference(forward_demodulation,[],[f135,f208])).
% 1.30/0.53  fof(f208,plain,(
% 1.30/0.53    ( ! [X0] : (k7_relset_1(sK0,sK1,sK2,X0) = k9_relat_1(sK2,X0)) )),
% 1.30/0.53    inference(resolution,[],[f83,f124])).
% 1.30/0.53  fof(f124,plain,(
% 1.30/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f57])).
% 1.30/0.53  fof(f57,plain,(
% 1.30/0.53    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.53    inference(ennf_transformation,[],[f25])).
% 1.30/0.53  fof(f25,axiom,(
% 1.30/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.30/0.53  fof(f135,plain,(
% 1.30/0.53    r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) | ~spl8_1),
% 1.30/0.53    inference(avatar_component_clause,[],[f134])).
% 1.30/0.53  fof(f134,plain,(
% 1.30/0.53    spl8_1 <=> r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 1.30/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.30/0.53  fof(f584,plain,(
% 1.30/0.53    spl8_1 | ~spl8_2 | ~spl8_4),
% 1.30/0.53    inference(avatar_contradiction_clause,[],[f583])).
% 1.30/0.53  fof(f583,plain,(
% 1.30/0.53    $false | (spl8_1 | ~spl8_2 | ~spl8_4)),
% 1.30/0.53    inference(subsumption_resolution,[],[f577,f227])).
% 1.30/0.53  fof(f227,plain,(
% 1.30/0.53    ~r1_tarski(k9_relat_1(sK2,sK3),sK4) | spl8_1),
% 1.30/0.53    inference(backward_demodulation,[],[f136,f208])).
% 1.30/0.53  fof(f136,plain,(
% 1.30/0.53    ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) | spl8_1),
% 1.30/0.53    inference(avatar_component_clause,[],[f134])).
% 1.30/0.53  fof(f577,plain,(
% 1.30/0.53    r1_tarski(k9_relat_1(sK2,sK3),sK4) | (~spl8_2 | ~spl8_4)),
% 1.30/0.53    inference(resolution,[],[f316,f405])).
% 1.30/0.53  fof(f405,plain,(
% 1.30/0.53    r1_tarski(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4))) | ~spl8_2),
% 1.30/0.53    inference(resolution,[],[f255,f202])).
% 1.30/0.53  fof(f255,plain,(
% 1.30/0.53    ( ! [X1] : (~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,sK3),k9_relat_1(X1,k10_relat_1(sK2,sK4)))) ) | ~spl8_2),
% 1.30/0.53    inference(resolution,[],[f229,f112])).
% 1.30/0.53  fof(f112,plain,(
% 1.30/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f44])).
% 1.30/0.53  fof(f44,plain,(
% 1.30/0.53    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 1.30/0.53    inference(flattening,[],[f43])).
% 1.30/0.53  fof(f43,plain,(
% 1.30/0.53    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 1.30/0.53    inference(ennf_transformation,[],[f18])).
% 1.30/0.53  fof(f18,axiom,(
% 1.30/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).
% 1.30/0.53  fof(f229,plain,(
% 1.30/0.53    r1_tarski(sK3,k10_relat_1(sK2,sK4)) | ~spl8_2),
% 1.30/0.53    inference(backward_demodulation,[],[f139,f209])).
% 1.30/0.53  fof(f139,plain,(
% 1.30/0.53    r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~spl8_2),
% 1.30/0.53    inference(avatar_component_clause,[],[f138])).
% 1.30/0.53  fof(f316,plain,(
% 1.30/0.53    ( ! [X2,X1] : (~r1_tarski(X1,k9_relat_1(sK2,k10_relat_1(sK2,X2))) | r1_tarski(X1,X2)) ) | ~spl8_4),
% 1.30/0.53    inference(resolution,[],[f150,f122])).
% 1.30/0.53  fof(f122,plain,(
% 1.30/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f55])).
% 1.30/0.53  fof(f55,plain,(
% 1.30/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.30/0.53    inference(flattening,[],[f54])).
% 1.30/0.53  fof(f54,plain,(
% 1.30/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.30/0.53    inference(ennf_transformation,[],[f7])).
% 1.30/0.53  fof(f7,axiom,(
% 1.30/0.53    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.30/0.53  fof(f150,plain,(
% 1.30/0.53    ( ! [X0] : (r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)) ) | ~spl8_4),
% 1.30/0.53    inference(avatar_component_clause,[],[f149])).
% 1.30/0.53  fof(f149,plain,(
% 1.30/0.53    spl8_4 <=> ! [X0] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)),
% 1.30/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.30/0.53  fof(f226,plain,(
% 1.30/0.53    spl8_13 | spl8_14),
% 1.30/0.53    inference(avatar_split_clause,[],[f217,f223,f219])).
% 1.30/0.53  fof(f217,plain,(
% 1.30/0.53    k1_xboole_0 = sK1 | sK0 = k8_relset_1(sK0,sK1,sK2,sK1)),
% 1.30/0.53    inference(subsumption_resolution,[],[f216,f81])).
% 1.30/0.53  fof(f216,plain,(
% 1.30/0.53    k1_xboole_0 = sK1 | sK0 = k8_relset_1(sK0,sK1,sK2,sK1) | ~v1_funct_1(sK2)),
% 1.30/0.53    inference(subsumption_resolution,[],[f207,f82])).
% 1.30/0.53  fof(f82,plain,(
% 1.30/0.53    v1_funct_2(sK2,sK0,sK1)),
% 1.30/0.53    inference(cnf_transformation,[],[f66])).
% 1.30/0.53  fof(f207,plain,(
% 1.30/0.53    k1_xboole_0 = sK1 | sK0 = k8_relset_1(sK0,sK1,sK2,sK1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.30/0.53    inference(resolution,[],[f83,f119])).
% 1.30/0.53  fof(f119,plain,(
% 1.30/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k8_relset_1(X0,X1,X2,X1) = X0 | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f51])).
% 1.30/0.53  fof(f51,plain,(
% 1.30/0.53    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.30/0.53    inference(flattening,[],[f50])).
% 1.30/0.53  fof(f50,plain,(
% 1.30/0.53    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.30/0.53    inference(ennf_transformation,[],[f28])).
% 1.30/0.53  fof(f28,axiom,(
% 1.30/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).
% 1.30/0.53  fof(f214,plain,(
% 1.30/0.53    spl8_3),
% 1.30/0.53    inference(avatar_contradiction_clause,[],[f213])).
% 1.30/0.53  fof(f213,plain,(
% 1.30/0.53    $false | spl8_3),
% 1.30/0.53    inference(subsumption_resolution,[],[f202,f147])).
% 1.30/0.53  fof(f147,plain,(
% 1.30/0.53    ~v1_relat_1(sK2) | spl8_3),
% 1.30/0.53    inference(avatar_component_clause,[],[f145])).
% 1.30/0.53  fof(f145,plain,(
% 1.30/0.53    spl8_3 <=> v1_relat_1(sK2)),
% 1.30/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.30/0.53  fof(f151,plain,(
% 1.30/0.53    ~spl8_3 | spl8_4),
% 1.30/0.53    inference(avatar_split_clause,[],[f143,f149,f145])).
% 1.30/0.53  fof(f143,plain,(
% 1.30/0.53    ( ! [X0] : (r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0) | ~v1_relat_1(sK2)) )),
% 1.30/0.53    inference(resolution,[],[f81,f100])).
% 1.30/0.53  fof(f100,plain,(
% 1.30/0.53    ( ! [X0,X1] : (~v1_funct_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f41])).
% 1.30/0.54  % (16649)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.30/0.54  fof(f41,plain,(
% 1.30/0.54    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.30/0.54    inference(flattening,[],[f40])).
% 1.30/0.54  fof(f40,plain,(
% 1.30/0.54    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.30/0.54    inference(ennf_transformation,[],[f20])).
% 1.30/0.54  fof(f20,axiom,(
% 1.30/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 1.30/0.54  fof(f142,plain,(
% 1.30/0.54    spl8_1 | spl8_2),
% 1.30/0.54    inference(avatar_split_clause,[],[f86,f138,f134])).
% 1.30/0.54  fof(f86,plain,(
% 1.30/0.54    r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 1.30/0.54    inference(cnf_transformation,[],[f66])).
% 1.30/0.54  fof(f141,plain,(
% 1.30/0.54    ~spl8_1 | ~spl8_2),
% 1.30/0.54    inference(avatar_split_clause,[],[f87,f138,f134])).
% 1.30/0.54  fof(f87,plain,(
% 1.30/0.54    ~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 1.30/0.54    inference(cnf_transformation,[],[f66])).
% 1.30/0.54  % SZS output end Proof for theBenchmark
% 1.30/0.54  % (16632)------------------------------
% 1.30/0.54  % (16632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (16632)Termination reason: Refutation
% 1.30/0.54  
% 1.30/0.54  % (16632)Memory used [KB]: 11129
% 1.30/0.54  % (16632)Time elapsed: 0.119 s
% 1.30/0.54  % (16632)------------------------------
% 1.30/0.54  % (16632)------------------------------
% 1.30/0.54  % (16623)Success in time 0.183 s
%------------------------------------------------------------------------------
