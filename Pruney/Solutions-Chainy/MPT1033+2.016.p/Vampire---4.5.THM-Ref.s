%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 255 expanded)
%              Number of leaves         :   21 (  84 expanded)
%              Depth                    :   12
%              Number of atoms          :  387 (1723 expanded)
%              Number of equality atoms :   47 ( 317 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f334,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f225,f226,f234,f235,f248,f263,f304,f306,f333])).

fof(f333,plain,
    ( ~ spl6_4
    | ~ spl6_6
    | spl6_11 ),
    inference(avatar_contradiction_clause,[],[f332])).

fof(f332,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_6
    | spl6_11 ),
    inference(subsumption_resolution,[],[f331,f174])).

fof(f174,plain,
    ( sK2 != sK3
    | spl6_11 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl6_11
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f331,plain,
    ( sK2 = sK3
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f98,f89])).

fof(f89,plain,
    ( sK2 = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl6_4
  <=> sK2 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f98,plain,
    ( k2_zfmisc_1(sK0,sK1) = sK3
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl6_6
  <=> k2_zfmisc_1(sK0,sK1) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f306,plain,
    ( ~ spl6_15
    | spl6_16 ),
    inference(avatar_split_clause,[],[f305,f207,f203])).

fof(f203,plain,
    ( spl6_15
  <=> v1_partfun1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f207,plain,
    ( spl6_16
  <=> ! [X1] :
        ( ~ r1_partfun1(X1,sK3)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | sK3 = X1
        | ~ v1_partfun1(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f305,plain,(
    ! [X0] :
      ( ~ r1_partfun1(X0,sK3)
      | ~ v1_partfun1(sK3,sK0)
      | ~ v1_partfun1(X0,sK0)
      | sK3 = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f281,f38])).

fof(f38,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_partfun1(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f22,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ( k1_xboole_0 = X0
              | k1_xboole_0 != X1 )
            & r1_partfun1(X2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK0,sK1,sK2,X3)
          & ( k1_xboole_0 = sK0
            | k1_xboole_0 != sK1 )
          & r1_partfun1(sK2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X3,sK0,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK0,sK1,sK2,X3)
        & ( k1_xboole_0 = sK0
          | k1_xboole_0 != sK1 )
        & r1_partfun1(sK2,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X3,sK0,sK1)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_partfun1(sK2,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( r1_partfun1(X2,X3)
             => ( r2_relset_1(X0,X1,X2,X3)
                | ( k1_xboole_0 != X0
                  & k1_xboole_0 = X1 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_relset_1(X0,X1,X2,X3)
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).

fof(f281,plain,(
    ! [X0] :
      ( ~ r1_partfun1(X0,sK3)
      | ~ v1_partfun1(sK3,sK0)
      | ~ v1_partfun1(X0,sK0)
      | sK3 = X0
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f40,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_partfun1(X2,X3)
      | ~ v1_partfun1(X3,X0)
      | ~ v1_partfun1(X2,X0)
      | X2 = X3
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( r1_partfun1(X2,X3)
              & v1_partfun1(X3,X0)
              & v1_partfun1(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f304,plain,
    ( spl6_11
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(avatar_contradiction_clause,[],[f303])).

fof(f303,plain,
    ( $false
    | spl6_11
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f302,f213])).

% (29939)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f213,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl6_17
  <=> v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f302,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | spl6_11
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f301,f174])).

fof(f301,plain,
    ( sK2 = sK3
    | ~ v1_partfun1(sK2,sK0)
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f300,f41])).

fof(f41,plain,(
    r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f300,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | sK2 = sK3
    | ~ v1_partfun1(sK2,sK0)
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f297,f35])).

fof(f35,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f297,plain,
    ( ~ v1_funct_1(sK2)
    | ~ r1_partfun1(sK2,sK3)
    | sK2 = sK3
    | ~ v1_partfun1(sK2,sK0)
    | ~ spl6_16 ),
    inference(resolution,[],[f208,f37])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f208,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X1)
        | ~ r1_partfun1(X1,sK3)
        | sK3 = X1
        | ~ v1_partfun1(X1,sK0) )
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f207])).

fof(f263,plain,(
    ~ spl6_11 ),
    inference(avatar_contradiction_clause,[],[f262])).

fof(f262,plain,
    ( $false
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f253,f140])).

fof(f140,plain,(
    r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(resolution,[],[f61,f37])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_relset_1(X1,X2,X0,X0) ) ),
    inference(condensation,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f253,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl6_11 ),
    inference(backward_demodulation,[],[f43,f175])).

fof(f175,plain,
    ( sK2 = sK3
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f173])).

fof(f43,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f248,plain,
    ( ~ spl6_7
    | spl6_19 ),
    inference(avatar_split_clause,[],[f245,f231,f118])).

fof(f118,plain,
    ( spl6_7
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f231,plain,
    ( spl6_19
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f245,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_19 ),
    inference(resolution,[],[f233,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X1,X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f116,f59])).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

% (29936)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X2,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f48,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f233,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl6_19 ),
    inference(avatar_component_clause,[],[f231])).

fof(f235,plain,
    ( ~ spl6_19
    | spl6_4 ),
    inference(avatar_split_clause,[],[f133,f87,f231])).

fof(f133,plain,
    ( sK2 = k2_zfmisc_1(sK0,sK1)
    | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f79,f72])).

fof(f72,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f55,f37])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f79,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | X1 = X2
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f51,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f53,f44])).

fof(f44,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f234,plain,
    ( ~ spl6_19
    | spl6_6 ),
    inference(avatar_split_clause,[],[f134,f96,f231])).

fof(f134,plain,
    ( k2_zfmisc_1(sK0,sK1) = sK3
    | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f79,f73])).

fof(f73,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f55,f40])).

fof(f226,plain,
    ( spl6_7
    | spl6_17 ),
    inference(avatar_split_clause,[],[f147,f212,f118])).

fof(f147,plain,
    ( v1_partfun1(sK2,sK0)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f146,f35])).

fof(f146,plain,
    ( ~ v1_funct_1(sK2)
    | v1_partfun1(sK2,sK0)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f143,f36])).

fof(f36,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f143,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | v1_partfun1(sK2,sK0)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f47,f37])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_partfun1(X2,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f225,plain,
    ( spl6_7
    | spl6_15 ),
    inference(avatar_split_clause,[],[f150,f203,f118])).

fof(f150,plain,
    ( v1_partfun1(sK3,sK0)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f149,f38])).

fof(f149,plain,
    ( ~ v1_funct_1(sK3)
    | v1_partfun1(sK3,sK0)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f144,f39])).

fof(f39,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f144,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3)
    | v1_partfun1(sK3,sK0)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f47,f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:31:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (29919)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.50  % (29915)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (29941)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.51  % (29916)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (29940)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.51  % (29916)Refutation not found, incomplete strategy% (29916)------------------------------
% 0.20/0.51  % (29916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (29916)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (29916)Memory used [KB]: 10746
% 0.20/0.51  % (29916)Time elapsed: 0.112 s
% 0.20/0.51  % (29916)------------------------------
% 0.20/0.51  % (29916)------------------------------
% 0.20/0.52  % (29917)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (29927)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (29922)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (29922)Refutation not found, incomplete strategy% (29922)------------------------------
% 0.20/0.52  % (29922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (29922)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (29922)Memory used [KB]: 10746
% 0.20/0.52  % (29922)Time elapsed: 0.105 s
% 0.20/0.52  % (29922)------------------------------
% 0.20/0.52  % (29922)------------------------------
% 0.20/0.52  % (29928)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (29926)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (29924)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (29920)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (29940)Refutation not found, incomplete strategy% (29940)------------------------------
% 0.20/0.53  % (29940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (29940)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (29940)Memory used [KB]: 10746
% 0.20/0.53  % (29940)Time elapsed: 0.116 s
% 0.20/0.53  % (29940)------------------------------
% 0.20/0.53  % (29940)------------------------------
% 0.20/0.53  % (29941)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f334,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f225,f226,f234,f235,f248,f263,f304,f306,f333])).
% 0.20/0.53  fof(f333,plain,(
% 0.20/0.53    ~spl6_4 | ~spl6_6 | spl6_11),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f332])).
% 0.20/0.53  fof(f332,plain,(
% 0.20/0.53    $false | (~spl6_4 | ~spl6_6 | spl6_11)),
% 0.20/0.53    inference(subsumption_resolution,[],[f331,f174])).
% 0.20/0.53  fof(f174,plain,(
% 0.20/0.53    sK2 != sK3 | spl6_11),
% 0.20/0.53    inference(avatar_component_clause,[],[f173])).
% 0.20/0.53  fof(f173,plain,(
% 0.20/0.53    spl6_11 <=> sK2 = sK3),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.20/0.53  fof(f331,plain,(
% 0.20/0.53    sK2 = sK3 | (~spl6_4 | ~spl6_6)),
% 0.20/0.53    inference(forward_demodulation,[],[f98,f89])).
% 0.20/0.53  fof(f89,plain,(
% 0.20/0.53    sK2 = k2_zfmisc_1(sK0,sK1) | ~spl6_4),
% 0.20/0.53    inference(avatar_component_clause,[],[f87])).
% 0.20/0.53  fof(f87,plain,(
% 0.20/0.53    spl6_4 <=> sK2 = k2_zfmisc_1(sK0,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.53  fof(f98,plain,(
% 0.20/0.53    k2_zfmisc_1(sK0,sK1) = sK3 | ~spl6_6),
% 0.20/0.53    inference(avatar_component_clause,[],[f96])).
% 0.20/0.53  fof(f96,plain,(
% 0.20/0.53    spl6_6 <=> k2_zfmisc_1(sK0,sK1) = sK3),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.53  fof(f306,plain,(
% 0.20/0.53    ~spl6_15 | spl6_16),
% 0.20/0.53    inference(avatar_split_clause,[],[f305,f207,f203])).
% 0.20/0.53  fof(f203,plain,(
% 0.20/0.53    spl6_15 <=> v1_partfun1(sK3,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.20/0.53  fof(f207,plain,(
% 0.20/0.53    spl6_16 <=> ! [X1] : (~r1_partfun1(X1,sK3) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | sK3 = X1 | ~v1_partfun1(X1,sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.20/0.53  fof(f305,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_partfun1(X0,sK3) | ~v1_partfun1(sK3,sK0) | ~v1_partfun1(X0,sK0) | sK3 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f281,f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    v1_funct_1(sK3)),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    (~r2_relset_1(sK0,sK1,sK2,sK3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f22,f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => (~r2_relset_1(sK0,sK1,sK2,sK3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f12,plain,(
% 0.20/0.53    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.53    inference(flattening,[],[f11])).
% 0.20/0.53  fof(f11,plain,(
% 0.20/0.53    ? [X0,X1,X2] : (? [X3] : (((~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.20/0.53    inference(negated_conjecture,[],[f9])).
% 0.20/0.53  fof(f9,conjecture,(
% 0.20/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).
% 0.20/0.53  fof(f281,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_partfun1(X0,sK3) | ~v1_partfun1(sK3,sK0) | ~v1_partfun1(X0,sK0) | sK3 = X0 | ~v1_funct_1(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0)) )),
% 0.20/0.53    inference(resolution,[],[f40,f57])).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | X2 = X3 | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.53    inference(flattening,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f304,plain,(
% 0.20/0.53    spl6_11 | ~spl6_16 | ~spl6_17),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f303])).
% 0.20/0.53  fof(f303,plain,(
% 0.20/0.53    $false | (spl6_11 | ~spl6_16 | ~spl6_17)),
% 0.20/0.53    inference(subsumption_resolution,[],[f302,f213])).
% 0.20/0.53  % (29939)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  fof(f213,plain,(
% 0.20/0.53    v1_partfun1(sK2,sK0) | ~spl6_17),
% 0.20/0.53    inference(avatar_component_clause,[],[f212])).
% 0.20/0.53  fof(f212,plain,(
% 0.20/0.53    spl6_17 <=> v1_partfun1(sK2,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.20/0.53  fof(f302,plain,(
% 0.20/0.53    ~v1_partfun1(sK2,sK0) | (spl6_11 | ~spl6_16)),
% 0.20/0.53    inference(subsumption_resolution,[],[f301,f174])).
% 0.20/0.53  fof(f301,plain,(
% 0.20/0.53    sK2 = sK3 | ~v1_partfun1(sK2,sK0) | ~spl6_16),
% 0.20/0.53    inference(subsumption_resolution,[],[f300,f41])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    r1_partfun1(sK2,sK3)),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f300,plain,(
% 0.20/0.53    ~r1_partfun1(sK2,sK3) | sK2 = sK3 | ~v1_partfun1(sK2,sK0) | ~spl6_16),
% 0.20/0.53    inference(subsumption_resolution,[],[f297,f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    v1_funct_1(sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f297,plain,(
% 0.20/0.53    ~v1_funct_1(sK2) | ~r1_partfun1(sK2,sK3) | sK2 = sK3 | ~v1_partfun1(sK2,sK0) | ~spl6_16),
% 0.20/0.53    inference(resolution,[],[f208,f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f208,plain,(
% 0.20/0.53    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X1) | ~r1_partfun1(X1,sK3) | sK3 = X1 | ~v1_partfun1(X1,sK0)) ) | ~spl6_16),
% 0.20/0.53    inference(avatar_component_clause,[],[f207])).
% 0.20/0.53  fof(f263,plain,(
% 0.20/0.53    ~spl6_11),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f262])).
% 0.20/0.53  fof(f262,plain,(
% 0.20/0.53    $false | ~spl6_11),
% 0.20/0.53    inference(subsumption_resolution,[],[f253,f140])).
% 0.20/0.53  fof(f140,plain,(
% 0.20/0.53    r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.20/0.53    inference(resolution,[],[f61,f37])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_relset_1(X1,X2,X0,X0)) )),
% 0.20/0.53    inference(condensation,[],[f58])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(flattening,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.20/0.53  fof(f253,plain,(
% 0.20/0.53    ~r2_relset_1(sK0,sK1,sK2,sK2) | ~spl6_11),
% 0.20/0.53    inference(backward_demodulation,[],[f43,f175])).
% 0.20/0.53  fof(f175,plain,(
% 0.20/0.53    sK2 = sK3 | ~spl6_11),
% 0.20/0.53    inference(avatar_component_clause,[],[f173])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f248,plain,(
% 0.20/0.53    ~spl6_7 | spl6_19),
% 0.20/0.53    inference(avatar_split_clause,[],[f245,f231,f118])).
% 0.20/0.53  fof(f118,plain,(
% 0.20/0.53    spl6_7 <=> v1_xboole_0(sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.53  fof(f231,plain,(
% 0.20/0.53    spl6_19 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.20/0.53  fof(f245,plain,(
% 0.20/0.53    ~v1_xboole_0(sK1) | spl6_19),
% 0.20/0.53    inference(resolution,[],[f233,f135])).
% 0.20/0.53  fof(f135,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X1,X0)) | ~v1_xboole_0(X0)) )),
% 0.20/0.53    inference(resolution,[],[f116,f59])).
% 0.20/0.53  fof(f59,plain,(
% 0.20/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.53    inference(equality_resolution,[],[f50])).
% 0.20/0.53  % (29936)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.53    inference(flattening,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.53  fof(f116,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X2,X1)) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.53    inference(resolution,[],[f48,f56])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.53    inference(nnf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.20/0.53  fof(f233,plain,(
% 0.20/0.53    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl6_19),
% 0.20/0.53    inference(avatar_component_clause,[],[f231])).
% 0.20/0.53  fof(f235,plain,(
% 0.20/0.53    ~spl6_19 | spl6_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f133,f87,f231])).
% 0.20/0.53  fof(f133,plain,(
% 0.20/0.53    sK2 = k2_zfmisc_1(sK0,sK1) | ~v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 0.20/0.53    inference(resolution,[],[f79,f72])).
% 0.20/0.53  fof(f72,plain,(
% 0.20/0.53    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.20/0.53    inference(resolution,[],[f55,f37])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f34])).
% 0.20/0.53  fof(f79,plain,(
% 0.20/0.53    ( ! [X2,X1] : (~r1_tarski(X1,X2) | X1 = X2 | ~v1_xboole_0(X2)) )),
% 0.20/0.53    inference(resolution,[],[f51,f75])).
% 0.20/0.53  fof(f75,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 0.20/0.53    inference(resolution,[],[f53,f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.53    inference(rectify,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.53    inference(nnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.53    inference(rectify,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.53    inference(nnf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f234,plain,(
% 0.20/0.53    ~spl6_19 | spl6_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f134,f96,f231])).
% 0.20/0.53  fof(f134,plain,(
% 0.20/0.53    k2_zfmisc_1(sK0,sK1) = sK3 | ~v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 0.20/0.53    inference(resolution,[],[f79,f73])).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 0.20/0.53    inference(resolution,[],[f55,f40])).
% 0.20/0.53  fof(f226,plain,(
% 0.20/0.53    spl6_7 | spl6_17),
% 0.20/0.53    inference(avatar_split_clause,[],[f147,f212,f118])).
% 0.20/0.53  fof(f147,plain,(
% 0.20/0.53    v1_partfun1(sK2,sK0) | v1_xboole_0(sK1)),
% 0.20/0.53    inference(subsumption_resolution,[],[f146,f35])).
% 0.20/0.53  fof(f146,plain,(
% 0.20/0.53    ~v1_funct_1(sK2) | v1_partfun1(sK2,sK0) | v1_xboole_0(sK1)),
% 0.20/0.53    inference(subsumption_resolution,[],[f143,f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f143,plain,(
% 0.20/0.53    ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | v1_partfun1(sK2,sK0) | v1_xboole_0(sK1)),
% 0.20/0.53    inference(resolution,[],[f47,f37])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_partfun1(X2,X0) | v1_xboole_0(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.53    inference(flattening,[],[f13])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.20/0.53  fof(f225,plain,(
% 0.20/0.53    spl6_7 | spl6_15),
% 0.20/0.53    inference(avatar_split_clause,[],[f150,f203,f118])).
% 0.20/0.53  fof(f150,plain,(
% 0.20/0.53    v1_partfun1(sK3,sK0) | v1_xboole_0(sK1)),
% 0.20/0.53    inference(subsumption_resolution,[],[f149,f38])).
% 0.20/0.53  fof(f149,plain,(
% 0.20/0.53    ~v1_funct_1(sK3) | v1_partfun1(sK3,sK0) | v1_xboole_0(sK1)),
% 0.20/0.53    inference(subsumption_resolution,[],[f144,f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f144,plain,(
% 0.20/0.53    ~v1_funct_2(sK3,sK0,sK1) | ~v1_funct_1(sK3) | v1_partfun1(sK3,sK0) | v1_xboole_0(sK1)),
% 0.20/0.53    inference(resolution,[],[f47,f40])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (29941)------------------------------
% 0.20/0.53  % (29941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (29941)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (29941)Memory used [KB]: 6396
% 0.20/0.53  % (29941)Time elapsed: 0.126 s
% 0.20/0.53  % (29941)------------------------------
% 0.20/0.53  % (29941)------------------------------
% 0.20/0.53  % (29942)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (29913)Success in time 0.174 s
%------------------------------------------------------------------------------
