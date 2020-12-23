%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:06 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 721 expanded)
%              Number of leaves         :   18 ( 221 expanded)
%              Depth                    :   28
%              Number of atoms          :  645 (4729 expanded)
%              Number of equality atoms :  157 (1002 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f709,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f116,f257,f295,f384,f509,f553,f621,f693,f708])).

fof(f708,plain,
    ( ~ spl8_15
    | ~ spl8_20 ),
    inference(avatar_contradiction_clause,[],[f707])).

fof(f707,plain,
    ( $false
    | ~ spl8_15
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f706,f56])).

fof(f56,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f706,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_15
    | ~ spl8_20 ),
    inference(resolution,[],[f695,f61])).

fof(f61,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK6(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f37,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
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

fof(f695,plain,
    ( r2_hidden(sK5(sK3,sK2),k1_xboole_0)
    | ~ spl8_15
    | ~ spl8_20 ),
    inference(forward_demodulation,[],[f263,f383])).

fof(f383,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f381])).

fof(f381,plain,
    ( spl8_20
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f263,plain,
    ( r2_hidden(sK5(sK3,sK2),sK0)
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl8_15
  <=> r2_hidden(sK5(sK3,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f693,plain,
    ( spl8_3
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(avatar_contradiction_clause,[],[f692])).

fof(f692,plain,
    ( $false
    | spl8_3
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f691,f662])).

fof(f662,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | spl8_3
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(forward_demodulation,[],[f661,f383])).

fof(f661,plain,
    ( sK0 != k1_relset_1(sK0,k1_xboole_0,sK2)
    | spl8_3
    | ~ spl8_4 ),
    inference(forward_demodulation,[],[f110,f115])).

fof(f115,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl8_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f110,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK2)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl8_3
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f691,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f680,f657])).

fof(f657,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(forward_demodulation,[],[f312,f383])).

fof(f312,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl8_4 ),
    inference(backward_demodulation,[],[f49,f115])).

fof(f49,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    & ! [X4] :
        ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
        | ~ r2_hidden(X4,sK0) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f30,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,X0) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK0,sK1,sK2,X3)
          & ! [X4] :
              ( k1_funct_1(X3,X4) = k1_funct_1(sK2,X4)
              | ~ r2_hidden(X4,sK0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X3,sK0,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK0,sK1,sK2,X3)
        & ! [X4] :
            ( k1_funct_1(X3,X4) = k1_funct_1(sK2,X4)
            | ~ r2_hidden(X4,sK0) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X3,sK0,sK1)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
      & ! [X4] :
          ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
          | ~ r2_hidden(X4,sK0) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( r2_hidden(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

fof(f680,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(resolution,[],[f656,f87])).

fof(f87,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f26])).

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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

% (21699)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% (21712)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f656,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(forward_demodulation,[],[f313,f383])).

fof(f313,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl8_4 ),
    inference(backward_demodulation,[],[f50,f115])).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f621,plain,
    ( spl8_3
    | ~ spl8_4
    | spl8_8
    | ~ spl8_19 ),
    inference(avatar_contradiction_clause,[],[f620])).

fof(f620,plain,
    ( $false
    | spl8_3
    | ~ spl8_4
    | spl8_8
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f619,f591])).

fof(f591,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl8_3
    | ~ spl8_4
    | spl8_8
    | ~ spl8_19 ),
    inference(forward_demodulation,[],[f590,f558])).

fof(f558,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_4
    | spl8_8
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f550,f519])).

fof(f519,plain,
    ( k1_xboole_0 != sK3
    | spl8_8
    | ~ spl8_19 ),
    inference(backward_demodulation,[],[f173,f379])).

fof(f379,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f377])).

fof(f377,plain,
    ( spl8_19
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f173,plain,
    ( sK2 != sK3
    | spl8_8 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl8_8
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f550,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f541,f314])).

fof(f314,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl8_4 ),
    inference(backward_demodulation,[],[f52,f115])).

fof(f52,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f541,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ spl8_4 ),
    inference(resolution,[],[f315,f85])).

fof(f85,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f315,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl8_4 ),
    inference(backward_demodulation,[],[f53,f115])).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f590,plain,
    ( sK0 != k1_relset_1(sK0,k1_xboole_0,k1_xboole_0)
    | spl8_3
    | ~ spl8_4
    | ~ spl8_19 ),
    inference(forward_demodulation,[],[f589,f115])).

fof(f589,plain,
    ( sK0 != k1_relset_1(sK0,sK1,k1_xboole_0)
    | spl8_3
    | ~ spl8_19 ),
    inference(forward_demodulation,[],[f110,f379])).

fof(f619,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl8_4
    | spl8_8
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f607,f574])).

fof(f574,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl8_4
    | spl8_8
    | ~ spl8_19 ),
    inference(backward_demodulation,[],[f522,f558])).

fof(f522,plain,
    ( v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl8_4
    | ~ spl8_19 ),
    inference(backward_demodulation,[],[f312,f379])).

fof(f607,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl8_4
    | spl8_8
    | ~ spl8_19 ),
    inference(resolution,[],[f575,f87])).

fof(f575,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl8_4
    | spl8_8
    | ~ spl8_19 ),
    inference(backward_demodulation,[],[f523,f558])).

fof(f523,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl8_4
    | ~ spl8_19 ),
    inference(backward_demodulation,[],[f313,f379])).

fof(f553,plain,
    ( ~ spl8_4
    | spl8_8
    | ~ spl8_19
    | spl8_20 ),
    inference(avatar_contradiction_clause,[],[f552])).

fof(f552,plain,
    ( $false
    | ~ spl8_4
    | spl8_8
    | ~ spl8_19
    | spl8_20 ),
    inference(subsumption_resolution,[],[f551,f519])).

fof(f551,plain,
    ( k1_xboole_0 = sK3
    | ~ spl8_4
    | spl8_20 ),
    inference(subsumption_resolution,[],[f550,f382])).

fof(f382,plain,
    ( k1_xboole_0 != sK0
    | spl8_20 ),
    inference(avatar_component_clause,[],[f381])).

fof(f509,plain,
    ( ~ spl8_3
    | ~ spl8_4
    | spl8_8
    | spl8_15
    | ~ spl8_20 ),
    inference(avatar_contradiction_clause,[],[f508])).

fof(f508,plain,
    ( $false
    | ~ spl8_3
    | ~ spl8_4
    | spl8_8
    | spl8_15
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f507,f119])).

fof(f119,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f53,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f507,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl8_3
    | ~ spl8_4
    | spl8_8
    | spl8_15
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f506,f51])).

fof(f51,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f506,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_3
    | ~ spl8_4
    | spl8_8
    | spl8_15
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f505,f173])).

fof(f505,plain,
    ( sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_3
    | ~ spl8_4
    | spl8_15
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f504,f390])).

fof(f390,plain,
    ( ~ r2_hidden(sK5(sK3,sK2),k1_xboole_0)
    | spl8_15
    | ~ spl8_20 ),
    inference(backward_demodulation,[],[f262,f383])).

fof(f262,plain,
    ( ~ r2_hidden(sK5(sK3,sK2),sK0)
    | spl8_15 ),
    inference(avatar_component_clause,[],[f261])).

fof(f504,plain,
    ( r2_hidden(sK5(sK3,sK2),k1_xboole_0)
    | sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(trivial_inequality_removal,[],[f503])).

fof(f503,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK5(sK3,sK2),k1_xboole_0)
    | sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(superposition,[],[f425,f467])).

fof(f467,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(backward_demodulation,[],[f400,f464])).

fof(f464,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f453,f394])).

fof(f394,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(backward_demodulation,[],[f314,f383])).

fof(f453,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(resolution,[],[f395,f87])).

fof(f395,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(backward_demodulation,[],[f315,f383])).

fof(f400,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl8_4
    | ~ spl8_20 ),
    inference(backward_demodulation,[],[f322,f383])).

fof(f322,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3)
    | ~ spl8_4 ),
    inference(backward_demodulation,[],[f120,f115])).

fof(f120,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f53,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f425,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_relat_1(X0)
        | r2_hidden(sK5(X0,sK2),k1_xboole_0)
        | sK2 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl8_3
    | ~ spl8_20 ),
    inference(forward_demodulation,[],[f388,f383])).

fof(f388,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_relat_1(X0)
        | r2_hidden(sK5(X0,sK2),sK0)
        | sK2 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl8_3
    | ~ spl8_20 ),
    inference(backward_demodulation,[],[f137,f383])).

fof(f137,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | r2_hidden(sK5(X0,sK2),sK0)
        | sK2 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl8_3 ),
    inference(inner_rewriting,[],[f136])).

fof(f136,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | r2_hidden(sK5(X0,sK2),k1_relat_1(X0))
        | sK2 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f135,f91])).

fof(f91,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f50,f71])).

fof(f135,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | r2_hidden(sK5(X0,sK2),k1_relat_1(X0))
        | sK2 = X0
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f133,f48])).

fof(f48,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f133,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | r2_hidden(sK5(X0,sK2),k1_relat_1(X0))
        | sK2 = X0
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl8_3 ),
    inference(superposition,[],[f59,f117])).

% (21710)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f117,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl8_3 ),
    inference(backward_demodulation,[],[f92,f111])).

fof(f111,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f92,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f50,f72])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != k1_relat_1(X1)
      | r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | X0 = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
            & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f19,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

fof(f384,plain,
    ( spl8_19
    | spl8_20
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f375,f113,f381,f377])).

fof(f375,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f366,f312])).

fof(f366,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl8_4 ),
    inference(resolution,[],[f313,f85])).

fof(f295,plain,(
    ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f294])).

fof(f294,plain,
    ( $false
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f281,f96])).

fof(f96,plain,(
    r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(resolution,[],[f50,f89])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f281,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl8_8 ),
    inference(backward_demodulation,[],[f55,f174])).

fof(f174,plain,
    ( sK2 = sK3
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f172])).

fof(f55,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f257,plain,
    ( ~ spl8_3
    | spl8_4
    | spl8_8 ),
    inference(avatar_contradiction_clause,[],[f256])).

fof(f256,plain,
    ( $false
    | ~ spl8_3
    | spl8_4
    | spl8_8 ),
    inference(subsumption_resolution,[],[f255,f117])).

fof(f255,plain,
    ( sK0 != k1_relat_1(sK2)
    | ~ spl8_3
    | spl8_4
    | spl8_8 ),
    inference(forward_demodulation,[],[f254,f128])).

fof(f128,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl8_4 ),
    inference(backward_demodulation,[],[f120,f127])).

fof(f127,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f126,f114])).

fof(f114,plain,
    ( k1_xboole_0 != sK1
    | spl8_4 ),
    inference(avatar_component_clause,[],[f113])).

fof(f126,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f121,f52])).

fof(f121,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f53,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f254,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ spl8_3
    | spl8_4
    | spl8_8 ),
    inference(subsumption_resolution,[],[f253,f119])).

fof(f253,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_3
    | spl8_4
    | spl8_8 ),
    inference(subsumption_resolution,[],[f252,f51])).

fof(f252,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_3
    | spl8_4
    | spl8_8 ),
    inference(subsumption_resolution,[],[f251,f91])).

fof(f251,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_3
    | spl8_4
    | spl8_8 ),
    inference(subsumption_resolution,[],[f250,f48])).

fof(f250,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_3
    | spl8_4
    | spl8_8 ),
    inference(subsumption_resolution,[],[f249,f173])).

fof(f249,plain,
    ( sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_3
    | spl8_4
    | spl8_8 ),
    inference(trivial_inequality_removal,[],[f248])).

fof(f248,plain,
    ( k1_funct_1(sK2,sK5(sK3,sK2)) != k1_funct_1(sK2,sK5(sK3,sK2))
    | sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_3
    | spl8_4
    | spl8_8 ),
    inference(superposition,[],[f60,f227])).

fof(f227,plain,
    ( k1_funct_1(sK2,sK5(sK3,sK2)) = k1_funct_1(sK3,sK5(sK3,sK2))
    | ~ spl8_3
    | spl8_4
    | spl8_8 ),
    inference(resolution,[],[f226,f54])).

fof(f54,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK0)
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f226,plain,
    ( r2_hidden(sK5(sK3,sK2),sK0)
    | ~ spl8_3
    | spl8_4
    | spl8_8 ),
    inference(subsumption_resolution,[],[f225,f119])).

fof(f225,plain,
    ( r2_hidden(sK5(sK3,sK2),sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl8_3
    | spl8_4
    | spl8_8 ),
    inference(subsumption_resolution,[],[f224,f51])).

fof(f224,plain,
    ( r2_hidden(sK5(sK3,sK2),sK0)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_3
    | spl8_4
    | spl8_8 ),
    inference(subsumption_resolution,[],[f223,f173])).

fof(f223,plain,
    ( r2_hidden(sK5(sK3,sK2),sK0)
    | sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_3
    | spl8_4 ),
    inference(trivial_inequality_removal,[],[f222])).

% (21709)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f222,plain,
    ( sK0 != sK0
    | r2_hidden(sK5(sK3,sK2),sK0)
    | sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_3
    | spl8_4 ),
    inference(superposition,[],[f137,f128])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
      | X0 = X1
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f116,plain,
    ( spl8_3
    | spl8_4 ),
    inference(avatar_split_clause,[],[f107,f113,f109])).

fof(f107,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f93,f49])).

fof(f93,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f50,f73])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:30:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (21692)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.50  % (21690)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (21708)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (21711)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (21687)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (21693)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (21688)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.25/0.52  % (21686)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.25/0.52  % (21700)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.25/0.52  % (21698)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.25/0.53  % (21703)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.25/0.53  % (21714)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.25/0.53  % (21705)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.25/0.53  % (21684)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.25/0.53  % (21695)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.25/0.53  % (21701)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.25/0.53  % (21706)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.25/0.53  % (21696)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.25/0.54  % (21685)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.25/0.54  % (21692)Refutation found. Thanks to Tanya!
% 1.25/0.54  % SZS status Theorem for theBenchmark
% 1.25/0.54  % (21697)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.25/0.54  % (21694)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.41/0.54  % (21707)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.41/0.54  % (21689)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.41/0.54  % SZS output start Proof for theBenchmark
% 1.41/0.54  fof(f709,plain,(
% 1.41/0.54    $false),
% 1.41/0.54    inference(avatar_sat_refutation,[],[f116,f257,f295,f384,f509,f553,f621,f693,f708])).
% 1.41/0.54  fof(f708,plain,(
% 1.41/0.54    ~spl8_15 | ~spl8_20),
% 1.41/0.54    inference(avatar_contradiction_clause,[],[f707])).
% 1.41/0.54  fof(f707,plain,(
% 1.41/0.54    $false | (~spl8_15 | ~spl8_20)),
% 1.41/0.54    inference(subsumption_resolution,[],[f706,f56])).
% 1.41/0.54  fof(f56,plain,(
% 1.41/0.54    v1_xboole_0(k1_xboole_0)),
% 1.41/0.54    inference(cnf_transformation,[],[f3])).
% 1.41/0.54  fof(f3,axiom,(
% 1.41/0.54    v1_xboole_0(k1_xboole_0)),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.41/0.54  fof(f706,plain,(
% 1.41/0.54    ~v1_xboole_0(k1_xboole_0) | (~spl8_15 | ~spl8_20)),
% 1.41/0.54    inference(resolution,[],[f695,f61])).
% 1.41/0.54  fof(f61,plain,(
% 1.41/0.54    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f39])).
% 1.41/0.54  fof(f39,plain,(
% 1.41/0.54    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK6(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.41/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f37,f38])).
% 1.41/0.54  fof(f38,plain,(
% 1.41/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 1.41/0.54    introduced(choice_axiom,[])).
% 1.41/0.54  fof(f37,plain,(
% 1.41/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.41/0.54    inference(rectify,[],[f36])).
% 1.41/0.54  fof(f36,plain,(
% 1.41/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.41/0.54    inference(nnf_transformation,[],[f1])).
% 1.41/0.54  fof(f1,axiom,(
% 1.41/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.41/0.54  fof(f695,plain,(
% 1.41/0.54    r2_hidden(sK5(sK3,sK2),k1_xboole_0) | (~spl8_15 | ~spl8_20)),
% 1.41/0.54    inference(forward_demodulation,[],[f263,f383])).
% 1.41/0.54  fof(f383,plain,(
% 1.41/0.54    k1_xboole_0 = sK0 | ~spl8_20),
% 1.41/0.54    inference(avatar_component_clause,[],[f381])).
% 1.41/0.54  fof(f381,plain,(
% 1.41/0.54    spl8_20 <=> k1_xboole_0 = sK0),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 1.41/0.54  fof(f263,plain,(
% 1.41/0.54    r2_hidden(sK5(sK3,sK2),sK0) | ~spl8_15),
% 1.41/0.54    inference(avatar_component_clause,[],[f261])).
% 1.41/0.54  fof(f261,plain,(
% 1.41/0.54    spl8_15 <=> r2_hidden(sK5(sK3,sK2),sK0)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 1.41/0.54  fof(f693,plain,(
% 1.41/0.54    spl8_3 | ~spl8_4 | ~spl8_20),
% 1.41/0.54    inference(avatar_contradiction_clause,[],[f692])).
% 1.41/0.54  fof(f692,plain,(
% 1.41/0.54    $false | (spl8_3 | ~spl8_4 | ~spl8_20)),
% 1.41/0.54    inference(subsumption_resolution,[],[f691,f662])).
% 1.41/0.54  fof(f662,plain,(
% 1.41/0.54    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (spl8_3 | ~spl8_4 | ~spl8_20)),
% 1.41/0.54    inference(forward_demodulation,[],[f661,f383])).
% 1.41/0.54  fof(f661,plain,(
% 1.41/0.54    sK0 != k1_relset_1(sK0,k1_xboole_0,sK2) | (spl8_3 | ~spl8_4)),
% 1.41/0.54    inference(forward_demodulation,[],[f110,f115])).
% 1.41/0.54  fof(f115,plain,(
% 1.41/0.54    k1_xboole_0 = sK1 | ~spl8_4),
% 1.41/0.54    inference(avatar_component_clause,[],[f113])).
% 1.41/0.54  fof(f113,plain,(
% 1.41/0.54    spl8_4 <=> k1_xboole_0 = sK1),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.41/0.54  fof(f110,plain,(
% 1.41/0.54    sK0 != k1_relset_1(sK0,sK1,sK2) | spl8_3),
% 1.41/0.54    inference(avatar_component_clause,[],[f109])).
% 1.41/0.54  fof(f109,plain,(
% 1.41/0.54    spl8_3 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.41/0.54  fof(f691,plain,(
% 1.41/0.54    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl8_4 | ~spl8_20)),
% 1.41/0.54    inference(subsumption_resolution,[],[f680,f657])).
% 1.41/0.54  fof(f657,plain,(
% 1.41/0.54    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl8_4 | ~spl8_20)),
% 1.41/0.54    inference(forward_demodulation,[],[f312,f383])).
% 1.41/0.54  fof(f312,plain,(
% 1.41/0.54    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl8_4),
% 1.41/0.54    inference(backward_demodulation,[],[f49,f115])).
% 1.41/0.54  fof(f49,plain,(
% 1.41/0.54    v1_funct_2(sK2,sK0,sK1)),
% 1.41/0.54    inference(cnf_transformation,[],[f31])).
% 1.41/0.54  fof(f31,plain,(
% 1.41/0.54    (~r2_relset_1(sK0,sK1,sK2,sK3) & ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.41/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f30,f29])).
% 1.41/0.54  fof(f29,plain,(
% 1.41/0.54    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.41/0.54    introduced(choice_axiom,[])).
% 1.41/0.54  fof(f30,plain,(
% 1.41/0.54    ? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => (~r2_relset_1(sK0,sK1,sK2,sK3) & ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.41/0.54    introduced(choice_axiom,[])).
% 1.41/0.54  fof(f16,plain,(
% 1.41/0.54    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.41/0.54    inference(flattening,[],[f15])).
% 1.41/0.54  fof(f15,plain,(
% 1.41/0.54    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.41/0.54    inference(ennf_transformation,[],[f14])).
% 1.41/0.54  fof(f14,negated_conjecture,(
% 1.41/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.41/0.54    inference(negated_conjecture,[],[f13])).
% 1.41/0.54  fof(f13,conjecture,(
% 1.41/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).
% 1.41/0.54  fof(f680,plain,(
% 1.41/0.54    ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl8_4 | ~spl8_20)),
% 1.41/0.54    inference(resolution,[],[f656,f87])).
% 1.41/0.54  fof(f87,plain,(
% 1.41/0.54    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) )),
% 1.41/0.54    inference(equality_resolution,[],[f74])).
% 1.41/0.54  fof(f74,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.41/0.54    inference(cnf_transformation,[],[f46])).
% 1.41/0.54  fof(f46,plain,(
% 1.41/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.54    inference(nnf_transformation,[],[f26])).
% 1.41/0.54  fof(f26,plain,(
% 1.41/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.54    inference(flattening,[],[f25])).
% 1.41/0.54  fof(f25,plain,(
% 1.41/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.54    inference(ennf_transformation,[],[f12])).
% 1.41/0.54  fof(f12,axiom,(
% 1.41/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.41/0.55  % (21699)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.41/0.55  % (21712)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.41/0.55  fof(f656,plain,(
% 1.41/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl8_4 | ~spl8_20)),
% 1.41/0.55    inference(forward_demodulation,[],[f313,f383])).
% 1.41/0.55  fof(f313,plain,(
% 1.41/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl8_4),
% 1.41/0.55    inference(backward_demodulation,[],[f50,f115])).
% 1.41/0.55  fof(f50,plain,(
% 1.41/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.41/0.55    inference(cnf_transformation,[],[f31])).
% 1.41/0.55  fof(f621,plain,(
% 1.41/0.55    spl8_3 | ~spl8_4 | spl8_8 | ~spl8_19),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f620])).
% 1.41/0.55  fof(f620,plain,(
% 1.41/0.55    $false | (spl8_3 | ~spl8_4 | spl8_8 | ~spl8_19)),
% 1.41/0.55    inference(subsumption_resolution,[],[f619,f591])).
% 1.41/0.55  fof(f591,plain,(
% 1.41/0.55    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl8_3 | ~spl8_4 | spl8_8 | ~spl8_19)),
% 1.41/0.55    inference(forward_demodulation,[],[f590,f558])).
% 1.41/0.55  fof(f558,plain,(
% 1.41/0.55    k1_xboole_0 = sK0 | (~spl8_4 | spl8_8 | ~spl8_19)),
% 1.41/0.55    inference(subsumption_resolution,[],[f550,f519])).
% 1.41/0.55  fof(f519,plain,(
% 1.41/0.55    k1_xboole_0 != sK3 | (spl8_8 | ~spl8_19)),
% 1.41/0.55    inference(backward_demodulation,[],[f173,f379])).
% 1.41/0.55  fof(f379,plain,(
% 1.41/0.55    k1_xboole_0 = sK2 | ~spl8_19),
% 1.41/0.55    inference(avatar_component_clause,[],[f377])).
% 1.41/0.55  fof(f377,plain,(
% 1.41/0.55    spl8_19 <=> k1_xboole_0 = sK2),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 1.41/0.55  fof(f173,plain,(
% 1.41/0.55    sK2 != sK3 | spl8_8),
% 1.41/0.55    inference(avatar_component_clause,[],[f172])).
% 1.41/0.55  fof(f172,plain,(
% 1.41/0.55    spl8_8 <=> sK2 = sK3),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.41/0.55  fof(f550,plain,(
% 1.41/0.55    k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | ~spl8_4),
% 1.41/0.55    inference(subsumption_resolution,[],[f541,f314])).
% 1.41/0.55  fof(f314,plain,(
% 1.41/0.55    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl8_4),
% 1.41/0.55    inference(backward_demodulation,[],[f52,f115])).
% 1.41/0.55  fof(f52,plain,(
% 1.41/0.55    v1_funct_2(sK3,sK0,sK1)),
% 1.41/0.55    inference(cnf_transformation,[],[f31])).
% 1.41/0.55  fof(f541,plain,(
% 1.41/0.55    ~v1_funct_2(sK3,sK0,k1_xboole_0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | ~spl8_4),
% 1.41/0.55    inference(resolution,[],[f315,f85])).
% 1.41/0.55  fof(f85,plain,(
% 1.41/0.55    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 1.41/0.55    inference(equality_resolution,[],[f77])).
% 1.41/0.55  fof(f77,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.41/0.55    inference(cnf_transformation,[],[f46])).
% 1.41/0.55  fof(f315,plain,(
% 1.41/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl8_4),
% 1.41/0.55    inference(backward_demodulation,[],[f53,f115])).
% 1.41/0.55  fof(f53,plain,(
% 1.41/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.41/0.55    inference(cnf_transformation,[],[f31])).
% 1.41/0.55  fof(f590,plain,(
% 1.41/0.55    sK0 != k1_relset_1(sK0,k1_xboole_0,k1_xboole_0) | (spl8_3 | ~spl8_4 | ~spl8_19)),
% 1.41/0.55    inference(forward_demodulation,[],[f589,f115])).
% 1.41/0.55  fof(f589,plain,(
% 1.41/0.55    sK0 != k1_relset_1(sK0,sK1,k1_xboole_0) | (spl8_3 | ~spl8_19)),
% 1.41/0.55    inference(forward_demodulation,[],[f110,f379])).
% 1.41/0.55  fof(f619,plain,(
% 1.41/0.55    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl8_4 | spl8_8 | ~spl8_19)),
% 1.41/0.55    inference(subsumption_resolution,[],[f607,f574])).
% 1.41/0.55  fof(f574,plain,(
% 1.41/0.55    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl8_4 | spl8_8 | ~spl8_19)),
% 1.41/0.55    inference(backward_demodulation,[],[f522,f558])).
% 1.41/0.55  fof(f522,plain,(
% 1.41/0.55    v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | (~spl8_4 | ~spl8_19)),
% 1.41/0.55    inference(backward_demodulation,[],[f312,f379])).
% 1.41/0.55  fof(f607,plain,(
% 1.41/0.55    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl8_4 | spl8_8 | ~spl8_19)),
% 1.41/0.55    inference(resolution,[],[f575,f87])).
% 1.41/0.55  fof(f575,plain,(
% 1.41/0.55    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl8_4 | spl8_8 | ~spl8_19)),
% 1.41/0.55    inference(backward_demodulation,[],[f523,f558])).
% 1.41/0.55  fof(f523,plain,(
% 1.41/0.55    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl8_4 | ~spl8_19)),
% 1.41/0.55    inference(backward_demodulation,[],[f313,f379])).
% 1.41/0.55  fof(f553,plain,(
% 1.41/0.55    ~spl8_4 | spl8_8 | ~spl8_19 | spl8_20),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f552])).
% 1.41/0.55  fof(f552,plain,(
% 1.41/0.55    $false | (~spl8_4 | spl8_8 | ~spl8_19 | spl8_20)),
% 1.41/0.55    inference(subsumption_resolution,[],[f551,f519])).
% 1.41/0.55  fof(f551,plain,(
% 1.41/0.55    k1_xboole_0 = sK3 | (~spl8_4 | spl8_20)),
% 1.41/0.55    inference(subsumption_resolution,[],[f550,f382])).
% 1.41/0.55  fof(f382,plain,(
% 1.41/0.55    k1_xboole_0 != sK0 | spl8_20),
% 1.41/0.55    inference(avatar_component_clause,[],[f381])).
% 1.41/0.55  fof(f509,plain,(
% 1.41/0.55    ~spl8_3 | ~spl8_4 | spl8_8 | spl8_15 | ~spl8_20),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f508])).
% 1.41/0.55  fof(f508,plain,(
% 1.41/0.55    $false | (~spl8_3 | ~spl8_4 | spl8_8 | spl8_15 | ~spl8_20)),
% 1.41/0.55    inference(subsumption_resolution,[],[f507,f119])).
% 1.41/0.55  fof(f119,plain,(
% 1.41/0.55    v1_relat_1(sK3)),
% 1.41/0.55    inference(resolution,[],[f53,f71])).
% 1.41/0.55  fof(f71,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f23])).
% 1.41/0.55  fof(f23,plain,(
% 1.41/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.55    inference(ennf_transformation,[],[f8])).
% 1.41/0.55  fof(f8,axiom,(
% 1.41/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.41/0.55  fof(f507,plain,(
% 1.41/0.55    ~v1_relat_1(sK3) | (~spl8_3 | ~spl8_4 | spl8_8 | spl8_15 | ~spl8_20)),
% 1.41/0.55    inference(subsumption_resolution,[],[f506,f51])).
% 1.41/0.55  fof(f51,plain,(
% 1.41/0.55    v1_funct_1(sK3)),
% 1.41/0.55    inference(cnf_transformation,[],[f31])).
% 1.41/0.55  fof(f506,plain,(
% 1.41/0.55    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl8_3 | ~spl8_4 | spl8_8 | spl8_15 | ~spl8_20)),
% 1.41/0.55    inference(subsumption_resolution,[],[f505,f173])).
% 1.41/0.55  fof(f505,plain,(
% 1.41/0.55    sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl8_3 | ~spl8_4 | spl8_15 | ~spl8_20)),
% 1.41/0.55    inference(subsumption_resolution,[],[f504,f390])).
% 1.41/0.55  fof(f390,plain,(
% 1.41/0.55    ~r2_hidden(sK5(sK3,sK2),k1_xboole_0) | (spl8_15 | ~spl8_20)),
% 1.41/0.55    inference(backward_demodulation,[],[f262,f383])).
% 1.41/0.55  fof(f262,plain,(
% 1.41/0.55    ~r2_hidden(sK5(sK3,sK2),sK0) | spl8_15),
% 1.41/0.55    inference(avatar_component_clause,[],[f261])).
% 1.41/0.55  fof(f504,plain,(
% 1.41/0.55    r2_hidden(sK5(sK3,sK2),k1_xboole_0) | sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl8_3 | ~spl8_4 | ~spl8_20)),
% 1.41/0.55    inference(trivial_inequality_removal,[],[f503])).
% 1.41/0.55  fof(f503,plain,(
% 1.41/0.55    k1_xboole_0 != k1_xboole_0 | r2_hidden(sK5(sK3,sK2),k1_xboole_0) | sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl8_3 | ~spl8_4 | ~spl8_20)),
% 1.41/0.55    inference(superposition,[],[f425,f467])).
% 1.41/0.55  fof(f467,plain,(
% 1.41/0.55    k1_xboole_0 = k1_relat_1(sK3) | (~spl8_4 | ~spl8_20)),
% 1.41/0.55    inference(backward_demodulation,[],[f400,f464])).
% 1.41/0.55  fof(f464,plain,(
% 1.41/0.55    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl8_4 | ~spl8_20)),
% 1.41/0.55    inference(subsumption_resolution,[],[f453,f394])).
% 1.41/0.55  fof(f394,plain,(
% 1.41/0.55    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl8_4 | ~spl8_20)),
% 1.41/0.55    inference(backward_demodulation,[],[f314,f383])).
% 1.41/0.55  fof(f453,plain,(
% 1.41/0.55    ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl8_4 | ~spl8_20)),
% 1.41/0.55    inference(resolution,[],[f395,f87])).
% 1.41/0.55  fof(f395,plain,(
% 1.41/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl8_4 | ~spl8_20)),
% 1.41/0.55    inference(backward_demodulation,[],[f315,f383])).
% 1.41/0.55  fof(f400,plain,(
% 1.41/0.55    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl8_4 | ~spl8_20)),
% 1.41/0.55    inference(backward_demodulation,[],[f322,f383])).
% 1.41/0.55  fof(f322,plain,(
% 1.41/0.55    k1_relat_1(sK3) = k1_relset_1(sK0,k1_xboole_0,sK3) | ~spl8_4),
% 1.41/0.55    inference(backward_demodulation,[],[f120,f115])).
% 1.41/0.55  fof(f120,plain,(
% 1.41/0.55    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.41/0.55    inference(resolution,[],[f53,f72])).
% 1.41/0.55  fof(f72,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f24])).
% 1.41/0.55  fof(f24,plain,(
% 1.41/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.55    inference(ennf_transformation,[],[f10])).
% 1.41/0.55  fof(f10,axiom,(
% 1.41/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.41/0.55  fof(f425,plain,(
% 1.41/0.55    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | r2_hidden(sK5(X0,sK2),k1_xboole_0) | sK2 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl8_3 | ~spl8_20)),
% 1.41/0.55    inference(forward_demodulation,[],[f388,f383])).
% 1.41/0.55  fof(f388,plain,(
% 1.41/0.55    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | r2_hidden(sK5(X0,sK2),sK0) | sK2 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl8_3 | ~spl8_20)),
% 1.41/0.55    inference(backward_demodulation,[],[f137,f383])).
% 1.41/0.55  fof(f137,plain,(
% 1.41/0.55    ( ! [X0] : (k1_relat_1(X0) != sK0 | r2_hidden(sK5(X0,sK2),sK0) | sK2 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl8_3),
% 1.41/0.55    inference(inner_rewriting,[],[f136])).
% 1.41/0.55  fof(f136,plain,(
% 1.41/0.55    ( ! [X0] : (k1_relat_1(X0) != sK0 | r2_hidden(sK5(X0,sK2),k1_relat_1(X0)) | sK2 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl8_3),
% 1.41/0.55    inference(subsumption_resolution,[],[f135,f91])).
% 1.41/0.55  fof(f91,plain,(
% 1.41/0.55    v1_relat_1(sK2)),
% 1.41/0.55    inference(resolution,[],[f50,f71])).
% 1.41/0.55  fof(f135,plain,(
% 1.41/0.55    ( ! [X0] : (k1_relat_1(X0) != sK0 | r2_hidden(sK5(X0,sK2),k1_relat_1(X0)) | sK2 = X0 | ~v1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl8_3),
% 1.41/0.55    inference(subsumption_resolution,[],[f133,f48])).
% 1.41/0.55  fof(f48,plain,(
% 1.41/0.55    v1_funct_1(sK2)),
% 1.41/0.55    inference(cnf_transformation,[],[f31])).
% 1.41/0.55  fof(f133,plain,(
% 1.41/0.55    ( ! [X0] : (k1_relat_1(X0) != sK0 | r2_hidden(sK5(X0,sK2),k1_relat_1(X0)) | sK2 = X0 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl8_3),
% 1.41/0.55    inference(superposition,[],[f59,f117])).
% 1.41/0.55  % (21710)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.41/0.55  fof(f117,plain,(
% 1.41/0.55    sK0 = k1_relat_1(sK2) | ~spl8_3),
% 1.41/0.55    inference(backward_demodulation,[],[f92,f111])).
% 1.41/0.55  fof(f111,plain,(
% 1.41/0.55    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl8_3),
% 1.41/0.55    inference(avatar_component_clause,[],[f109])).
% 1.41/0.55  fof(f92,plain,(
% 1.41/0.55    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 1.41/0.55    inference(resolution,[],[f50,f72])).
% 1.41/0.55  fof(f59,plain,(
% 1.41/0.55    ( ! [X0,X1] : (k1_relat_1(X0) != k1_relat_1(X1) | r2_hidden(sK5(X0,X1),k1_relat_1(X0)) | X0 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f35])).
% 1.41/0.55  fof(f35,plain,(
% 1.41/0.55    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.41/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f19,f34])).
% 1.41/0.55  fof(f34,plain,(
% 1.41/0.55    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))))),
% 1.41/0.55    introduced(choice_axiom,[])).
% 1.41/0.55  fof(f19,plain,(
% 1.41/0.55    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.41/0.55    inference(flattening,[],[f18])).
% 1.41/0.55  fof(f18,plain,(
% 1.41/0.55    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.41/0.55    inference(ennf_transformation,[],[f7])).
% 1.41/0.55  fof(f7,axiom,(
% 1.41/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).
% 1.41/0.55  fof(f384,plain,(
% 1.41/0.55    spl8_19 | spl8_20 | ~spl8_4),
% 1.41/0.55    inference(avatar_split_clause,[],[f375,f113,f381,f377])).
% 1.41/0.55  fof(f375,plain,(
% 1.41/0.55    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~spl8_4),
% 1.41/0.55    inference(subsumption_resolution,[],[f366,f312])).
% 1.41/0.55  fof(f366,plain,(
% 1.41/0.55    ~v1_funct_2(sK2,sK0,k1_xboole_0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~spl8_4),
% 1.41/0.55    inference(resolution,[],[f313,f85])).
% 1.41/0.55  fof(f295,plain,(
% 1.41/0.55    ~spl8_8),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f294])).
% 1.41/0.55  fof(f294,plain,(
% 1.41/0.55    $false | ~spl8_8),
% 1.41/0.55    inference(subsumption_resolution,[],[f281,f96])).
% 1.41/0.55  fof(f96,plain,(
% 1.41/0.55    r2_relset_1(sK0,sK1,sK2,sK2)),
% 1.41/0.55    inference(resolution,[],[f50,f89])).
% 1.41/0.55  fof(f89,plain,(
% 1.41/0.55    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.41/0.55    inference(duplicate_literal_removal,[],[f88])).
% 1.41/0.55  fof(f88,plain,(
% 1.41/0.55    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.41/0.55    inference(equality_resolution,[],[f80])).
% 1.41/0.55  fof(f80,plain,(
% 1.41/0.55    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.41/0.55    inference(cnf_transformation,[],[f47])).
% 1.41/0.55  fof(f47,plain,(
% 1.41/0.55    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.55    inference(nnf_transformation,[],[f28])).
% 1.41/0.55  fof(f28,plain,(
% 1.41/0.55    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.55    inference(flattening,[],[f27])).
% 1.41/0.55  fof(f27,plain,(
% 1.41/0.55    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.41/0.55    inference(ennf_transformation,[],[f11])).
% 1.41/0.55  fof(f11,axiom,(
% 1.41/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.41/0.55  fof(f281,plain,(
% 1.41/0.55    ~r2_relset_1(sK0,sK1,sK2,sK2) | ~spl8_8),
% 1.41/0.55    inference(backward_demodulation,[],[f55,f174])).
% 1.41/0.55  fof(f174,plain,(
% 1.41/0.55    sK2 = sK3 | ~spl8_8),
% 1.41/0.55    inference(avatar_component_clause,[],[f172])).
% 1.41/0.55  fof(f55,plain,(
% 1.41/0.55    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 1.41/0.55    inference(cnf_transformation,[],[f31])).
% 1.41/0.55  fof(f257,plain,(
% 1.41/0.55    ~spl8_3 | spl8_4 | spl8_8),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f256])).
% 1.41/0.55  fof(f256,plain,(
% 1.41/0.55    $false | (~spl8_3 | spl8_4 | spl8_8)),
% 1.41/0.55    inference(subsumption_resolution,[],[f255,f117])).
% 1.41/0.55  fof(f255,plain,(
% 1.41/0.55    sK0 != k1_relat_1(sK2) | (~spl8_3 | spl8_4 | spl8_8)),
% 1.41/0.55    inference(forward_demodulation,[],[f254,f128])).
% 1.41/0.55  fof(f128,plain,(
% 1.41/0.55    sK0 = k1_relat_1(sK3) | spl8_4),
% 1.41/0.55    inference(backward_demodulation,[],[f120,f127])).
% 1.41/0.55  fof(f127,plain,(
% 1.41/0.55    sK0 = k1_relset_1(sK0,sK1,sK3) | spl8_4),
% 1.41/0.55    inference(subsumption_resolution,[],[f126,f114])).
% 1.41/0.55  fof(f114,plain,(
% 1.41/0.55    k1_xboole_0 != sK1 | spl8_4),
% 1.41/0.55    inference(avatar_component_clause,[],[f113])).
% 1.41/0.55  fof(f126,plain,(
% 1.41/0.55    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.41/0.55    inference(subsumption_resolution,[],[f121,f52])).
% 1.41/0.55  fof(f121,plain,(
% 1.41/0.55    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.41/0.55    inference(resolution,[],[f53,f73])).
% 1.41/0.55  fof(f73,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.41/0.55    inference(cnf_transformation,[],[f46])).
% 1.41/0.55  fof(f254,plain,(
% 1.41/0.55    k1_relat_1(sK2) != k1_relat_1(sK3) | (~spl8_3 | spl8_4 | spl8_8)),
% 1.41/0.55    inference(subsumption_resolution,[],[f253,f119])).
% 1.41/0.55  fof(f253,plain,(
% 1.41/0.55    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | (~spl8_3 | spl8_4 | spl8_8)),
% 1.41/0.55    inference(subsumption_resolution,[],[f252,f51])).
% 1.41/0.55  fof(f252,plain,(
% 1.41/0.55    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl8_3 | spl8_4 | spl8_8)),
% 1.41/0.55    inference(subsumption_resolution,[],[f251,f91])).
% 1.41/0.55  fof(f251,plain,(
% 1.41/0.55    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl8_3 | spl8_4 | spl8_8)),
% 1.41/0.55    inference(subsumption_resolution,[],[f250,f48])).
% 1.41/0.55  fof(f250,plain,(
% 1.41/0.55    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl8_3 | spl8_4 | spl8_8)),
% 1.41/0.55    inference(subsumption_resolution,[],[f249,f173])).
% 1.41/0.55  fof(f249,plain,(
% 1.41/0.55    sK2 = sK3 | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl8_3 | spl8_4 | spl8_8)),
% 1.41/0.55    inference(trivial_inequality_removal,[],[f248])).
% 1.41/0.55  fof(f248,plain,(
% 1.41/0.55    k1_funct_1(sK2,sK5(sK3,sK2)) != k1_funct_1(sK2,sK5(sK3,sK2)) | sK2 = sK3 | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl8_3 | spl8_4 | spl8_8)),
% 1.41/0.55    inference(superposition,[],[f60,f227])).
% 1.41/0.55  fof(f227,plain,(
% 1.41/0.55    k1_funct_1(sK2,sK5(sK3,sK2)) = k1_funct_1(sK3,sK5(sK3,sK2)) | (~spl8_3 | spl8_4 | spl8_8)),
% 1.41/0.55    inference(resolution,[],[f226,f54])).
% 1.41/0.55  fof(f54,plain,(
% 1.41/0.55    ( ! [X4] : (~r2_hidden(X4,sK0) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f31])).
% 1.41/0.55  fof(f226,plain,(
% 1.41/0.55    r2_hidden(sK5(sK3,sK2),sK0) | (~spl8_3 | spl8_4 | spl8_8)),
% 1.41/0.55    inference(subsumption_resolution,[],[f225,f119])).
% 1.41/0.55  fof(f225,plain,(
% 1.41/0.55    r2_hidden(sK5(sK3,sK2),sK0) | ~v1_relat_1(sK3) | (~spl8_3 | spl8_4 | spl8_8)),
% 1.41/0.55    inference(subsumption_resolution,[],[f224,f51])).
% 1.41/0.55  fof(f224,plain,(
% 1.41/0.55    r2_hidden(sK5(sK3,sK2),sK0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl8_3 | spl8_4 | spl8_8)),
% 1.41/0.55    inference(subsumption_resolution,[],[f223,f173])).
% 1.41/0.55  fof(f223,plain,(
% 1.41/0.55    r2_hidden(sK5(sK3,sK2),sK0) | sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl8_3 | spl8_4)),
% 1.41/0.55    inference(trivial_inequality_removal,[],[f222])).
% 1.41/0.55  % (21709)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.41/0.55  fof(f222,plain,(
% 1.41/0.55    sK0 != sK0 | r2_hidden(sK5(sK3,sK2),sK0) | sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl8_3 | spl8_4)),
% 1.41/0.55    inference(superposition,[],[f137,f128])).
% 1.41/0.55  fof(f60,plain,(
% 1.41/0.55    ( ! [X0,X1] : (k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1)) | X0 = X1 | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f35])).
% 1.41/0.55  fof(f116,plain,(
% 1.41/0.55    spl8_3 | spl8_4),
% 1.41/0.55    inference(avatar_split_clause,[],[f107,f113,f109])).
% 1.41/0.55  fof(f107,plain,(
% 1.41/0.55    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.41/0.55    inference(subsumption_resolution,[],[f93,f49])).
% 1.41/0.55  fof(f93,plain,(
% 1.41/0.55    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.41/0.55    inference(resolution,[],[f50,f73])).
% 1.41/0.55  % SZS output end Proof for theBenchmark
% 1.41/0.55  % (21692)------------------------------
% 1.41/0.55  % (21692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (21692)Termination reason: Refutation
% 1.41/0.55  
% 1.41/0.55  % (21692)Memory used [KB]: 10874
% 1.41/0.55  % (21692)Time elapsed: 0.120 s
% 1.41/0.55  % (21692)------------------------------
% 1.41/0.55  % (21692)------------------------------
% 1.41/0.55  % (21683)Success in time 0.191 s
%------------------------------------------------------------------------------
