%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 237 expanded)
%              Number of leaves         :   35 ( 106 expanded)
%              Depth                    :   13
%              Number of atoms          :  455 (1097 expanded)
%              Number of equality atoms :   64 (  86 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f328,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f80,f84,f88,f92,f96,f100,f105,f116,f127,f156,f163,f188,f197,f198,f205,f214,f254,f321,f327])).

fof(f327,plain,
    ( ~ spl5_26
    | spl5_12
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f325,f319,f125,f225])).

fof(f225,plain,
    ( spl5_26
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f125,plain,
    ( spl5_12
  <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f319,plain,
    ( spl5_40
  <=> k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f325,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_40 ),
    inference(superposition,[],[f48,f320])).

fof(f320,plain,
    ( k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3)
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f319])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f321,plain,
    ( spl5_40
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f317,f225,f319])).

fof(f317,plain,
    ( k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3)
    | ~ spl5_26 ),
    inference(resolution,[],[f226,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f226,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f225])).

fof(f254,plain,
    ( spl5_26
    | ~ spl5_23
    | ~ spl5_24
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f253,f212,f203,f195,f225])).

fof(f195,plain,
    ( spl5_23
  <=> ! [X0] :
        ( r2_hidden(sK4(sK1,X0,sK3),sK1)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f203,plain,
    ( spl5_24
  <=> ! [X0] :
        ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f212,plain,
    ( spl5_25
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f253,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_23
    | ~ spl5_24
    | ~ spl5_25 ),
    inference(duplicate_literal_removal,[],[f251])).

fof(f251,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_23
    | ~ spl5_24
    | ~ spl5_25 ),
    inference(resolution,[],[f219,f204])).

fof(f204,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) )
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f203])).

fof(f219,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),sK0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) )
    | ~ spl5_23
    | ~ spl5_25 ),
    inference(resolution,[],[f218,f196])).

fof(f196,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK1,X0,sK3),sK1)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) )
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f195])).

fof(f218,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(k1_funct_1(sK3,X0),sK0) )
    | ~ spl5_25 ),
    inference(duplicate_literal_removal,[],[f217])).

fof(f217,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),sK0)
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl5_25 ),
    inference(resolution,[],[f216,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f216,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | r2_hidden(k1_funct_1(sK3,X0),sK0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl5_25 ),
    inference(superposition,[],[f40,f215])).

fof(f215,plain,
    ( ! [X0] :
        ( k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl5_25 ),
    inference(resolution,[],[f213,f43])).

fof(f213,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) )
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f212])).

fof(f40,plain,(
    ! [X4] :
      ( r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0)
      | ~ m1_subset_1(X4,sK1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)
    & ! [X4] :
        ( r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0)
        | ~ m1_subset_1(X4,sK1) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK2)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f30,f29,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
                & ! [X4] :
                    ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                    | ~ m1_subset_1(X4,X1) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(X3,X1,X2)
                & v1_funct_1(X3) )
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(sK1,X2,X3),sK0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(sK1,X2,X3,X4),sK0)
                  | ~ m1_subset_1(X4,sK1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
              & v1_funct_2(X3,sK1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

% (3918)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% (3908)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f29,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k2_relset_1(sK1,X2,X3),sK0)
            & ! [X4] :
                ( r2_hidden(k3_funct_2(sK1,X2,X3,X4),sK0)
                | ~ m1_subset_1(X4,sK1) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
            & v1_funct_2(X3,sK1,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k2_relset_1(sK1,sK2,X3),sK0)
          & ! [X4] :
              ( r2_hidden(k3_funct_2(sK1,sK2,X3,X4),sK0)
              | ~ m1_subset_1(X4,sK1) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X3,sK1,sK2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,X3),sK0)
        & ! [X4] :
            ( r2_hidden(k3_funct_2(sK1,sK2,X3,X4),sK0)
            | ~ m1_subset_1(X4,sK1) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        & v1_funct_2(X3,sK1,sK2)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)
      & ! [X4] :
          ( r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0)
          | ~ m1_subset_1(X4,sK1) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_2(X3,X1,X2)
                  & v1_funct_1(X3) )
               => ( ! [X4] :
                      ( m1_subset_1(X4,X1)
                     => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) )
                 => r1_tarski(k2_relset_1(X1,X2,X3),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(X3,X1,X2)
                & v1_funct_1(X3) )
             => ( ! [X4] :
                    ( m1_subset_1(X4,X1)
                   => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) )
               => r1_tarski(k2_relset_1(X1,X2,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_funct_2)).

fof(f214,plain,
    ( spl5_6
    | spl5_25
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f209,f86,f82,f78,f212,f94])).

fof(f94,plain,
    ( spl5_6
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f78,plain,
    ( spl5_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f82,plain,
    ( spl5_3
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f86,plain,
    ( spl5_4
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f209,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0)
        | v1_xboole_0(sK1) )
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(resolution,[],[f208,f83])).

fof(f83,plain,
    ( v1_funct_2(sK3,sK1,sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f208,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(sK3,X1,X2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ m1_subset_1(X0,X1)
        | k3_funct_2(X1,X2,sK3,X0) = k1_funct_1(sK3,X0)
        | v1_xboole_0(X1) )
    | ~ spl5_4 ),
    inference(resolution,[],[f61,f87])).

fof(f87,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

% (3911)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f205,plain,
    ( ~ spl5_18
    | spl5_24
    | ~ spl5_4
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f201,f160,f86,f203,f168])).

fof(f168,plain,
    ( spl5_18
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f160,plain,
    ( spl5_17
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f201,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),X0)
        | ~ v1_relat_1(sK3) )
    | ~ spl5_4
    | ~ spl5_17 ),
    inference(forward_demodulation,[],[f200,f161])).

fof(f161,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f160])).

fof(f200,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))
        | ~ v1_relat_1(sK3) )
    | ~ spl5_4
    | ~ spl5_17 ),
    inference(forward_demodulation,[],[f199,f161])).

fof(f199,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK3,sK4(k1_relat_1(sK3),X0,sK3)),X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))
        | ~ v1_relat_1(sK3) )
    | ~ spl5_4 ),
    inference(resolution,[],[f67,f87])).

fof(f67,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k1_funct_1(X2,sK4(k1_relat_1(X2),X1,X2)),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ( ~ r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1)
        & r2_hidden(sK4(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1)
        & r2_hidden(sK4(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

fof(f198,plain,
    ( k1_xboole_0 != sK2
    | ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f197,plain,
    ( ~ spl5_18
    | ~ spl5_4
    | spl5_23
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f193,f160,f195,f86,f168])).

fof(f193,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK1,X0,sK3),sK1)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl5_17 ),
    inference(superposition,[],[f68,f161])).

fof(f68,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK4(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK4(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f188,plain,
    ( ~ spl5_2
    | spl5_18 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | ~ spl5_2
    | spl5_18 ),
    inference(subsumption_resolution,[],[f79,f186])).

fof(f186,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl5_18 ),
    inference(resolution,[],[f169,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f169,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_18 ),
    inference(avatar_component_clause,[],[f168])).

fof(f79,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f163,plain,
    ( ~ spl5_2
    | spl5_17
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f158,f154,f160,f78])).

fof(f154,plain,
    ( spl5_16
  <=> sK1 = k1_relset_1(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f158,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_16 ),
    inference(superposition,[],[f46,f155])).

fof(f155,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f154])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f156,plain,
    ( ~ spl5_2
    | spl5_15
    | spl5_16
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f147,f82,f154,f151,f78])).

fof(f151,plain,
    ( spl5_15
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f147,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_3 ),
    inference(resolution,[],[f49,f83])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f8])).

% (3918)Refutation not found, incomplete strategy% (3918)------------------------------
% (3918)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3918)Termination reason: Refutation not found, incomplete strategy

% (3918)Memory used [KB]: 6140
% (3918)Time elapsed: 0.066 s
% (3918)------------------------------
% (3918)------------------------------
% (3912)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% (3909)Refutation not found, incomplete strategy% (3909)------------------------------
% (3909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3909)Termination reason: Refutation not found, incomplete strategy

% (3909)Memory used [KB]: 10618
% (3909)Time elapsed: 0.073 s
% (3909)------------------------------
% (3909)------------------------------
% (3925)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% (3919)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% (3910)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% (3919)Refutation not found, incomplete strategy% (3919)------------------------------
% (3919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3919)Termination reason: Refutation not found, incomplete strategy

% (3919)Memory used [KB]: 10618
% (3919)Time elapsed: 0.080 s
% (3919)------------------------------
% (3919)------------------------------
fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f127,plain,
    ( ~ spl5_12
    | spl5_8
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f118,f114,f103,f125])).

fof(f103,plain,
    ( spl5_8
  <=> m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f114,plain,
    ( spl5_10
  <=> k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f118,plain,
    ( ~ m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK0))
    | spl5_8
    | ~ spl5_10 ),
    inference(superposition,[],[f104,f115])).

fof(f115,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f114])).

fof(f104,plain,
    ( ~ m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK0))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f103])).

fof(f116,plain,
    ( spl5_10
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f111,f78,f114])).

fof(f111,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)
    | ~ spl5_2 ),
    inference(resolution,[],[f47,f79])).

fof(f105,plain,
    ( ~ spl5_8
    | spl5_1 ),
    inference(avatar_split_clause,[],[f101,f74,f103])).

fof(f74,plain,
    ( spl5_1
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f101,plain,
    ( ~ m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK0))
    | spl5_1 ),
    inference(resolution,[],[f44,f75])).

fof(f75,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f100,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f42,f98])).

fof(f98,plain,
    ( spl5_7
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f42,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f96,plain,(
    ~ spl5_6 ),
    inference(avatar_split_clause,[],[f35,f94])).

fof(f35,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f92,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f36,f90])).

fof(f90,plain,
    ( spl5_5
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f36,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f88,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f37,f86])).

fof(f37,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f84,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f38,f82])).

fof(f38,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f80,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f39,f78])).

fof(f39,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f31])).

fof(f76,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f41,f74])).

fof(f41,plain,(
    ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:59:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.46  % (3914)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (3926)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.47  % (3914)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (3909)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (3922)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % (3913)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f328,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f76,f80,f84,f88,f92,f96,f100,f105,f116,f127,f156,f163,f188,f197,f198,f205,f214,f254,f321,f327])).
% 0.20/0.47  fof(f327,plain,(
% 0.20/0.47    ~spl5_26 | spl5_12 | ~spl5_40),
% 0.20/0.47    inference(avatar_split_clause,[],[f325,f319,f125,f225])).
% 0.20/0.47  fof(f225,plain,(
% 0.20/0.47    spl5_26 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.20/0.47  fof(f125,plain,(
% 0.20/0.47    spl5_12 <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.20/0.47  fof(f319,plain,(
% 0.20/0.47    spl5_40 <=> k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 0.20/0.47  fof(f325,plain,(
% 0.20/0.47    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl5_40),
% 0.20/0.47    inference(superposition,[],[f48,f320])).
% 0.20/0.47  fof(f320,plain,(
% 0.20/0.47    k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3) | ~spl5_40),
% 0.20/0.47    inference(avatar_component_clause,[],[f319])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.20/0.47  fof(f321,plain,(
% 0.20/0.47    spl5_40 | ~spl5_26),
% 0.20/0.47    inference(avatar_split_clause,[],[f317,f225,f319])).
% 0.20/0.47  fof(f317,plain,(
% 0.20/0.47    k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3) | ~spl5_26),
% 0.20/0.47    inference(resolution,[],[f226,f47])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.47  fof(f226,plain,(
% 0.20/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl5_26),
% 0.20/0.47    inference(avatar_component_clause,[],[f225])).
% 0.20/0.47  fof(f254,plain,(
% 0.20/0.47    spl5_26 | ~spl5_23 | ~spl5_24 | ~spl5_25),
% 0.20/0.47    inference(avatar_split_clause,[],[f253,f212,f203,f195,f225])).
% 0.20/0.47  fof(f195,plain,(
% 0.20/0.47    spl5_23 <=> ! [X0] : (r2_hidden(sK4(sK1,X0,sK3),sK1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.20/0.47  fof(f203,plain,(
% 0.20/0.47    spl5_24 <=> ! [X0] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.20/0.47  fof(f212,plain,(
% 0.20/0.47    spl5_25 <=> ! [X0] : (~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.20/0.47  fof(f253,plain,(
% 0.20/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl5_23 | ~spl5_24 | ~spl5_25)),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f251])).
% 0.20/0.47  fof(f251,plain,(
% 0.20/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl5_23 | ~spl5_24 | ~spl5_25)),
% 0.20/0.47    inference(resolution,[],[f219,f204])).
% 0.20/0.47  fof(f204,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | ~spl5_24),
% 0.20/0.47    inference(avatar_component_clause,[],[f203])).
% 0.20/0.47  fof(f219,plain,(
% 0.20/0.47    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),sK0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | (~spl5_23 | ~spl5_25)),
% 0.20/0.47    inference(resolution,[],[f218,f196])).
% 0.20/0.47  fof(f196,plain,(
% 0.20/0.47    ( ! [X0] : (r2_hidden(sK4(sK1,X0,sK3),sK1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | ~spl5_23),
% 0.20/0.47    inference(avatar_component_clause,[],[f195])).
% 0.20/0.47  fof(f218,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(k1_funct_1(sK3,X0),sK0)) ) | ~spl5_25),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f217])).
% 0.20/0.47  fof(f217,plain,(
% 0.20/0.47    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),sK0) | ~r2_hidden(X0,sK1) | ~r2_hidden(X0,sK1)) ) | ~spl5_25),
% 0.20/0.47    inference(resolution,[],[f216,f43])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.47  fof(f216,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(X0,sK1) | r2_hidden(k1_funct_1(sK3,X0),sK0) | ~r2_hidden(X0,sK1)) ) | ~spl5_25),
% 0.20/0.47    inference(superposition,[],[f40,f215])).
% 0.20/0.47  fof(f215,plain,(
% 0.20/0.47    ( ! [X0] : (k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) | ~r2_hidden(X0,sK1)) ) | ~spl5_25),
% 0.20/0.47    inference(resolution,[],[f213,f43])).
% 0.20/0.47  fof(f213,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0)) ) | ~spl5_25),
% 0.20/0.47    inference(avatar_component_clause,[],[f212])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X4] : (r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0) | ~m1_subset_1(X4,sK1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ((~r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f30,f29,f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK1,X2,X3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,X2,X3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) & v1_funct_2(X3,sK1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  % (3918)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.47  % (3908)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK1,X2,X3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,X2,X3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) & v1_funct_2(X3,sK1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (~r1_tarski(k2_relset_1(sK1,sK2,X3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,sK2,X3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & ~v1_xboole_0(sK2))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ? [X3] : (~r1_tarski(k2_relset_1(sK1,sK2,X3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,sK2,X3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) => (~r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 0.20/0.47    inference(flattening,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 0.20/0.47    inference(negated_conjecture,[],[f11])).
% 0.20/0.47  fof(f11,conjecture,(
% 0.20/0.47    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_funct_2)).
% 0.20/0.47  fof(f214,plain,(
% 0.20/0.47    spl5_6 | spl5_25 | ~spl5_2 | ~spl5_3 | ~spl5_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f209,f86,f82,f78,f212,f94])).
% 0.20/0.47  fof(f94,plain,(
% 0.20/0.47    spl5_6 <=> v1_xboole_0(sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    spl5_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.48  fof(f82,plain,(
% 0.20/0.48    spl5_3 <=> v1_funct_2(sK3,sK1,sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.48  fof(f86,plain,(
% 0.20/0.48    spl5_4 <=> v1_funct_1(sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.48  fof(f209,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK2,sK3,X0) = k1_funct_1(sK3,X0) | v1_xboole_0(sK1)) ) | (~spl5_3 | ~spl5_4)),
% 0.20/0.48    inference(resolution,[],[f208,f83])).
% 0.20/0.48  fof(f83,plain,(
% 0.20/0.48    v1_funct_2(sK3,sK1,sK2) | ~spl5_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f82])).
% 0.20/0.48  fof(f208,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_funct_2(sK3,X1,X2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X0,X1) | k3_funct_2(X1,X2,sK3,X0) = k1_funct_1(sK3,X0) | v1_xboole_0(X1)) ) | ~spl5_4),
% 0.20/0.48    inference(resolution,[],[f61,f87])).
% 0.20/0.48  fof(f87,plain,(
% 0.20/0.48    v1_funct_1(sK3) | ~spl5_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f86])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | v1_xboole_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.20/0.48    inference(flattening,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  % (3911)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.20/0.48  fof(f205,plain,(
% 0.20/0.48    ~spl5_18 | spl5_24 | ~spl5_4 | ~spl5_17),
% 0.20/0.48    inference(avatar_split_clause,[],[f201,f160,f86,f203,f168])).
% 0.20/0.48  fof(f168,plain,(
% 0.20/0.48    spl5_18 <=> v1_relat_1(sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.20/0.48  fof(f160,plain,(
% 0.20/0.48    spl5_17 <=> sK1 = k1_relat_1(sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.20/0.48  fof(f201,plain,(
% 0.20/0.48    ( ! [X0] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),X0) | ~v1_relat_1(sK3)) ) | (~spl5_4 | ~spl5_17)),
% 0.20/0.48    inference(forward_demodulation,[],[f200,f161])).
% 0.20/0.48  fof(f161,plain,(
% 0.20/0.48    sK1 = k1_relat_1(sK3) | ~spl5_17),
% 0.20/0.48    inference(avatar_component_clause,[],[f160])).
% 0.20/0.48  fof(f200,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) | ~v1_relat_1(sK3)) ) | (~spl5_4 | ~spl5_17)),
% 0.20/0.48    inference(forward_demodulation,[],[f199,f161])).
% 0.20/0.48  fof(f199,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(k1_funct_1(sK3,sK4(k1_relat_1(sK3),X0,sK3)),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) | ~v1_relat_1(sK3)) ) | ~spl5_4),
% 0.20/0.48    inference(resolution,[],[f67,f87])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    ( ! [X2,X1] : (~v1_funct_1(X2) | ~r2_hidden(k1_funct_1(X2,sK4(k1_relat_1(X2),X1,X2)),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | ~v1_relat_1(X2)) )),
% 0.20/0.48    inference(equality_resolution,[],[f60])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1) & r2_hidden(sK4(X0,X1,X2),X0)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(flattening,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.48    inference(ennf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).
% 0.20/0.48  fof(f198,plain,(
% 0.20/0.48    k1_xboole_0 != sK2 | ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(sK2)),
% 0.20/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.48  fof(f197,plain,(
% 0.20/0.48    ~spl5_18 | ~spl5_4 | spl5_23 | ~spl5_17),
% 0.20/0.48    inference(avatar_split_clause,[],[f193,f160,f195,f86,f168])).
% 0.20/0.48  fof(f193,plain,(
% 0.20/0.48    ( ! [X0] : (r2_hidden(sK4(sK1,X0,sK3),sK1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) ) | ~spl5_17),
% 0.20/0.48    inference(superposition,[],[f68,f161])).
% 0.20/0.48  fof(f68,plain,(
% 0.20/0.48    ( ! [X2,X1] : (r2_hidden(sK4(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.48    inference(equality_resolution,[],[f59])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK4(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f34])).
% 0.20/0.48  fof(f188,plain,(
% 0.20/0.48    ~spl5_2 | spl5_18),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f187])).
% 0.20/0.48  fof(f187,plain,(
% 0.20/0.48    $false | (~spl5_2 | spl5_18)),
% 0.20/0.48    inference(subsumption_resolution,[],[f79,f186])).
% 0.20/0.48  fof(f186,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl5_18),
% 0.20/0.48    inference(resolution,[],[f169,f45])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.48  fof(f169,plain,(
% 0.20/0.48    ~v1_relat_1(sK3) | spl5_18),
% 0.20/0.48    inference(avatar_component_clause,[],[f168])).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f78])).
% 0.20/0.48  fof(f163,plain,(
% 0.20/0.48    ~spl5_2 | spl5_17 | ~spl5_16),
% 0.20/0.48    inference(avatar_split_clause,[],[f158,f154,f160,f78])).
% 0.20/0.48  fof(f154,plain,(
% 0.20/0.48    spl5_16 <=> sK1 = k1_relset_1(sK1,sK2,sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.48  fof(f158,plain,(
% 0.20/0.48    sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_16),
% 0.20/0.48    inference(superposition,[],[f46,f155])).
% 0.20/0.48  fof(f155,plain,(
% 0.20/0.48    sK1 = k1_relset_1(sK1,sK2,sK3) | ~spl5_16),
% 0.20/0.48    inference(avatar_component_clause,[],[f154])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.48  fof(f156,plain,(
% 0.20/0.48    ~spl5_2 | spl5_15 | spl5_16 | ~spl5_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f147,f82,f154,f151,f78])).
% 0.20/0.48  fof(f151,plain,(
% 0.20/0.48    spl5_15 <=> k1_xboole_0 = sK2),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.20/0.48  fof(f147,plain,(
% 0.20/0.48    sK1 = k1_relset_1(sK1,sK2,sK3) | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_3),
% 0.20/0.48    inference(resolution,[],[f49,f83])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(nnf_transformation,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(flattening,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  % (3918)Refutation not found, incomplete strategy% (3918)------------------------------
% 0.20/0.48  % (3918)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (3918)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (3918)Memory used [KB]: 6140
% 0.20/0.48  % (3918)Time elapsed: 0.066 s
% 0.20/0.48  % (3918)------------------------------
% 0.20/0.48  % (3918)------------------------------
% 0.20/0.48  % (3912)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.48  % (3909)Refutation not found, incomplete strategy% (3909)------------------------------
% 0.20/0.48  % (3909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (3909)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (3909)Memory used [KB]: 10618
% 0.20/0.48  % (3909)Time elapsed: 0.073 s
% 0.20/0.48  % (3909)------------------------------
% 0.20/0.48  % (3909)------------------------------
% 0.20/0.48  % (3925)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.49  % (3919)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.49  % (3910)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.49  % (3919)Refutation not found, incomplete strategy% (3919)------------------------------
% 0.20/0.49  % (3919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (3919)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (3919)Memory used [KB]: 10618
% 0.20/0.49  % (3919)Time elapsed: 0.080 s
% 0.20/0.49  % (3919)------------------------------
% 0.20/0.49  % (3919)------------------------------
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.49  fof(f127,plain,(
% 0.20/0.49    ~spl5_12 | spl5_8 | ~spl5_10),
% 0.20/0.49    inference(avatar_split_clause,[],[f118,f114,f103,f125])).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    spl5_8 <=> m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    spl5_10 <=> k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.49  fof(f118,plain,(
% 0.20/0.49    ~m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK0)) | (spl5_8 | ~spl5_10)),
% 0.20/0.49    inference(superposition,[],[f104,f115])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) | ~spl5_10),
% 0.20/0.49    inference(avatar_component_clause,[],[f114])).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    ~m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK0)) | spl5_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f103])).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    spl5_10 | ~spl5_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f111,f78,f114])).
% 0.20/0.49  fof(f111,plain,(
% 0.20/0.49    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) | ~spl5_2),
% 0.20/0.49    inference(resolution,[],[f47,f79])).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    ~spl5_8 | spl5_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f101,f74,f103])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    spl5_1 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.49  fof(f101,plain,(
% 0.20/0.49    ~m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK0)) | spl5_1),
% 0.20/0.49    inference(resolution,[],[f44,f75])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    ~r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) | spl5_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f74])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.20/0.49    inference(unused_predicate_definition_removal,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.49  fof(f100,plain,(
% 0.20/0.49    spl5_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f42,f98])).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    spl5_7 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    v1_xboole_0(k1_xboole_0)),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    v1_xboole_0(k1_xboole_0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    ~spl5_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f35,f94])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ~v1_xboole_0(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    ~spl5_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f36,f90])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    spl5_5 <=> v1_xboole_0(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ~v1_xboole_0(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    spl5_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f37,f86])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    v1_funct_1(sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    spl5_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f38,f82])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    v1_funct_2(sK3,sK1,sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    spl5_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f39,f78])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    ~spl5_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f41,f74])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ~r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (3914)------------------------------
% 0.20/0.49  % (3914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (3914)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (3914)Memory used [KB]: 10874
% 0.20/0.49  % (3914)Time elapsed: 0.060 s
% 0.20/0.49  % (3914)------------------------------
% 0.20/0.49  % (3914)------------------------------
% 0.20/0.49  % (3907)Success in time 0.135 s
%------------------------------------------------------------------------------
