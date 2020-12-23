%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  203 ( 452 expanded)
%              Number of leaves         :   36 ( 178 expanded)
%              Depth                    :   14
%              Number of atoms          :  887 (1803 expanded)
%              Number of equality atoms :  114 ( 313 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f586,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f56,f60,f67,f71,f75,f101,f108,f114,f130,f142,f173,f193,f202,f206,f264,f274,f332,f350,f362,f367,f383,f395,f430,f480,f510,f547,f571,f578,f585])).

fof(f585,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_21
    | ~ spl6_44
    | spl6_45
    | ~ spl6_56 ),
    inference(avatar_contradiction_clause,[],[f584])).

fof(f584,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_21
    | ~ spl6_44
    | spl6_45
    | ~ spl6_56 ),
    inference(subsumption_resolution,[],[f583,f363])).

fof(f363,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl6_9
  <=> r1_partfun1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f583,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_21
    | ~ spl6_44
    | spl6_45
    | ~ spl6_56 ),
    inference(subsumption_resolution,[],[f582,f361])).

fof(f361,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
    | spl6_45 ),
    inference(avatar_component_clause,[],[f360])).

fof(f360,plain,
    ( spl6_45
  <=> k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f582,plain,
    ( k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4)
    | ~ r1_partfun1(sK2,sK3)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_21
    | ~ spl6_44
    | ~ spl6_56 ),
    inference(subsumption_resolution,[],[f581,f192])).

fof(f192,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl6_21
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f581,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4)
    | ~ r1_partfun1(sK2,sK3)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_44
    | ~ spl6_56 ),
    inference(subsumption_resolution,[],[f580,f113])).

fof(f113,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl6_11
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f580,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK2),sK0)
    | k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4)
    | ~ r1_partfun1(sK2,sK3)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_44
    | ~ spl6_56 ),
    inference(subsumption_resolution,[],[f579,f55])).

fof(f55,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl6_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f579,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK2),sK0)
    | k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4)
    | ~ r1_partfun1(sK2,sK3)
    | ~ spl6_1
    | ~ spl6_8
    | ~ spl6_44
    | ~ spl6_56 ),
    inference(resolution,[],[f357,f496])).

fof(f496,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k1_relat_1(X2))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(k1_relat_1(X2),sK0)
        | k1_funct_1(sK3,X3) = k1_funct_1(X2,X3)
        | ~ r1_partfun1(X2,sK3) )
    | ~ spl6_1
    | ~ spl6_8
    | ~ spl6_56 ),
    inference(subsumption_resolution,[],[f495,f51])).

fof(f51,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl6_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f495,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(k1_relat_1(X2),sK0)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(X2)
        | ~ r2_hidden(X3,k1_relat_1(X2))
        | k1_funct_1(sK3,X3) = k1_funct_1(X2,X3)
        | ~ r1_partfun1(X2,sK3) )
    | ~ spl6_8
    | ~ spl6_56 ),
    inference(subsumption_resolution,[],[f488,f100])).

fof(f100,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl6_8
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f488,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(k1_relat_1(X2),sK0)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(sK3)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(X2)
        | ~ r2_hidden(X3,k1_relat_1(X2))
        | k1_funct_1(sK3,X3) = k1_funct_1(X2,X3)
        | ~ r1_partfun1(X2,sK3) )
    | ~ spl6_56 ),
    inference(superposition,[],[f30,f473])).

fof(f473,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl6_56 ),
    inference(avatar_component_clause,[],[f472])).

fof(f472,plain,
    ( spl6_56
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
      | ~ r1_partfun1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_partfun1(X0,X1)
          <=> ! [X2] :
                ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                | ~ r2_hidden(X2,k1_relat_1(X0)) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_partfun1(X0,X1)
          <=> ! [X2] :
                ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                | ~ r2_hidden(X2,k1_relat_1(X0)) ) )
          | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
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
         => ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
           => ( r1_partfun1(X0,X1)
            <=> ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_partfun1)).

fof(f357,plain,
    ( r2_hidden(sK4,k1_relat_1(sK2))
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f356])).

fof(f356,plain,
    ( spl6_44
  <=> r2_hidden(sK4,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f578,plain,
    ( spl6_44
    | ~ spl6_10
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f576,f272,f106,f356])).

fof(f106,plain,
    ( spl6_10
  <=> r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f272,plain,
    ( spl6_30
  <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f576,plain,
    ( r2_hidden(sK4,k1_relat_1(sK2))
    | ~ spl6_10
    | ~ spl6_30 ),
    inference(forward_demodulation,[],[f107,f273])).

fof(f273,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f272])).

fof(f107,plain,
    ( r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f106])).

fof(f571,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | spl6_9
    | ~ spl6_11
    | ~ spl6_21
    | ~ spl6_30
    | ~ spl6_43
    | ~ spl6_56 ),
    inference(avatar_contradiction_clause,[],[f570])).

fof(f570,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | spl6_9
    | ~ spl6_11
    | ~ spl6_21
    | ~ spl6_30
    | ~ spl6_43
    | ~ spl6_56 ),
    inference(subsumption_resolution,[],[f569,f568])).

fof(f568,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | spl6_9
    | ~ spl6_11
    | ~ spl6_21
    | ~ spl6_56 ),
    inference(subsumption_resolution,[],[f564,f104])).

fof(f104,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f103])).

fof(f564,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))
    | r1_partfun1(sK2,sK3)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_21
    | ~ spl6_56 ),
    inference(subsumption_resolution,[],[f563,f113])).

fof(f563,plain,
    ( ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))
    | r1_partfun1(sK2,sK3)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_21
    | ~ spl6_56 ),
    inference(subsumption_resolution,[],[f559,f55])).

fof(f559,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))
    | r1_partfun1(sK2,sK3)
    | ~ spl6_1
    | ~ spl6_8
    | ~ spl6_21
    | ~ spl6_56 ),
    inference(resolution,[],[f504,f192])).

fof(f504,plain,
    ( ! [X7] :
        ( ~ r1_tarski(k1_relat_1(X7),sK0)
        | ~ v1_funct_1(X7)
        | ~ v1_relat_1(X7)
        | k1_funct_1(X7,sK5(X7,sK3)) != k1_funct_1(sK3,sK5(X7,sK3))
        | r1_partfun1(X7,sK3) )
    | ~ spl6_1
    | ~ spl6_8
    | ~ spl6_56 ),
    inference(subsumption_resolution,[],[f503,f51])).

fof(f503,plain,
    ( ! [X7] :
        ( ~ r1_tarski(k1_relat_1(X7),sK0)
        | ~ v1_funct_1(X7)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(X7)
        | k1_funct_1(X7,sK5(X7,sK3)) != k1_funct_1(sK3,sK5(X7,sK3))
        | r1_partfun1(X7,sK3) )
    | ~ spl6_8
    | ~ spl6_56 ),
    inference(subsumption_resolution,[],[f492,f100])).

fof(f492,plain,
    ( ! [X7] :
        ( ~ r1_tarski(k1_relat_1(X7),sK0)
        | ~ v1_funct_1(X7)
        | ~ v1_relat_1(sK3)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(X7)
        | k1_funct_1(X7,sK5(X7,sK3)) != k1_funct_1(sK3,sK5(X7,sK3))
        | r1_partfun1(X7,sK3) )
    | ~ spl6_56 ),
    inference(superposition,[],[f32,f473])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
      | r1_partfun1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f569,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3))
    | spl6_9
    | ~ spl6_30
    | ~ spl6_43 ),
    inference(resolution,[],[f505,f349])).

fof(f349,plain,
    ( r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f348])).

fof(f348,plain,
    ( spl6_43
  <=> r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f505,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) )
    | spl6_9
    | ~ spl6_30 ),
    inference(superposition,[],[f474,f273])).

fof(f474,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_relset_1(sK0,sK1,sK2))
        | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) )
    | spl6_9 ),
    inference(subsumption_resolution,[],[f23,f104])).

fof(f23,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_relset_1(sK0,sK1,sK2))
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
      | r1_partfun1(sK2,sK3) ) ),
    inference(cnf_transformation,[],[f12])).

% (8208)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( r1_partfun1(X2,X3)
          <~> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( r1_partfun1(X2,X3)
          <~> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ( k1_xboole_0 = X1
               => k1_xboole_0 = X0 )
             => ( r1_partfun1(X2,X3)
              <=> ! [X4] :
                    ( r2_hidden(X4,k1_relset_1(X0,X1,X2))
                   => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ( k1_xboole_0 = X1
             => k1_xboole_0 = X0 )
           => ( r1_partfun1(X2,X3)
            <=> ! [X4] :
                  ( r2_hidden(X4,k1_relset_1(X0,X1,X2))
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_2)).

fof(f547,plain,
    ( spl6_43
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | spl6_9
    | ~ spl6_11
    | ~ spl6_21
    | ~ spl6_56 ),
    inference(avatar_split_clause,[],[f546,f472,f191,f112,f103,f99,f54,f50,f348])).

fof(f546,plain,
    ( r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | spl6_9
    | ~ spl6_11
    | ~ spl6_21
    | ~ spl6_56 ),
    inference(subsumption_resolution,[],[f545,f104])).

fof(f545,plain,
    ( r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | r1_partfun1(sK2,sK3)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_21
    | ~ spl6_56 ),
    inference(subsumption_resolution,[],[f544,f113])).

fof(f544,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | r1_partfun1(sK2,sK3)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_21
    | ~ spl6_56 ),
    inference(subsumption_resolution,[],[f542,f55])).

fof(f542,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | r1_partfun1(sK2,sK3)
    | ~ spl6_1
    | ~ spl6_8
    | ~ spl6_21
    | ~ spl6_56 ),
    inference(resolution,[],[f500,f192])).

fof(f500,plain,
    ( ! [X5] :
        ( ~ r1_tarski(k1_relat_1(X5),sK0)
        | ~ v1_funct_1(X5)
        | ~ v1_relat_1(X5)
        | r2_hidden(sK5(X5,sK3),k1_relat_1(X5))
        | r1_partfun1(X5,sK3) )
    | ~ spl6_1
    | ~ spl6_8
    | ~ spl6_56 ),
    inference(subsumption_resolution,[],[f499,f51])).

fof(f499,plain,
    ( ! [X5] :
        ( ~ r1_tarski(k1_relat_1(X5),sK0)
        | ~ v1_funct_1(X5)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(X5)
        | r2_hidden(sK5(X5,sK3),k1_relat_1(X5))
        | r1_partfun1(X5,sK3) )
    | ~ spl6_8
    | ~ spl6_56 ),
    inference(subsumption_resolution,[],[f490,f100])).

fof(f490,plain,
    ( ! [X5] :
        ( ~ r1_tarski(k1_relat_1(X5),sK0)
        | ~ v1_funct_1(X5)
        | ~ v1_relat_1(sK3)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(X5)
        | r2_hidden(sK5(X5,sK3),k1_relat_1(X5))
        | r1_partfun1(X5,sK3) )
    | ~ spl6_56 ),
    inference(superposition,[],[f31,f473])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | r1_partfun1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f510,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK3)
    | k1_relset_1(sK0,sK1,sK3) != k1_relat_1(sK3)
    | sK0 = k1_relat_1(sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f480,plain,
    ( spl6_26
    | ~ spl6_18
    | ~ spl6_51 ),
    inference(avatar_split_clause,[],[f477,f428,f171,f223])).

fof(f223,plain,
    ( spl6_26
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f171,plain,
    ( spl6_18
  <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f428,plain,
    ( spl6_51
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f477,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl6_18
    | ~ spl6_51 ),
    inference(forward_demodulation,[],[f442,f448])).

fof(f448,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl6_18
    | ~ spl6_51 ),
    inference(subsumption_resolution,[],[f440,f172])).

fof(f172,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f171])).

fof(f440,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl6_51 ),
    inference(resolution,[],[f429,f44])).

fof(f44,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f429,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_51 ),
    inference(avatar_component_clause,[],[f428])).

fof(f442,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl6_51 ),
    inference(resolution,[],[f429,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f430,plain,
    ( spl6_51
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f405,f69,f65,f62,f428])).

fof(f62,plain,
    ( spl6_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f65,plain,
    ( spl6_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f69,plain,
    ( spl6_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f405,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f163,f63])).

fof(f63,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f163,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(superposition,[],[f70,f143])).

fof(f143,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f65])).

fof(f70,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f69])).

fof(f395,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | spl6_9
    | ~ spl6_11
    | ~ spl6_23
    | ~ spl6_26
    | ~ spl6_43
    | ~ spl6_46 ),
    inference(avatar_contradiction_clause,[],[f394])).

fof(f394,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | spl6_9
    | ~ spl6_11
    | ~ spl6_23
    | ~ spl6_26
    | ~ spl6_43
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f392,f391])).

fof(f391,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | spl6_9
    | ~ spl6_11
    | ~ spl6_23
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f390,f104])).

fof(f390,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))
    | r1_partfun1(sK2,sK3)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_23
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f389,f113])).

fof(f389,plain,
    ( ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))
    | r1_partfun1(sK2,sK3)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_23
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f384,f55])).

fof(f384,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3))
    | r1_partfun1(sK2,sK3)
    | ~ spl6_1
    | ~ spl6_8
    | ~ spl6_23
    | ~ spl6_26 ),
    inference(resolution,[],[f258,f201])).

fof(f201,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_xboole_0)
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl6_23
  <=> r1_tarski(k1_relat_1(sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f258,plain,
    ( ! [X6] :
        ( ~ r1_tarski(k1_relat_1(X6),k1_xboole_0)
        | ~ v1_funct_1(X6)
        | ~ v1_relat_1(X6)
        | k1_funct_1(X6,sK5(X6,sK3)) != k1_funct_1(sK3,sK5(X6,sK3))
        | r1_partfun1(X6,sK3) )
    | ~ spl6_1
    | ~ spl6_8
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f257,f51])).

fof(f257,plain,
    ( ! [X6] :
        ( ~ r1_tarski(k1_relat_1(X6),k1_xboole_0)
        | ~ v1_funct_1(X6)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(X6)
        | k1_funct_1(X6,sK5(X6,sK3)) != k1_funct_1(sK3,sK5(X6,sK3))
        | r1_partfun1(X6,sK3) )
    | ~ spl6_8
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f245,f100])).

fof(f245,plain,
    ( ! [X6] :
        ( ~ r1_tarski(k1_relat_1(X6),k1_xboole_0)
        | ~ v1_funct_1(X6)
        | ~ v1_relat_1(sK3)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(X6)
        | k1_funct_1(X6,sK5(X6,sK3)) != k1_funct_1(sK3,sK5(X6,sK3))
        | r1_partfun1(X6,sK3) )
    | ~ spl6_26 ),
    inference(superposition,[],[f32,f224])).

fof(f224,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f223])).

fof(f392,plain,
    ( k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3))
    | ~ spl6_43
    | ~ spl6_46 ),
    inference(resolution,[],[f349,f366])).

fof(f366,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_relat_1(sK2))
        | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) )
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f365])).

fof(f365,plain,
    ( spl6_46
  <=> ! [X4] :
        ( ~ r2_hidden(X4,k1_relat_1(sK2))
        | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f383,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_23
    | ~ spl6_26
    | ~ spl6_44
    | spl6_45 ),
    inference(avatar_contradiction_clause,[],[f382])).

fof(f382,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_23
    | ~ spl6_26
    | ~ spl6_44
    | spl6_45 ),
    inference(subsumption_resolution,[],[f381,f363])).

fof(f381,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_23
    | ~ spl6_26
    | ~ spl6_44
    | spl6_45 ),
    inference(subsumption_resolution,[],[f380,f361])).

fof(f380,plain,
    ( k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4)
    | ~ r1_partfun1(sK2,sK3)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_23
    | ~ spl6_26
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f379,f201])).

fof(f379,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_xboole_0)
    | k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4)
    | ~ r1_partfun1(sK2,sK3)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_26
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f378,f113])).

fof(f378,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK2),k1_xboole_0)
    | k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4)
    | ~ r1_partfun1(sK2,sK3)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_26
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f376,f55])).

fof(f376,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK2),k1_xboole_0)
    | k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4)
    | ~ r1_partfun1(sK2,sK3)
    | ~ spl6_1
    | ~ spl6_8
    | ~ spl6_26
    | ~ spl6_44 ),
    inference(resolution,[],[f250,f357])).

fof(f250,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(k1_relat_1(X0),k1_xboole_0)
        | k1_funct_1(X0,X1) = k1_funct_1(sK3,X1)
        | ~ r1_partfun1(X0,sK3) )
    | ~ spl6_1
    | ~ spl6_8
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f249,f51])).

fof(f249,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(X0),k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(X1,k1_relat_1(X0))
        | k1_funct_1(X0,X1) = k1_funct_1(sK3,X1)
        | ~ r1_partfun1(X0,sK3) )
    | ~ spl6_8
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f241,f100])).

fof(f241,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(X0),k1_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(sK3)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(X1,k1_relat_1(X0))
        | k1_funct_1(X0,X1) = k1_funct_1(sK3,X1)
        | ~ r1_partfun1(X0,sK3) )
    | ~ spl6_26 ),
    inference(superposition,[],[f30,f224])).

fof(f367,plain,
    ( spl6_9
    | spl6_46
    | ~ spl6_4
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f352,f276,f62,f365,f103])).

fof(f276,plain,
    ( spl6_31
  <=> k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f352,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_relat_1(sK2))
        | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
        | r1_partfun1(sK2,sK3) )
    | ~ spl6_4
    | ~ spl6_31 ),
    inference(forward_demodulation,[],[f351,f277])).

fof(f277,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,sK1,sK2)
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f276])).

fof(f351,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_relset_1(k1_xboole_0,sK1,sK2))
        | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
        | r1_partfun1(sK2,sK3) )
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f23,f63])).

fof(f362,plain,
    ( ~ spl6_9
    | ~ spl6_45 ),
    inference(avatar_split_clause,[],[f22,f360,f103])).

fof(f22,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4)
    | ~ r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f350,plain,
    ( spl6_43
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | spl6_9
    | ~ spl6_11
    | ~ spl6_23
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f343,f223,f200,f112,f103,f99,f54,f50,f348])).

fof(f343,plain,
    ( r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | spl6_9
    | ~ spl6_11
    | ~ spl6_23
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f342,f104])).

fof(f342,plain,
    ( r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | r1_partfun1(sK2,sK3)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_23
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f341,f113])).

fof(f341,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | r1_partfun1(sK2,sK3)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_23
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f338,f55])).

fof(f338,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))
    | r1_partfun1(sK2,sK3)
    | ~ spl6_1
    | ~ spl6_8
    | ~ spl6_23
    | ~ spl6_26 ),
    inference(resolution,[],[f254,f201])).

fof(f254,plain,
    ( ! [X4] :
        ( ~ r1_tarski(k1_relat_1(X4),k1_xboole_0)
        | ~ v1_funct_1(X4)
        | ~ v1_relat_1(X4)
        | r2_hidden(sK5(X4,sK3),k1_relat_1(X4))
        | r1_partfun1(X4,sK3) )
    | ~ spl6_1
    | ~ spl6_8
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f253,f51])).

fof(f253,plain,
    ( ! [X4] :
        ( ~ r1_tarski(k1_relat_1(X4),k1_xboole_0)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(X4)
        | r2_hidden(sK5(X4,sK3),k1_relat_1(X4))
        | r1_partfun1(X4,sK3) )
    | ~ spl6_8
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f243,f100])).

fof(f243,plain,
    ( ! [X4] :
        ( ~ r1_tarski(k1_relat_1(X4),k1_xboole_0)
        | ~ v1_funct_1(X4)
        | ~ v1_relat_1(sK3)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(X4)
        | r2_hidden(sK5(X4,sK3),k1_relat_1(X4))
        | r1_partfun1(X4,sK3) )
    | ~ spl6_26 ),
    inference(superposition,[],[f31,f224])).

fof(f332,plain,
    ( spl6_31
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f228,f204,f276])).

fof(f204,plain,
    ( spl6_24
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f228,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,sK1,sK2)
    | ~ spl6_24 ),
    inference(resolution,[],[f205,f40])).

fof(f205,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f204])).

fof(f274,plain,
    ( spl6_30
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f86,f73,f272])).

fof(f73,plain,
    ( spl6_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f86,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl6_7 ),
    inference(resolution,[],[f74,f40])).

fof(f74,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f73])).

fof(f264,plain,
    ( spl6_28
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f76,f69,f262])).

fof(f262,plain,
    ( spl6_28
  <=> k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f76,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl6_6 ),
    inference(resolution,[],[f70,f40])).

fof(f206,plain,
    ( spl6_24
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f149,f73,f62,f204])).

fof(f149,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(superposition,[],[f74,f63])).

fof(f202,plain,
    ( spl6_23
    | ~ spl6_4
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f194,f191,f62,f200])).

fof(f194,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_xboole_0)
    | ~ spl6_4
    | ~ spl6_21 ),
    inference(forward_demodulation,[],[f192,f63])).

fof(f193,plain,
    ( spl6_21
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f137,f128,f191])).

fof(f128,plain,
    ( spl6_15
  <=> m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f137,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl6_15 ),
    inference(resolution,[],[f129,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

% (8220)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f129,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f128])).

fof(f173,plain,
    ( spl6_18
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f155,f65,f62,f58,f171])).

fof(f58,plain,
    ( spl6_3
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f155,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f147,f143])).

fof(f147,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(superposition,[],[f59,f63])).

fof(f59,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f142,plain,
    ( spl6_17
    | ~ spl6_3
    | spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f84,f69,f65,f58,f140])).

fof(f140,plain,
    ( spl6_17
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f84,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl6_3
    | spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f83,f59])).

fof(f83,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f79,f66])).

fof(f66,plain,
    ( k1_xboole_0 != sK1
    | spl6_5 ),
    inference(avatar_component_clause,[],[f65])).

fof(f79,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl6_6 ),
    inference(resolution,[],[f70,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f130,plain,
    ( spl6_15
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f92,f73,f128])).

fof(f92,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f87,f86])).

fof(f87,plain,
    ( m1_subset_1(k1_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))
    | ~ spl6_7 ),
    inference(resolution,[],[f74,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f114,plain,
    ( spl6_11
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f97,f73,f112])).

fof(f97,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f91,f42])).

fof(f42,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f91,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2)
    | ~ spl6_7 ),
    inference(resolution,[],[f74,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f108,plain,
    ( ~ spl6_9
    | spl6_10 ),
    inference(avatar_split_clause,[],[f21,f106,f103])).

fof(f21,plain,
    ( r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2))
    | ~ r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f101,plain,
    ( spl6_8
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f85,f69,f99])).

fof(f85,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f81,f42])).

fof(f81,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3)
    | ~ spl6_6 ),
    inference(resolution,[],[f70,f41])).

fof(f75,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f29,f73])).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f12])).

fof(f71,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f27,f69])).

fof(f27,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f12])).

fof(f67,plain,
    ( spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f24,f65,f62])).

fof(f24,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f12])).

fof(f60,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f26,f58])).

fof(f26,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f56,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f28,f54])).

fof(f28,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f52,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f25,f50])).

fof(f25,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:52:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (8202)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (8209)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (8217)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (8206)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (8212)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (8211)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (8202)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (8218)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (8204)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (8210)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (8207)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (8203)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (8215)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  % (8205)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (8214)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f586,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f52,f56,f60,f67,f71,f75,f101,f108,f114,f130,f142,f173,f193,f202,f206,f264,f274,f332,f350,f362,f367,f383,f395,f430,f480,f510,f547,f571,f578,f585])).
% 0.21/0.51  fof(f585,plain,(
% 0.21/0.51    ~spl6_1 | ~spl6_2 | ~spl6_8 | ~spl6_9 | ~spl6_11 | ~spl6_21 | ~spl6_44 | spl6_45 | ~spl6_56),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f584])).
% 0.21/0.51  fof(f584,plain,(
% 0.21/0.51    $false | (~spl6_1 | ~spl6_2 | ~spl6_8 | ~spl6_9 | ~spl6_11 | ~spl6_21 | ~spl6_44 | spl6_45 | ~spl6_56)),
% 0.21/0.51    inference(subsumption_resolution,[],[f583,f363])).
% 0.21/0.51  fof(f363,plain,(
% 0.21/0.51    r1_partfun1(sK2,sK3) | ~spl6_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f103])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    spl6_9 <=> r1_partfun1(sK2,sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.51  fof(f583,plain,(
% 0.21/0.51    ~r1_partfun1(sK2,sK3) | (~spl6_1 | ~spl6_2 | ~spl6_8 | ~spl6_11 | ~spl6_21 | ~spl6_44 | spl6_45 | ~spl6_56)),
% 0.21/0.51    inference(subsumption_resolution,[],[f582,f361])).
% 0.21/0.51  fof(f361,plain,(
% 0.21/0.51    k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) | spl6_45),
% 0.21/0.51    inference(avatar_component_clause,[],[f360])).
% 0.21/0.51  fof(f360,plain,(
% 0.21/0.51    spl6_45 <=> k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 0.21/0.51  fof(f582,plain,(
% 0.21/0.51    k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4) | ~r1_partfun1(sK2,sK3) | (~spl6_1 | ~spl6_2 | ~spl6_8 | ~spl6_11 | ~spl6_21 | ~spl6_44 | ~spl6_56)),
% 0.21/0.51    inference(subsumption_resolution,[],[f581,f192])).
% 0.21/0.51  fof(f192,plain,(
% 0.21/0.51    r1_tarski(k1_relat_1(sK2),sK0) | ~spl6_21),
% 0.21/0.51    inference(avatar_component_clause,[],[f191])).
% 0.21/0.51  fof(f191,plain,(
% 0.21/0.51    spl6_21 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.21/0.51  fof(f581,plain,(
% 0.21/0.51    ~r1_tarski(k1_relat_1(sK2),sK0) | k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4) | ~r1_partfun1(sK2,sK3) | (~spl6_1 | ~spl6_2 | ~spl6_8 | ~spl6_11 | ~spl6_44 | ~spl6_56)),
% 0.21/0.51    inference(subsumption_resolution,[],[f580,f113])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    v1_relat_1(sK2) | ~spl6_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f112])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    spl6_11 <=> v1_relat_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.51  fof(f580,plain,(
% 0.21/0.51    ~v1_relat_1(sK2) | ~r1_tarski(k1_relat_1(sK2),sK0) | k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4) | ~r1_partfun1(sK2,sK3) | (~spl6_1 | ~spl6_2 | ~spl6_8 | ~spl6_44 | ~spl6_56)),
% 0.21/0.51    inference(subsumption_resolution,[],[f579,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    v1_funct_1(sK2) | ~spl6_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    spl6_2 <=> v1_funct_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.51  fof(f579,plain,(
% 0.21/0.51    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~r1_tarski(k1_relat_1(sK2),sK0) | k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4) | ~r1_partfun1(sK2,sK3) | (~spl6_1 | ~spl6_8 | ~spl6_44 | ~spl6_56)),
% 0.21/0.51    inference(resolution,[],[f357,f496])).
% 0.21/0.51  fof(f496,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~r2_hidden(X3,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r1_tarski(k1_relat_1(X2),sK0) | k1_funct_1(sK3,X3) = k1_funct_1(X2,X3) | ~r1_partfun1(X2,sK3)) ) | (~spl6_1 | ~spl6_8 | ~spl6_56)),
% 0.21/0.51    inference(subsumption_resolution,[],[f495,f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    v1_funct_1(sK3) | ~spl6_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    spl6_1 <=> v1_funct_1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.51  fof(f495,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~r1_tarski(k1_relat_1(X2),sK0) | ~v1_funct_1(X2) | ~v1_funct_1(sK3) | ~v1_relat_1(X2) | ~r2_hidden(X3,k1_relat_1(X2)) | k1_funct_1(sK3,X3) = k1_funct_1(X2,X3) | ~r1_partfun1(X2,sK3)) ) | (~spl6_8 | ~spl6_56)),
% 0.21/0.51    inference(subsumption_resolution,[],[f488,f100])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    v1_relat_1(sK3) | ~spl6_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f99])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    spl6_8 <=> v1_relat_1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.51  fof(f488,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~r1_tarski(k1_relat_1(X2),sK0) | ~v1_funct_1(X2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(X2) | ~r2_hidden(X3,k1_relat_1(X2)) | k1_funct_1(sK3,X3) = k1_funct_1(X2,X3) | ~r1_partfun1(X2,sK3)) ) | ~spl6_56),
% 0.21/0.51    inference(superposition,[],[f30,f473])).
% 0.21/0.51  fof(f473,plain,(
% 0.21/0.51    sK0 = k1_relat_1(sK3) | ~spl6_56),
% 0.21/0.51    inference(avatar_component_clause,[],[f472])).
% 0.21/0.51  fof(f472,plain,(
% 0.21/0.51    spl6_56 <=> sK0 = k1_relat_1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | ~r2_hidden(X2,k1_relat_1(X0)) | k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r1_partfun1(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((r1_partfun1(X0,X1) <=> ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0)))) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) => (r1_partfun1(X0,X1) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_partfun1)).
% 0.21/0.51  fof(f357,plain,(
% 0.21/0.51    r2_hidden(sK4,k1_relat_1(sK2)) | ~spl6_44),
% 0.21/0.51    inference(avatar_component_clause,[],[f356])).
% 0.21/0.51  fof(f356,plain,(
% 0.21/0.51    spl6_44 <=> r2_hidden(sK4,k1_relat_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 0.21/0.51  fof(f578,plain,(
% 0.21/0.51    spl6_44 | ~spl6_10 | ~spl6_30),
% 0.21/0.51    inference(avatar_split_clause,[],[f576,f272,f106,f356])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    spl6_10 <=> r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.51  fof(f272,plain,(
% 0.21/0.51    spl6_30 <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.21/0.51  fof(f576,plain,(
% 0.21/0.51    r2_hidden(sK4,k1_relat_1(sK2)) | (~spl6_10 | ~spl6_30)),
% 0.21/0.51    inference(forward_demodulation,[],[f107,f273])).
% 0.21/0.51  fof(f273,plain,(
% 0.21/0.51    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | ~spl6_30),
% 0.21/0.51    inference(avatar_component_clause,[],[f272])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2)) | ~spl6_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f106])).
% 0.21/0.51  fof(f571,plain,(
% 0.21/0.51    ~spl6_1 | ~spl6_2 | ~spl6_8 | spl6_9 | ~spl6_11 | ~spl6_21 | ~spl6_30 | ~spl6_43 | ~spl6_56),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f570])).
% 0.21/0.51  fof(f570,plain,(
% 0.21/0.51    $false | (~spl6_1 | ~spl6_2 | ~spl6_8 | spl6_9 | ~spl6_11 | ~spl6_21 | ~spl6_30 | ~spl6_43 | ~spl6_56)),
% 0.21/0.51    inference(subsumption_resolution,[],[f569,f568])).
% 0.21/0.51  fof(f568,plain,(
% 0.21/0.51    k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) | (~spl6_1 | ~spl6_2 | ~spl6_8 | spl6_9 | ~spl6_11 | ~spl6_21 | ~spl6_56)),
% 0.21/0.51    inference(subsumption_resolution,[],[f564,f104])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    ~r1_partfun1(sK2,sK3) | spl6_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f103])).
% 0.21/0.51  fof(f564,plain,(
% 0.21/0.51    k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) | r1_partfun1(sK2,sK3) | (~spl6_1 | ~spl6_2 | ~spl6_8 | ~spl6_11 | ~spl6_21 | ~spl6_56)),
% 0.21/0.51    inference(subsumption_resolution,[],[f563,f113])).
% 0.21/0.51  fof(f563,plain,(
% 0.21/0.51    ~v1_relat_1(sK2) | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) | r1_partfun1(sK2,sK3) | (~spl6_1 | ~spl6_2 | ~spl6_8 | ~spl6_21 | ~spl6_56)),
% 0.21/0.51    inference(subsumption_resolution,[],[f559,f55])).
% 0.21/0.51  fof(f559,plain,(
% 0.21/0.51    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) | r1_partfun1(sK2,sK3) | (~spl6_1 | ~spl6_8 | ~spl6_21 | ~spl6_56)),
% 0.21/0.51    inference(resolution,[],[f504,f192])).
% 0.21/0.51  fof(f504,plain,(
% 0.21/0.51    ( ! [X7] : (~r1_tarski(k1_relat_1(X7),sK0) | ~v1_funct_1(X7) | ~v1_relat_1(X7) | k1_funct_1(X7,sK5(X7,sK3)) != k1_funct_1(sK3,sK5(X7,sK3)) | r1_partfun1(X7,sK3)) ) | (~spl6_1 | ~spl6_8 | ~spl6_56)),
% 0.21/0.51    inference(subsumption_resolution,[],[f503,f51])).
% 0.21/0.51  fof(f503,plain,(
% 0.21/0.51    ( ! [X7] : (~r1_tarski(k1_relat_1(X7),sK0) | ~v1_funct_1(X7) | ~v1_funct_1(sK3) | ~v1_relat_1(X7) | k1_funct_1(X7,sK5(X7,sK3)) != k1_funct_1(sK3,sK5(X7,sK3)) | r1_partfun1(X7,sK3)) ) | (~spl6_8 | ~spl6_56)),
% 0.21/0.51    inference(subsumption_resolution,[],[f492,f100])).
% 0.21/0.51  fof(f492,plain,(
% 0.21/0.51    ( ! [X7] : (~r1_tarski(k1_relat_1(X7),sK0) | ~v1_funct_1(X7) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(X7) | k1_funct_1(X7,sK5(X7,sK3)) != k1_funct_1(sK3,sK5(X7,sK3)) | r1_partfun1(X7,sK3)) ) | ~spl6_56),
% 0.21/0.51    inference(superposition,[],[f32,f473])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1)) | r1_partfun1(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f569,plain,(
% 0.21/0.51    k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3)) | (spl6_9 | ~spl6_30 | ~spl6_43)),
% 0.21/0.51    inference(resolution,[],[f505,f349])).
% 0.21/0.51  fof(f349,plain,(
% 0.21/0.51    r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2)) | ~spl6_43),
% 0.21/0.51    inference(avatar_component_clause,[],[f348])).
% 0.21/0.51  fof(f348,plain,(
% 0.21/0.51    spl6_43 <=> r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 0.21/0.51  fof(f505,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)) ) | (spl6_9 | ~spl6_30)),
% 0.21/0.51    inference(superposition,[],[f474,f273])).
% 0.21/0.51  fof(f474,plain,(
% 0.21/0.51    ( ! [X4] : (~r2_hidden(X4,k1_relset_1(sK0,sK1,sK2)) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)) ) | spl6_9),
% 0.21/0.51    inference(subsumption_resolution,[],[f23,f104])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ( ! [X4] : (~r2_hidden(X4,k1_relset_1(sK0,sK1,sK2)) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | r1_partfun1(sK2,sK3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  % (8208)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (? [X3] : ((r1_partfun1(X2,X3) <~> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2)))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (? [X3] : (((r1_partfun1(X2,X3) <~> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,k1_relset_1(X0,X1,X2)))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (r1_partfun1(X2,X3) <=> ! [X4] : (r2_hidden(X4,k1_relset_1(X0,X1,X2)) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f8])).
% 0.21/0.51  fof(f8,conjecture,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (r1_partfun1(X2,X3) <=> ! [X4] : (r2_hidden(X4,k1_relset_1(X0,X1,X2)) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_2)).
% 0.21/0.51  fof(f547,plain,(
% 0.21/0.51    spl6_43 | ~spl6_1 | ~spl6_2 | ~spl6_8 | spl6_9 | ~spl6_11 | ~spl6_21 | ~spl6_56),
% 0.21/0.51    inference(avatar_split_clause,[],[f546,f472,f191,f112,f103,f99,f54,f50,f348])).
% 0.21/0.51  fof(f546,plain,(
% 0.21/0.51    r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2)) | (~spl6_1 | ~spl6_2 | ~spl6_8 | spl6_9 | ~spl6_11 | ~spl6_21 | ~spl6_56)),
% 0.21/0.51    inference(subsumption_resolution,[],[f545,f104])).
% 0.21/0.51  fof(f545,plain,(
% 0.21/0.51    r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2)) | r1_partfun1(sK2,sK3) | (~spl6_1 | ~spl6_2 | ~spl6_8 | ~spl6_11 | ~spl6_21 | ~spl6_56)),
% 0.21/0.51    inference(subsumption_resolution,[],[f544,f113])).
% 0.21/0.51  fof(f544,plain,(
% 0.21/0.51    ~v1_relat_1(sK2) | r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2)) | r1_partfun1(sK2,sK3) | (~spl6_1 | ~spl6_2 | ~spl6_8 | ~spl6_21 | ~spl6_56)),
% 0.21/0.51    inference(subsumption_resolution,[],[f542,f55])).
% 0.21/0.51  fof(f542,plain,(
% 0.21/0.51    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2)) | r1_partfun1(sK2,sK3) | (~spl6_1 | ~spl6_8 | ~spl6_21 | ~spl6_56)),
% 0.21/0.51    inference(resolution,[],[f500,f192])).
% 0.21/0.51  fof(f500,plain,(
% 0.21/0.51    ( ! [X5] : (~r1_tarski(k1_relat_1(X5),sK0) | ~v1_funct_1(X5) | ~v1_relat_1(X5) | r2_hidden(sK5(X5,sK3),k1_relat_1(X5)) | r1_partfun1(X5,sK3)) ) | (~spl6_1 | ~spl6_8 | ~spl6_56)),
% 0.21/0.51    inference(subsumption_resolution,[],[f499,f51])).
% 0.21/0.51  fof(f499,plain,(
% 0.21/0.51    ( ! [X5] : (~r1_tarski(k1_relat_1(X5),sK0) | ~v1_funct_1(X5) | ~v1_funct_1(sK3) | ~v1_relat_1(X5) | r2_hidden(sK5(X5,sK3),k1_relat_1(X5)) | r1_partfun1(X5,sK3)) ) | (~spl6_8 | ~spl6_56)),
% 0.21/0.51    inference(subsumption_resolution,[],[f490,f100])).
% 0.21/0.51  fof(f490,plain,(
% 0.21/0.51    ( ! [X5] : (~r1_tarski(k1_relat_1(X5),sK0) | ~v1_funct_1(X5) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(X5) | r2_hidden(sK5(X5,sK3),k1_relat_1(X5)) | r1_partfun1(X5,sK3)) ) | ~spl6_56),
% 0.21/0.51    inference(superposition,[],[f31,f473])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | r2_hidden(sK5(X0,X1),k1_relat_1(X0)) | r1_partfun1(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f510,plain,(
% 0.21/0.51    sK0 != k1_relset_1(sK0,sK1,sK3) | k1_relset_1(sK0,sK1,sK3) != k1_relat_1(sK3) | sK0 = k1_relat_1(sK3)),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f480,plain,(
% 0.21/0.51    spl6_26 | ~spl6_18 | ~spl6_51),
% 0.21/0.51    inference(avatar_split_clause,[],[f477,f428,f171,f223])).
% 0.21/0.51  fof(f223,plain,(
% 0.21/0.51    spl6_26 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.21/0.51  fof(f171,plain,(
% 0.21/0.51    spl6_18 <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.21/0.51  fof(f428,plain,(
% 0.21/0.51    spl6_51 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).
% 0.21/0.51  fof(f477,plain,(
% 0.21/0.51    k1_xboole_0 = k1_relat_1(sK3) | (~spl6_18 | ~spl6_51)),
% 0.21/0.51    inference(forward_demodulation,[],[f442,f448])).
% 0.21/0.51  fof(f448,plain,(
% 0.21/0.51    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl6_18 | ~spl6_51)),
% 0.21/0.51    inference(subsumption_resolution,[],[f440,f172])).
% 0.21/0.51  fof(f172,plain,(
% 0.21/0.51    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | ~spl6_18),
% 0.21/0.51    inference(avatar_component_clause,[],[f171])).
% 0.21/0.51  fof(f440,plain,(
% 0.21/0.51    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | ~spl6_51),
% 0.21/0.51    inference(resolution,[],[f429,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.51  fof(f429,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl6_51),
% 0.21/0.51    inference(avatar_component_clause,[],[f428])).
% 0.21/0.51  fof(f442,plain,(
% 0.21/0.51    k1_relat_1(sK3) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~spl6_51),
% 0.21/0.51    inference(resolution,[],[f429,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.51  fof(f430,plain,(
% 0.21/0.51    spl6_51 | ~spl6_4 | ~spl6_5 | ~spl6_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f405,f69,f65,f62,f428])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    spl6_4 <=> k1_xboole_0 = sK0),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    spl6_5 <=> k1_xboole_0 = sK1),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    spl6_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.51  fof(f405,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl6_4 | ~spl6_5 | ~spl6_6)),
% 0.21/0.51    inference(forward_demodulation,[],[f163,f63])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | ~spl6_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f62])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl6_5 | ~spl6_6)),
% 0.21/0.51    inference(superposition,[],[f70,f143])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | ~spl6_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f65])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f69])).
% 0.21/0.51  fof(f395,plain,(
% 0.21/0.51    ~spl6_1 | ~spl6_2 | ~spl6_8 | spl6_9 | ~spl6_11 | ~spl6_23 | ~spl6_26 | ~spl6_43 | ~spl6_46),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f394])).
% 0.21/0.51  fof(f394,plain,(
% 0.21/0.51    $false | (~spl6_1 | ~spl6_2 | ~spl6_8 | spl6_9 | ~spl6_11 | ~spl6_23 | ~spl6_26 | ~spl6_43 | ~spl6_46)),
% 0.21/0.51    inference(subsumption_resolution,[],[f392,f391])).
% 0.21/0.51  fof(f391,plain,(
% 0.21/0.51    k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) | (~spl6_1 | ~spl6_2 | ~spl6_8 | spl6_9 | ~spl6_11 | ~spl6_23 | ~spl6_26)),
% 0.21/0.51    inference(subsumption_resolution,[],[f390,f104])).
% 0.21/0.51  fof(f390,plain,(
% 0.21/0.51    k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) | r1_partfun1(sK2,sK3) | (~spl6_1 | ~spl6_2 | ~spl6_8 | ~spl6_11 | ~spl6_23 | ~spl6_26)),
% 0.21/0.51    inference(subsumption_resolution,[],[f389,f113])).
% 0.21/0.51  fof(f389,plain,(
% 0.21/0.51    ~v1_relat_1(sK2) | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) | r1_partfun1(sK2,sK3) | (~spl6_1 | ~spl6_2 | ~spl6_8 | ~spl6_23 | ~spl6_26)),
% 0.21/0.51    inference(subsumption_resolution,[],[f384,f55])).
% 0.21/0.51  fof(f384,plain,(
% 0.21/0.51    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_funct_1(sK2,sK5(sK2,sK3)) != k1_funct_1(sK3,sK5(sK2,sK3)) | r1_partfun1(sK2,sK3) | (~spl6_1 | ~spl6_8 | ~spl6_23 | ~spl6_26)),
% 0.21/0.51    inference(resolution,[],[f258,f201])).
% 0.21/0.51  fof(f201,plain,(
% 0.21/0.51    r1_tarski(k1_relat_1(sK2),k1_xboole_0) | ~spl6_23),
% 0.21/0.51    inference(avatar_component_clause,[],[f200])).
% 0.21/0.51  fof(f200,plain,(
% 0.21/0.51    spl6_23 <=> r1_tarski(k1_relat_1(sK2),k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.21/0.51  fof(f258,plain,(
% 0.21/0.51    ( ! [X6] : (~r1_tarski(k1_relat_1(X6),k1_xboole_0) | ~v1_funct_1(X6) | ~v1_relat_1(X6) | k1_funct_1(X6,sK5(X6,sK3)) != k1_funct_1(sK3,sK5(X6,sK3)) | r1_partfun1(X6,sK3)) ) | (~spl6_1 | ~spl6_8 | ~spl6_26)),
% 0.21/0.51    inference(subsumption_resolution,[],[f257,f51])).
% 0.21/0.51  fof(f257,plain,(
% 0.21/0.51    ( ! [X6] : (~r1_tarski(k1_relat_1(X6),k1_xboole_0) | ~v1_funct_1(X6) | ~v1_funct_1(sK3) | ~v1_relat_1(X6) | k1_funct_1(X6,sK5(X6,sK3)) != k1_funct_1(sK3,sK5(X6,sK3)) | r1_partfun1(X6,sK3)) ) | (~spl6_8 | ~spl6_26)),
% 0.21/0.51    inference(subsumption_resolution,[],[f245,f100])).
% 0.21/0.51  fof(f245,plain,(
% 0.21/0.51    ( ! [X6] : (~r1_tarski(k1_relat_1(X6),k1_xboole_0) | ~v1_funct_1(X6) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(X6) | k1_funct_1(X6,sK5(X6,sK3)) != k1_funct_1(sK3,sK5(X6,sK3)) | r1_partfun1(X6,sK3)) ) | ~spl6_26),
% 0.21/0.51    inference(superposition,[],[f32,f224])).
% 0.21/0.51  fof(f224,plain,(
% 0.21/0.51    k1_xboole_0 = k1_relat_1(sK3) | ~spl6_26),
% 0.21/0.51    inference(avatar_component_clause,[],[f223])).
% 0.21/0.51  fof(f392,plain,(
% 0.21/0.51    k1_funct_1(sK2,sK5(sK2,sK3)) = k1_funct_1(sK3,sK5(sK2,sK3)) | (~spl6_43 | ~spl6_46)),
% 0.21/0.51    inference(resolution,[],[f349,f366])).
% 0.21/0.51  fof(f366,plain,(
% 0.21/0.51    ( ! [X4] : (~r2_hidden(X4,k1_relat_1(sK2)) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)) ) | ~spl6_46),
% 0.21/0.51    inference(avatar_component_clause,[],[f365])).
% 0.21/0.51  fof(f365,plain,(
% 0.21/0.51    spl6_46 <=> ! [X4] : (~r2_hidden(X4,k1_relat_1(sK2)) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).
% 0.21/0.51  fof(f383,plain,(
% 0.21/0.51    ~spl6_1 | ~spl6_2 | ~spl6_8 | ~spl6_9 | ~spl6_11 | ~spl6_23 | ~spl6_26 | ~spl6_44 | spl6_45),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f382])).
% 0.21/0.51  fof(f382,plain,(
% 0.21/0.51    $false | (~spl6_1 | ~spl6_2 | ~spl6_8 | ~spl6_9 | ~spl6_11 | ~spl6_23 | ~spl6_26 | ~spl6_44 | spl6_45)),
% 0.21/0.51    inference(subsumption_resolution,[],[f381,f363])).
% 0.21/0.51  fof(f381,plain,(
% 0.21/0.51    ~r1_partfun1(sK2,sK3) | (~spl6_1 | ~spl6_2 | ~spl6_8 | ~spl6_11 | ~spl6_23 | ~spl6_26 | ~spl6_44 | spl6_45)),
% 0.21/0.51    inference(subsumption_resolution,[],[f380,f361])).
% 0.21/0.51  fof(f380,plain,(
% 0.21/0.51    k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4) | ~r1_partfun1(sK2,sK3) | (~spl6_1 | ~spl6_2 | ~spl6_8 | ~spl6_11 | ~spl6_23 | ~spl6_26 | ~spl6_44)),
% 0.21/0.51    inference(subsumption_resolution,[],[f379,f201])).
% 0.21/0.51  fof(f379,plain,(
% 0.21/0.51    ~r1_tarski(k1_relat_1(sK2),k1_xboole_0) | k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4) | ~r1_partfun1(sK2,sK3) | (~spl6_1 | ~spl6_2 | ~spl6_8 | ~spl6_11 | ~spl6_26 | ~spl6_44)),
% 0.21/0.51    inference(subsumption_resolution,[],[f378,f113])).
% 0.21/0.51  fof(f378,plain,(
% 0.21/0.51    ~v1_relat_1(sK2) | ~r1_tarski(k1_relat_1(sK2),k1_xboole_0) | k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4) | ~r1_partfun1(sK2,sK3) | (~spl6_1 | ~spl6_2 | ~spl6_8 | ~spl6_26 | ~spl6_44)),
% 0.21/0.51    inference(subsumption_resolution,[],[f376,f55])).
% 0.21/0.51  fof(f376,plain,(
% 0.21/0.51    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~r1_tarski(k1_relat_1(sK2),k1_xboole_0) | k1_funct_1(sK2,sK4) = k1_funct_1(sK3,sK4) | ~r1_partfun1(sK2,sK3) | (~spl6_1 | ~spl6_8 | ~spl6_26 | ~spl6_44)),
% 0.21/0.51    inference(resolution,[],[f250,f357])).
% 0.21/0.51  fof(f250,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k1_xboole_0) | k1_funct_1(X0,X1) = k1_funct_1(sK3,X1) | ~r1_partfun1(X0,sK3)) ) | (~spl6_1 | ~spl6_8 | ~spl6_26)),
% 0.21/0.51    inference(subsumption_resolution,[],[f249,f51])).
% 0.21/0.51  fof(f249,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k1_xboole_0) | ~v1_funct_1(X0) | ~v1_funct_1(sK3) | ~v1_relat_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | k1_funct_1(X0,X1) = k1_funct_1(sK3,X1) | ~r1_partfun1(X0,sK3)) ) | (~spl6_8 | ~spl6_26)),
% 0.21/0.51    inference(subsumption_resolution,[],[f241,f100])).
% 0.21/0.51  fof(f241,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k1_xboole_0) | ~v1_funct_1(X0) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | k1_funct_1(X0,X1) = k1_funct_1(sK3,X1) | ~r1_partfun1(X0,sK3)) ) | ~spl6_26),
% 0.21/0.51    inference(superposition,[],[f30,f224])).
% 0.21/0.51  fof(f367,plain,(
% 0.21/0.51    spl6_9 | spl6_46 | ~spl6_4 | ~spl6_31),
% 0.21/0.51    inference(avatar_split_clause,[],[f352,f276,f62,f365,f103])).
% 0.21/0.51  fof(f276,plain,(
% 0.21/0.51    spl6_31 <=> k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,sK1,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.21/0.51  fof(f352,plain,(
% 0.21/0.51    ( ! [X4] : (~r2_hidden(X4,k1_relat_1(sK2)) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | r1_partfun1(sK2,sK3)) ) | (~spl6_4 | ~spl6_31)),
% 0.21/0.51    inference(forward_demodulation,[],[f351,f277])).
% 0.21/0.51  fof(f277,plain,(
% 0.21/0.51    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,sK1,sK2) | ~spl6_31),
% 0.21/0.51    inference(avatar_component_clause,[],[f276])).
% 0.21/0.51  fof(f351,plain,(
% 0.21/0.51    ( ! [X4] : (~r2_hidden(X4,k1_relset_1(k1_xboole_0,sK1,sK2)) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | r1_partfun1(sK2,sK3)) ) | ~spl6_4),
% 0.21/0.51    inference(forward_demodulation,[],[f23,f63])).
% 0.21/0.51  fof(f362,plain,(
% 0.21/0.51    ~spl6_9 | ~spl6_45),
% 0.21/0.51    inference(avatar_split_clause,[],[f22,f360,f103])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    k1_funct_1(sK2,sK4) != k1_funct_1(sK3,sK4) | ~r1_partfun1(sK2,sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f350,plain,(
% 0.21/0.51    spl6_43 | ~spl6_1 | ~spl6_2 | ~spl6_8 | spl6_9 | ~spl6_11 | ~spl6_23 | ~spl6_26),
% 0.21/0.51    inference(avatar_split_clause,[],[f343,f223,f200,f112,f103,f99,f54,f50,f348])).
% 0.21/0.51  fof(f343,plain,(
% 0.21/0.51    r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2)) | (~spl6_1 | ~spl6_2 | ~spl6_8 | spl6_9 | ~spl6_11 | ~spl6_23 | ~spl6_26)),
% 0.21/0.51    inference(subsumption_resolution,[],[f342,f104])).
% 0.21/0.51  fof(f342,plain,(
% 0.21/0.51    r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2)) | r1_partfun1(sK2,sK3) | (~spl6_1 | ~spl6_2 | ~spl6_8 | ~spl6_11 | ~spl6_23 | ~spl6_26)),
% 0.21/0.51    inference(subsumption_resolution,[],[f341,f113])).
% 0.21/0.51  fof(f341,plain,(
% 0.21/0.51    ~v1_relat_1(sK2) | r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2)) | r1_partfun1(sK2,sK3) | (~spl6_1 | ~spl6_2 | ~spl6_8 | ~spl6_23 | ~spl6_26)),
% 0.21/0.51    inference(subsumption_resolution,[],[f338,f55])).
% 0.21/0.51  fof(f338,plain,(
% 0.21/0.51    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | r2_hidden(sK5(sK2,sK3),k1_relat_1(sK2)) | r1_partfun1(sK2,sK3) | (~spl6_1 | ~spl6_8 | ~spl6_23 | ~spl6_26)),
% 0.21/0.51    inference(resolution,[],[f254,f201])).
% 0.21/0.51  fof(f254,plain,(
% 0.21/0.51    ( ! [X4] : (~r1_tarski(k1_relat_1(X4),k1_xboole_0) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | r2_hidden(sK5(X4,sK3),k1_relat_1(X4)) | r1_partfun1(X4,sK3)) ) | (~spl6_1 | ~spl6_8 | ~spl6_26)),
% 0.21/0.51    inference(subsumption_resolution,[],[f253,f51])).
% 0.21/0.51  fof(f253,plain,(
% 0.21/0.51    ( ! [X4] : (~r1_tarski(k1_relat_1(X4),k1_xboole_0) | ~v1_funct_1(X4) | ~v1_funct_1(sK3) | ~v1_relat_1(X4) | r2_hidden(sK5(X4,sK3),k1_relat_1(X4)) | r1_partfun1(X4,sK3)) ) | (~spl6_8 | ~spl6_26)),
% 0.21/0.51    inference(subsumption_resolution,[],[f243,f100])).
% 0.21/0.51  fof(f243,plain,(
% 0.21/0.51    ( ! [X4] : (~r1_tarski(k1_relat_1(X4),k1_xboole_0) | ~v1_funct_1(X4) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(X4) | r2_hidden(sK5(X4,sK3),k1_relat_1(X4)) | r1_partfun1(X4,sK3)) ) | ~spl6_26),
% 0.21/0.51    inference(superposition,[],[f31,f224])).
% 0.21/0.51  fof(f332,plain,(
% 0.21/0.51    spl6_31 | ~spl6_24),
% 0.21/0.51    inference(avatar_split_clause,[],[f228,f204,f276])).
% 0.21/0.51  fof(f204,plain,(
% 0.21/0.51    spl6_24 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.21/0.51  fof(f228,plain,(
% 0.21/0.51    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,sK1,sK2) | ~spl6_24),
% 0.21/0.51    inference(resolution,[],[f205,f40])).
% 0.21/0.51  fof(f205,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~spl6_24),
% 0.21/0.51    inference(avatar_component_clause,[],[f204])).
% 0.21/0.51  fof(f274,plain,(
% 0.21/0.51    spl6_30 | ~spl6_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f86,f73,f272])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    spl6_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | ~spl6_7),
% 0.21/0.51    inference(resolution,[],[f74,f40])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f73])).
% 0.21/0.51  fof(f264,plain,(
% 0.21/0.51    spl6_28 | ~spl6_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f76,f69,f262])).
% 0.21/0.51  fof(f262,plain,(
% 0.21/0.51    spl6_28 <=> k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) | ~spl6_6),
% 0.21/0.51    inference(resolution,[],[f70,f40])).
% 0.21/0.51  fof(f206,plain,(
% 0.21/0.51    spl6_24 | ~spl6_4 | ~spl6_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f149,f73,f62,f204])).
% 0.21/0.51  fof(f149,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl6_4 | ~spl6_7)),
% 0.21/0.51    inference(superposition,[],[f74,f63])).
% 0.21/0.51  fof(f202,plain,(
% 0.21/0.51    spl6_23 | ~spl6_4 | ~spl6_21),
% 0.21/0.51    inference(avatar_split_clause,[],[f194,f191,f62,f200])).
% 0.21/0.51  fof(f194,plain,(
% 0.21/0.51    r1_tarski(k1_relat_1(sK2),k1_xboole_0) | (~spl6_4 | ~spl6_21)),
% 0.21/0.51    inference(forward_demodulation,[],[f192,f63])).
% 0.21/0.51  fof(f193,plain,(
% 0.21/0.51    spl6_21 | ~spl6_15),
% 0.21/0.51    inference(avatar_split_clause,[],[f137,f128,f191])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    spl6_15 <=> m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    r1_tarski(k1_relat_1(sK2),sK0) | ~spl6_15),
% 0.21/0.51    inference(resolution,[],[f129,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.21/0.51    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.51  % (8220)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) | ~spl6_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f128])).
% 0.21/0.51  fof(f173,plain,(
% 0.21/0.51    spl6_18 | ~spl6_3 | ~spl6_4 | ~spl6_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f155,f65,f62,f58,f171])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    spl6_3 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl6_3 | ~spl6_4 | ~spl6_5)),
% 0.21/0.51    inference(forward_demodulation,[],[f147,f143])).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    v1_funct_2(sK3,k1_xboole_0,sK1) | (~spl6_3 | ~spl6_4)),
% 0.21/0.51    inference(superposition,[],[f59,f63])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    v1_funct_2(sK3,sK0,sK1) | ~spl6_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f58])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    spl6_17 | ~spl6_3 | spl6_5 | ~spl6_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f84,f69,f65,f58,f140])).
% 0.21/0.51  fof(f140,plain,(
% 0.21/0.51    spl6_17 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    sK0 = k1_relset_1(sK0,sK1,sK3) | (~spl6_3 | spl6_5 | ~spl6_6)),
% 0.21/0.51    inference(subsumption_resolution,[],[f83,f59])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | (spl6_5 | ~spl6_6)),
% 0.21/0.51    inference(subsumption_resolution,[],[f79,f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    k1_xboole_0 != sK1 | spl6_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f65])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | ~spl6_6),
% 0.21/0.51    inference(resolution,[],[f70,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    spl6_15 | ~spl6_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f92,f73,f128])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) | ~spl6_7),
% 0.21/0.51    inference(forward_demodulation,[],[f87,f86])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    m1_subset_1(k1_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) | ~spl6_7),
% 0.21/0.51    inference(resolution,[],[f74,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    spl6_11 | ~spl6_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f97,f73,f112])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    v1_relat_1(sK2) | ~spl6_7),
% 0.21/0.51    inference(subsumption_resolution,[],[f91,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2) | ~spl6_7),
% 0.21/0.51    inference(resolution,[],[f74,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    ~spl6_9 | spl6_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f21,f106,f103])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    r2_hidden(sK4,k1_relset_1(sK0,sK1,sK2)) | ~r1_partfun1(sK2,sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    spl6_8 | ~spl6_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f85,f69,f99])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    v1_relat_1(sK3) | ~spl6_6),
% 0.21/0.51    inference(subsumption_resolution,[],[f81,f42])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3) | ~spl6_6),
% 0.21/0.51    inference(resolution,[],[f70,f41])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    spl6_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f29,f73])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    spl6_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f27,f69])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    spl6_4 | ~spl6_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f24,f65,f62])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    spl6_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f26,f58])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    spl6_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f28,f54])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    v1_funct_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    spl6_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f25,f50])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    v1_funct_1(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (8202)------------------------------
% 0.21/0.52  % (8202)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (8202)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (8202)Memory used [KB]: 6524
% 0.21/0.52  % (8202)Time elapsed: 0.076 s
% 0.21/0.52  % (8202)------------------------------
% 0.21/0.52  % (8202)------------------------------
% 0.21/0.52  % (8201)Success in time 0.151 s
%------------------------------------------------------------------------------
