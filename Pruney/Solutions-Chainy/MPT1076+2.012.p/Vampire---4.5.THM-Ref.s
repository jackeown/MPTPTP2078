%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  192 ( 425 expanded)
%              Number of leaves         :   45 ( 203 expanded)
%              Depth                    :   16
%              Number of atoms          :  776 (2164 expanded)
%              Number of equality atoms :   62 ( 216 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f462,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f82,f87,f92,f97,f102,f107,f112,f117,f122,f147,f163,f164,f187,f188,f204,f205,f211,f225,f285,f324,f330,f341,f347,f380,f411,f448,f461])).

fof(f461,plain,
    ( ~ spl6_5
    | ~ spl6_15
    | ~ spl6_19
    | ~ spl6_28
    | ~ spl6_32
    | spl6_43 ),
    inference(avatar_contradiction_clause,[],[f460])).

fof(f460,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_15
    | ~ spl6_19
    | ~ spl6_28
    | ~ spl6_32
    | spl6_43 ),
    inference(subsumption_resolution,[],[f459,f346])).

fof(f346,plain,
    ( r2_hidden(k1_funct_1(sK3,sK5),sK0)
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f344])).

fof(f344,plain,
    ( spl6_32
  <=> r2_hidden(k1_funct_1(sK3,sK5),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f459,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),sK0)
    | ~ spl6_5
    | ~ spl6_15
    | ~ spl6_19
    | ~ spl6_28
    | spl6_43 ),
    inference(forward_demodulation,[],[f458,f284])).

fof(f284,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f282])).

fof(f282,plain,
    ( spl6_28
  <=> sK0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f458,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ spl6_5
    | ~ spl6_15
    | ~ spl6_19
    | spl6_43 ),
    inference(subsumption_resolution,[],[f457,f161])).

fof(f161,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl6_15
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f457,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ spl6_5
    | ~ spl6_19
    | spl6_43 ),
    inference(subsumption_resolution,[],[f456,f202])).

fof(f202,plain,
    ( v5_relat_1(sK4,sK2)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl6_19
  <=> v5_relat_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f456,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ v5_relat_1(sK4,sK2)
    | ~ v1_relat_1(sK4)
    | ~ spl6_5
    | spl6_43 ),
    inference(subsumption_resolution,[],[f452,f96])).

fof(f96,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl6_5
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f452,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v5_relat_1(sK4,sK2)
    | ~ v1_relat_1(sK4)
    | spl6_43 ),
    inference(trivial_inequality_removal,[],[f451])).

fof(f451,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v5_relat_1(sK4,sK2)
    | ~ v1_relat_1(sK4)
    | spl6_43 ),
    inference(superposition,[],[f447,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

fof(f447,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | spl6_43 ),
    inference(avatar_component_clause,[],[f445])).

fof(f445,plain,
    ( spl6_43
  <=> k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f448,plain,
    ( ~ spl6_43
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | spl6_9
    | spl6_10
    | ~ spl6_34
    | spl6_40 ),
    inference(avatar_split_clause,[],[f443,f408,f377,f119,f114,f109,f104,f99,f94,f89,f84,f79,f445])).

fof(f79,plain,
    ( spl6_2
  <=> v1_partfun1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f84,plain,
    ( spl6_3
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f89,plain,
    ( spl6_4
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f99,plain,
    ( spl6_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f104,plain,
    ( spl6_7
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f109,plain,
    ( spl6_8
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f114,plain,
    ( spl6_9
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f119,plain,
    ( spl6_10
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f377,plain,
    ( spl6_34
  <=> k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f408,plain,
    ( spl6_40
  <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f443,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | spl6_9
    | spl6_10
    | ~ spl6_34
    | spl6_40 ),
    inference(forward_demodulation,[],[f442,f379])).

fof(f379,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5)
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f377])).

fof(f442,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | spl6_9
    | spl6_10
    | spl6_40 ),
    inference(subsumption_resolution,[],[f441,f121])).

fof(f121,plain,
    ( ~ v1_xboole_0(sK0)
    | spl6_10 ),
    inference(avatar_component_clause,[],[f119])).

fof(f441,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | v1_xboole_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | spl6_9
    | spl6_40 ),
    inference(subsumption_resolution,[],[f440,f116])).

fof(f116,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f114])).

fof(f440,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | spl6_40 ),
    inference(subsumption_resolution,[],[f439,f111])).

fof(f111,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f109])).

fof(f439,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_40 ),
    inference(subsumption_resolution,[],[f438,f106])).

fof(f106,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f104])).

fof(f438,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_40 ),
    inference(subsumption_resolution,[],[f437,f101])).

fof(f101,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f99])).

fof(f437,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_40 ),
    inference(subsumption_resolution,[],[f436,f96])).

fof(f436,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_40 ),
    inference(subsumption_resolution,[],[f435,f91])).

fof(f91,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f435,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | spl6_40 ),
    inference(subsumption_resolution,[],[f434,f86])).

fof(f86,plain,
    ( m1_subset_1(sK5,sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f434,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | ~ m1_subset_1(sK5,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_2
    | spl6_40 ),
    inference(subsumption_resolution,[],[f425,f81])).

fof(f81,plain,
    ( v1_partfun1(sK4,sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f425,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | ~ v1_partfun1(sK4,sK0)
    | ~ m1_subset_1(sK5,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_40 ),
    inference(superposition,[],[f410,f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
      | ~ v1_partfun1(X4,X0)
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                      | ~ v1_partfun1(X4,X0)
                      | ~ m1_subset_1(X5,X1) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  | ~ v1_funct_1(X4) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              | ~ v1_funct_2(X3,X1,X0)
              | ~ v1_funct_1(X3) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                      | ~ v1_partfun1(X4,X0)
                      | ~ m1_subset_1(X5,X1) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  | ~ v1_funct_1(X4) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              | ~ v1_funct_2(X3,X1,X0)
              | ~ v1_funct_1(X3) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2,X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
             => ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                    & v1_funct_1(X4) )
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( v1_partfun1(X4,X0)
                       => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_funct_2)).

fof(f410,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | spl6_40 ),
    inference(avatar_component_clause,[],[f408])).

fof(f411,plain,
    ( ~ spl6_40
    | spl6_1
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f401,f377,f74,f408])).

fof(f74,plain,
    ( spl6_1
  <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f401,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | spl6_1
    | ~ spl6_34 ),
    inference(backward_demodulation,[],[f76,f379])).

fof(f76,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f380,plain,
    ( spl6_34
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | spl6_9 ),
    inference(avatar_split_clause,[],[f374,f114,f109,f104,f99,f84,f377])).

fof(f374,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5)
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | spl6_9 ),
    inference(unit_resulting_resolution,[],[f116,f111,f86,f106,f101,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f347,plain,
    ( spl6_32
    | spl6_10
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f342,f338,f119,f344])).

fof(f338,plain,
    ( spl6_31
  <=> m1_subset_1(k1_funct_1(sK3,sK5),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f342,plain,
    ( r2_hidden(k1_funct_1(sK3,sK5),sK0)
    | spl6_10
    | ~ spl6_31 ),
    inference(unit_resulting_resolution,[],[f121,f340,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f340,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK5),sK0)
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f338])).

fof(f341,plain,
    ( spl6_31
    | ~ spl6_8
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_22
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f336,f327,f222,f154,f144,f109,f338])).

fof(f144,plain,
    ( spl6_13
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f154,plain,
    ( spl6_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f222,plain,
    ( spl6_22
  <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f327,plain,
    ( spl6_30
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f336,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK5),sK0)
    | ~ spl6_8
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_22
    | ~ spl6_30 ),
    inference(unit_resulting_resolution,[],[f146,f331])).

fof(f331,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_funct_1(sK3,X0),sK0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl6_8
    | ~ spl6_14
    | ~ spl6_22
    | ~ spl6_30 ),
    inference(backward_demodulation,[],[f293,f329])).

fof(f329,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f327])).

fof(f293,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_funct_1(sK3,X0),sK0)
        | ~ r2_hidden(X0,k1_relat_1(sK3)) )
    | ~ spl6_8
    | ~ spl6_14
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f292,f156])).

fof(f156,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f154])).

fof(f292,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK3))
        | ~ v1_relat_1(sK3)
        | m1_subset_1(k1_funct_1(sK3,X0),sK0) )
    | ~ spl6_8
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f290,f111])).

fof(f290,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK3))
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3)
        | m1_subset_1(k1_funct_1(sK3,X0),sK0) )
    | ~ spl6_22 ),
    inference(resolution,[],[f61,f244])).

fof(f244,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_relat_1(sK3))
        | m1_subset_1(X3,sK0) )
    | ~ spl6_22 ),
    inference(resolution,[],[f70,f224])).

fof(f224,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK0))
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f222])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

fof(f146,plain,
    ( r2_hidden(sK5,sK1)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f144])).

fof(f330,plain,
    ( spl6_30
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f325,f317,f178,f154,f327])).

fof(f178,plain,
    ( spl6_16
  <=> v4_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f317,plain,
    ( spl6_29
  <=> v1_partfun1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f325,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_29 ),
    inference(unit_resulting_resolution,[],[f156,f180,f319,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f319,plain,
    ( v1_partfun1(sK3,sK1)
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f317])).

fof(f180,plain,
    ( v4_relat_1(sK3,sK1)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f178])).

fof(f324,plain,
    ( spl6_29
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | spl6_10 ),
    inference(avatar_split_clause,[],[f323,f119,f109,f104,f99,f317])).

fof(f323,plain,
    ( v1_partfun1(sK3,sK1)
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | spl6_10 ),
    inference(subsumption_resolution,[],[f322,f121])).

fof(f322,plain,
    ( v1_partfun1(sK3,sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f321,f111])).

fof(f321,plain,
    ( ~ v1_funct_1(sK3)
    | v1_partfun1(sK3,sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f314,f106])).

fof(f314,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | v1_partfun1(sK3,sK1)
    | v1_xboole_0(sK0)
    | ~ spl6_6 ),
    inference(resolution,[],[f57,f101])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_partfun1(X2,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f285,plain,
    ( spl6_28
    | ~ spl6_2
    | ~ spl6_15
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f276,f183,f159,f79,f282])).

fof(f183,plain,
    ( spl6_17
  <=> v4_relat_1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f276,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ spl6_2
    | ~ spl6_15
    | ~ spl6_17 ),
    inference(unit_resulting_resolution,[],[f161,f185,f81,f62])).

fof(f185,plain,
    ( v4_relat_1(sK4,sK0)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f183])).

fof(f225,plain,
    ( spl6_22
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f219,f208,f222])).

fof(f208,plain,
    ( spl6_20
  <=> r1_tarski(k2_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f219,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK0))
    | ~ spl6_20 ),
    inference(unit_resulting_resolution,[],[f210,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f210,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f208])).

fof(f211,plain,
    ( spl6_20
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f206,f195,f154,f208])).

fof(f195,plain,
    ( spl6_18
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f206,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0)
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(unit_resulting_resolution,[],[f156,f197,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f197,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f195])).

fof(f205,plain,
    ( spl6_19
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f193,f89,f200])).

fof(f193,plain,
    ( v5_relat_1(sK4,sK2)
    | ~ spl6_4 ),
    inference(resolution,[],[f69,f91])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f204,plain,
    ( spl6_18
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f192,f99,f195])).

fof(f192,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ spl6_6 ),
    inference(resolution,[],[f69,f101])).

fof(f188,plain,
    ( spl6_17
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f176,f89,f183])).

fof(f176,plain,
    ( v4_relat_1(sK4,sK0)
    | ~ spl6_4 ),
    inference(resolution,[],[f68,f91])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f187,plain,
    ( spl6_16
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f175,f99,f178])).

fof(f175,plain,
    ( v4_relat_1(sK3,sK1)
    | ~ spl6_6 ),
    inference(resolution,[],[f68,f101])).

fof(f164,plain,
    ( spl6_15
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f152,f89,f159])).

fof(f152,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_4 ),
    inference(resolution,[],[f67,f91])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f163,plain,
    ( spl6_14
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f151,f99,f154])).

fof(f151,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_6 ),
    inference(resolution,[],[f67,f101])).

fof(f147,plain,
    ( spl6_13
    | ~ spl6_3
    | spl6_9 ),
    inference(avatar_split_clause,[],[f142,f114,f84,f144])).

fof(f142,plain,
    ( r2_hidden(sK5,sK1)
    | ~ spl6_3
    | spl6_9 ),
    inference(unit_resulting_resolution,[],[f86,f116,f60])).

fof(f122,plain,(
    ~ spl6_10 ),
    inference(avatar_split_clause,[],[f45,f119])).

fof(f45,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    & v1_partfun1(sK4,sK0)
    & m1_subset_1(sK5,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f16,f40,f39,f38,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2,X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                        & v1_partfun1(X4,X0)
                        & m1_subset_1(X5,X1) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X3,X2] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,sK0,X3,X5))
                      & v1_partfun1(X4,sK0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
              & v1_funct_2(X3,X1,sK0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( ? [X3,X2] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,sK0,X3,X5))
                    & v1_partfun1(X4,sK0)
                    & m1_subset_1(X5,X1) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
            & v1_funct_2(X3,X1,sK0)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X3,X2] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k3_funct_2(sK1,X2,k8_funct_2(sK1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(sK1,sK0,X3,X5))
                  & v1_partfun1(X4,sK0)
                  & m1_subset_1(X5,sK1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X3,X2] :
        ( ? [X4] :
            ( ? [X5] :
                ( k3_funct_2(sK1,X2,k8_funct_2(sK1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(sK1,sK0,X3,X5))
                & v1_partfun1(X4,sK0)
                & m1_subset_1(X5,sK1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,X4),X5) != k7_partfun1(sK2,X4,k3_funct_2(sK1,sK0,sK3,X5))
              & v1_partfun1(X4,sK0)
              & m1_subset_1(X5,sK1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,X4),X5) != k7_partfun1(sK2,X4,k3_funct_2(sK1,sK0,sK3,X5))
            & v1_partfun1(X4,sK0)
            & m1_subset_1(X5,sK1) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,X5))
          & v1_partfun1(sK4,sK0)
          & m1_subset_1(X5,sK1) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X5] :
        ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,X5))
        & v1_partfun1(sK4,sK0)
        & m1_subset_1(X5,sK1) )
   => ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))
      & v1_partfun1(sK4,sK0)
      & m1_subset_1(sK5,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2,X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                  & v1_funct_2(X3,X1,X0)
                  & v1_funct_1(X3) )
               => ! [X4] :
                    ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                      & v1_funct_1(X4) )
                   => ! [X5] :
                        ( m1_subset_1(X5,X1)
                       => ( v1_partfun1(X4,X0)
                         => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2,X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
             => ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                    & v1_funct_1(X4) )
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( v1_partfun1(X4,X0)
                       => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_funct_2)).

fof(f117,plain,(
    ~ spl6_9 ),
    inference(avatar_split_clause,[],[f46,f114])).

fof(f46,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f112,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f47,f109])).

fof(f47,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f107,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f48,f104])).

fof(f48,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f102,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f49,f99])).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f97,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f50,f94])).

fof(f50,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f92,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f51,f89])).

fof(f51,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f41])).

fof(f87,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f52,f84])).

fof(f52,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f82,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f53,f79])).

fof(f53,plain,(
    v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f77,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f54,f74])).

fof(f54,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:19:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.42  % (21494)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.43  % (21494)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f462,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f77,f82,f87,f92,f97,f102,f107,f112,f117,f122,f147,f163,f164,f187,f188,f204,f205,f211,f225,f285,f324,f330,f341,f347,f380,f411,f448,f461])).
% 0.20/0.43  fof(f461,plain,(
% 0.20/0.43    ~spl6_5 | ~spl6_15 | ~spl6_19 | ~spl6_28 | ~spl6_32 | spl6_43),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f460])).
% 0.20/0.43  fof(f460,plain,(
% 0.20/0.43    $false | (~spl6_5 | ~spl6_15 | ~spl6_19 | ~spl6_28 | ~spl6_32 | spl6_43)),
% 0.20/0.43    inference(subsumption_resolution,[],[f459,f346])).
% 0.20/0.43  fof(f346,plain,(
% 0.20/0.43    r2_hidden(k1_funct_1(sK3,sK5),sK0) | ~spl6_32),
% 0.20/0.43    inference(avatar_component_clause,[],[f344])).
% 0.20/0.43  fof(f344,plain,(
% 0.20/0.43    spl6_32 <=> r2_hidden(k1_funct_1(sK3,sK5),sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 0.20/0.43  fof(f459,plain,(
% 0.20/0.43    ~r2_hidden(k1_funct_1(sK3,sK5),sK0) | (~spl6_5 | ~spl6_15 | ~spl6_19 | ~spl6_28 | spl6_43)),
% 0.20/0.43    inference(forward_demodulation,[],[f458,f284])).
% 0.20/0.43  fof(f284,plain,(
% 0.20/0.43    sK0 = k1_relat_1(sK4) | ~spl6_28),
% 0.20/0.43    inference(avatar_component_clause,[],[f282])).
% 0.20/0.43  fof(f282,plain,(
% 0.20/0.43    spl6_28 <=> sK0 = k1_relat_1(sK4)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.20/0.43  fof(f458,plain,(
% 0.20/0.43    ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | (~spl6_5 | ~spl6_15 | ~spl6_19 | spl6_43)),
% 0.20/0.43    inference(subsumption_resolution,[],[f457,f161])).
% 0.20/0.43  fof(f161,plain,(
% 0.20/0.43    v1_relat_1(sK4) | ~spl6_15),
% 0.20/0.43    inference(avatar_component_clause,[],[f159])).
% 0.20/0.43  fof(f159,plain,(
% 0.20/0.43    spl6_15 <=> v1_relat_1(sK4)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.20/0.43  fof(f457,plain,(
% 0.20/0.43    ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~v1_relat_1(sK4) | (~spl6_5 | ~spl6_19 | spl6_43)),
% 0.20/0.43    inference(subsumption_resolution,[],[f456,f202])).
% 0.20/0.43  fof(f202,plain,(
% 0.20/0.43    v5_relat_1(sK4,sK2) | ~spl6_19),
% 0.20/0.43    inference(avatar_component_clause,[],[f200])).
% 0.20/0.43  fof(f200,plain,(
% 0.20/0.43    spl6_19 <=> v5_relat_1(sK4,sK2)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.20/0.43  fof(f456,plain,(
% 0.20/0.43    ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~v5_relat_1(sK4,sK2) | ~v1_relat_1(sK4) | (~spl6_5 | spl6_43)),
% 0.20/0.43    inference(subsumption_resolution,[],[f452,f96])).
% 0.20/0.43  fof(f96,plain,(
% 0.20/0.43    v1_funct_1(sK4) | ~spl6_5),
% 0.20/0.43    inference(avatar_component_clause,[],[f94])).
% 0.20/0.43  fof(f94,plain,(
% 0.20/0.43    spl6_5 <=> v1_funct_1(sK4)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.43  fof(f452,plain,(
% 0.20/0.43    ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v5_relat_1(sK4,sK2) | ~v1_relat_1(sK4) | spl6_43),
% 0.20/0.43    inference(trivial_inequality_removal,[],[f451])).
% 0.20/0.43  fof(f451,plain,(
% 0.20/0.43    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v5_relat_1(sK4,sK2) | ~v1_relat_1(sK4) | spl6_43),
% 0.20/0.43    inference(superposition,[],[f447,f64])).
% 0.20/0.43  fof(f64,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f29])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(flattening,[],[f28])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.43    inference(ennf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,axiom,(
% 0.20/0.43    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).
% 0.20/0.43  fof(f447,plain,(
% 0.20/0.43    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | spl6_43),
% 0.20/0.43    inference(avatar_component_clause,[],[f445])).
% 0.20/0.43  fof(f445,plain,(
% 0.20/0.43    spl6_43 <=> k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 0.20/0.43  fof(f448,plain,(
% 0.20/0.43    ~spl6_43 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | spl6_9 | spl6_10 | ~spl6_34 | spl6_40),
% 0.20/0.43    inference(avatar_split_clause,[],[f443,f408,f377,f119,f114,f109,f104,f99,f94,f89,f84,f79,f445])).
% 0.20/0.43  fof(f79,plain,(
% 0.20/0.43    spl6_2 <=> v1_partfun1(sK4,sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.43  fof(f84,plain,(
% 0.20/0.43    spl6_3 <=> m1_subset_1(sK5,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.43  fof(f89,plain,(
% 0.20/0.43    spl6_4 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.43  fof(f99,plain,(
% 0.20/0.43    spl6_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.43  fof(f104,plain,(
% 0.20/0.43    spl6_7 <=> v1_funct_2(sK3,sK1,sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.43  fof(f109,plain,(
% 0.20/0.43    spl6_8 <=> v1_funct_1(sK3)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.20/0.43  fof(f114,plain,(
% 0.20/0.43    spl6_9 <=> v1_xboole_0(sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.20/0.43  fof(f119,plain,(
% 0.20/0.43    spl6_10 <=> v1_xboole_0(sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.43  fof(f377,plain,(
% 0.20/0.43    spl6_34 <=> k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 0.20/0.43  fof(f408,plain,(
% 0.20/0.43    spl6_40 <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 0.20/0.43  fof(f443,plain,(
% 0.20/0.43    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | spl6_9 | spl6_10 | ~spl6_34 | spl6_40)),
% 0.20/0.43    inference(forward_demodulation,[],[f442,f379])).
% 0.20/0.43  fof(f379,plain,(
% 0.20/0.43    k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) | ~spl6_34),
% 0.20/0.43    inference(avatar_component_clause,[],[f377])).
% 0.20/0.43  fof(f442,plain,(
% 0.20/0.43    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | spl6_9 | spl6_10 | spl6_40)),
% 0.20/0.43    inference(subsumption_resolution,[],[f441,f121])).
% 0.20/0.43  fof(f121,plain,(
% 0.20/0.43    ~v1_xboole_0(sK0) | spl6_10),
% 0.20/0.43    inference(avatar_component_clause,[],[f119])).
% 0.20/0.43  fof(f441,plain,(
% 0.20/0.43    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | v1_xboole_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | spl6_9 | spl6_40)),
% 0.20/0.43    inference(subsumption_resolution,[],[f440,f116])).
% 0.20/0.43  fof(f116,plain,(
% 0.20/0.43    ~v1_xboole_0(sK1) | spl6_9),
% 0.20/0.43    inference(avatar_component_clause,[],[f114])).
% 0.20/0.43  fof(f440,plain,(
% 0.20/0.43    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | spl6_40)),
% 0.20/0.43    inference(subsumption_resolution,[],[f439,f111])).
% 0.20/0.43  fof(f111,plain,(
% 0.20/0.43    v1_funct_1(sK3) | ~spl6_8),
% 0.20/0.43    inference(avatar_component_clause,[],[f109])).
% 0.20/0.43  fof(f439,plain,(
% 0.20/0.43    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | ~v1_funct_1(sK3) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | spl6_40)),
% 0.20/0.43    inference(subsumption_resolution,[],[f438,f106])).
% 0.20/0.43  fof(f106,plain,(
% 0.20/0.43    v1_funct_2(sK3,sK1,sK0) | ~spl6_7),
% 0.20/0.43    inference(avatar_component_clause,[],[f104])).
% 0.20/0.43  fof(f438,plain,(
% 0.20/0.43    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_40)),
% 0.20/0.43    inference(subsumption_resolution,[],[f437,f101])).
% 0.20/0.43  fof(f101,plain,(
% 0.20/0.43    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl6_6),
% 0.20/0.43    inference(avatar_component_clause,[],[f99])).
% 0.20/0.43  fof(f437,plain,(
% 0.20/0.43    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | spl6_40)),
% 0.20/0.43    inference(subsumption_resolution,[],[f436,f96])).
% 0.20/0.43  fof(f436,plain,(
% 0.20/0.43    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_40)),
% 0.20/0.43    inference(subsumption_resolution,[],[f435,f91])).
% 0.20/0.43  fof(f91,plain,(
% 0.20/0.43    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl6_4),
% 0.20/0.43    inference(avatar_component_clause,[],[f89])).
% 0.20/0.43  fof(f435,plain,(
% 0.20/0.43    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | (~spl6_2 | ~spl6_3 | spl6_40)),
% 0.20/0.43    inference(subsumption_resolution,[],[f434,f86])).
% 0.20/0.43  fof(f86,plain,(
% 0.20/0.43    m1_subset_1(sK5,sK1) | ~spl6_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f84])).
% 0.20/0.43  fof(f434,plain,(
% 0.20/0.43    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | ~m1_subset_1(sK5,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | (~spl6_2 | spl6_40)),
% 0.20/0.43    inference(subsumption_resolution,[],[f425,f81])).
% 0.20/0.43  fof(f81,plain,(
% 0.20/0.43    v1_partfun1(sK4,sK0) | ~spl6_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f79])).
% 0.20/0.43  fof(f425,plain,(
% 0.20/0.43    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | ~v1_partfun1(sK4,sK0) | ~m1_subset_1(sK5,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_40),
% 0.20/0.43    inference(superposition,[],[f410,f55])).
% 0.20/0.43  fof(f55,plain,(
% 0.20/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) | ~v1_partfun1(X4,X0) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (! [X2,X3] : (! [X4] : (! [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) | ~v1_partfun1(X4,X0) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.43    inference(flattening,[],[f17])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (! [X2,X3] : (! [X4] : (! [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) | ~v1_partfun1(X4,X0)) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f12])).
% 0.20/0.43  fof(f12,axiom,(
% 0.20/0.43    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_funct_2)).
% 0.20/0.43  fof(f410,plain,(
% 0.20/0.43    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | spl6_40),
% 0.20/0.43    inference(avatar_component_clause,[],[f408])).
% 0.20/0.43  fof(f411,plain,(
% 0.20/0.43    ~spl6_40 | spl6_1 | ~spl6_34),
% 0.20/0.43    inference(avatar_split_clause,[],[f401,f377,f74,f408])).
% 0.20/0.43  fof(f74,plain,(
% 0.20/0.43    spl6_1 <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.43  fof(f401,plain,(
% 0.20/0.43    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | (spl6_1 | ~spl6_34)),
% 0.20/0.43    inference(backward_demodulation,[],[f76,f379])).
% 0.20/0.43  fof(f76,plain,(
% 0.20/0.43    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | spl6_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f74])).
% 0.20/0.43  fof(f380,plain,(
% 0.20/0.43    spl6_34 | ~spl6_3 | ~spl6_6 | ~spl6_7 | ~spl6_8 | spl6_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f374,f114,f109,f104,f99,f84,f377])).
% 0.20/0.43  fof(f374,plain,(
% 0.20/0.43    k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) | (~spl6_3 | ~spl6_6 | ~spl6_7 | ~spl6_8 | spl6_9)),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f116,f111,f86,f106,f101,f71])).
% 0.20/0.43  fof(f71,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f35])).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.20/0.43    inference(flattening,[],[f34])).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.20/0.43  fof(f347,plain,(
% 0.20/0.43    spl6_32 | spl6_10 | ~spl6_31),
% 0.20/0.43    inference(avatar_split_clause,[],[f342,f338,f119,f344])).
% 0.20/0.43  fof(f338,plain,(
% 0.20/0.43    spl6_31 <=> m1_subset_1(k1_funct_1(sK3,sK5),sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.20/0.43  fof(f342,plain,(
% 0.20/0.43    r2_hidden(k1_funct_1(sK3,sK5),sK0) | (spl6_10 | ~spl6_31)),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f121,f340,f60])).
% 0.20/0.43  fof(f60,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f23])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.43    inference(flattening,[],[f22])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.43  fof(f340,plain,(
% 0.20/0.43    m1_subset_1(k1_funct_1(sK3,sK5),sK0) | ~spl6_31),
% 0.20/0.43    inference(avatar_component_clause,[],[f338])).
% 0.20/0.43  fof(f341,plain,(
% 0.20/0.43    spl6_31 | ~spl6_8 | ~spl6_13 | ~spl6_14 | ~spl6_22 | ~spl6_30),
% 0.20/0.43    inference(avatar_split_clause,[],[f336,f327,f222,f154,f144,f109,f338])).
% 0.20/0.43  fof(f144,plain,(
% 0.20/0.43    spl6_13 <=> r2_hidden(sK5,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.20/0.43  fof(f154,plain,(
% 0.20/0.43    spl6_14 <=> v1_relat_1(sK3)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.20/0.43  fof(f222,plain,(
% 0.20/0.43    spl6_22 <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.20/0.43  fof(f327,plain,(
% 0.20/0.43    spl6_30 <=> sK1 = k1_relat_1(sK3)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.20/0.43  fof(f336,plain,(
% 0.20/0.43    m1_subset_1(k1_funct_1(sK3,sK5),sK0) | (~spl6_8 | ~spl6_13 | ~spl6_14 | ~spl6_22 | ~spl6_30)),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f146,f331])).
% 0.20/0.43  fof(f331,plain,(
% 0.20/0.43    ( ! [X0] : (m1_subset_1(k1_funct_1(sK3,X0),sK0) | ~r2_hidden(X0,sK1)) ) | (~spl6_8 | ~spl6_14 | ~spl6_22 | ~spl6_30)),
% 0.20/0.43    inference(backward_demodulation,[],[f293,f329])).
% 0.20/0.43  fof(f329,plain,(
% 0.20/0.43    sK1 = k1_relat_1(sK3) | ~spl6_30),
% 0.20/0.43    inference(avatar_component_clause,[],[f327])).
% 0.20/0.43  fof(f293,plain,(
% 0.20/0.43    ( ! [X0] : (m1_subset_1(k1_funct_1(sK3,X0),sK0) | ~r2_hidden(X0,k1_relat_1(sK3))) ) | (~spl6_8 | ~spl6_14 | ~spl6_22)),
% 0.20/0.43    inference(subsumption_resolution,[],[f292,f156])).
% 0.20/0.43  fof(f156,plain,(
% 0.20/0.43    v1_relat_1(sK3) | ~spl6_14),
% 0.20/0.43    inference(avatar_component_clause,[],[f154])).
% 0.20/0.43  fof(f292,plain,(
% 0.20/0.43    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | m1_subset_1(k1_funct_1(sK3,X0),sK0)) ) | (~spl6_8 | ~spl6_22)),
% 0.20/0.43    inference(subsumption_resolution,[],[f290,f111])).
% 0.20/0.43  fof(f290,plain,(
% 0.20/0.43    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | m1_subset_1(k1_funct_1(sK3,X0),sK0)) ) | ~spl6_22),
% 0.20/0.43    inference(resolution,[],[f61,f244])).
% 0.20/0.43  fof(f244,plain,(
% 0.20/0.43    ( ! [X3] : (~r2_hidden(X3,k2_relat_1(sK3)) | m1_subset_1(X3,sK0)) ) | ~spl6_22),
% 0.20/0.43    inference(resolution,[],[f70,f224])).
% 0.20/0.43  fof(f224,plain,(
% 0.20/0.43    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK0)) | ~spl6_22),
% 0.20/0.43    inference(avatar_component_clause,[],[f222])).
% 0.20/0.43  fof(f70,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f33])).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.43    inference(flattening,[],[f32])).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.20/0.43    inference(ennf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.20/0.43  fof(f61,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f25])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(flattening,[],[f24])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.43    inference(ennf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).
% 0.20/0.43  fof(f146,plain,(
% 0.20/0.43    r2_hidden(sK5,sK1) | ~spl6_13),
% 0.20/0.43    inference(avatar_component_clause,[],[f144])).
% 0.20/0.43  fof(f330,plain,(
% 0.20/0.43    spl6_30 | ~spl6_14 | ~spl6_16 | ~spl6_29),
% 0.20/0.43    inference(avatar_split_clause,[],[f325,f317,f178,f154,f327])).
% 0.20/0.43  fof(f178,plain,(
% 0.20/0.43    spl6_16 <=> v4_relat_1(sK3,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.20/0.43  fof(f317,plain,(
% 0.20/0.43    spl6_29 <=> v1_partfun1(sK3,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.20/0.43  fof(f325,plain,(
% 0.20/0.43    sK1 = k1_relat_1(sK3) | (~spl6_14 | ~spl6_16 | ~spl6_29)),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f156,f180,f319,f62])).
% 0.20/0.43  fof(f62,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f43])).
% 0.20/0.43  fof(f43,plain,(
% 0.20/0.43    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(nnf_transformation,[],[f27])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(flattening,[],[f26])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.43    inference(ennf_transformation,[],[f9])).
% 0.20/0.43  fof(f9,axiom,(
% 0.20/0.43    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.20/0.43  fof(f319,plain,(
% 0.20/0.43    v1_partfun1(sK3,sK1) | ~spl6_29),
% 0.20/0.43    inference(avatar_component_clause,[],[f317])).
% 0.20/0.43  fof(f180,plain,(
% 0.20/0.43    v4_relat_1(sK3,sK1) | ~spl6_16),
% 0.20/0.43    inference(avatar_component_clause,[],[f178])).
% 0.20/0.43  fof(f324,plain,(
% 0.20/0.43    spl6_29 | ~spl6_6 | ~spl6_7 | ~spl6_8 | spl6_10),
% 0.20/0.43    inference(avatar_split_clause,[],[f323,f119,f109,f104,f99,f317])).
% 0.20/0.43  fof(f323,plain,(
% 0.20/0.43    v1_partfun1(sK3,sK1) | (~spl6_6 | ~spl6_7 | ~spl6_8 | spl6_10)),
% 0.20/0.43    inference(subsumption_resolution,[],[f322,f121])).
% 0.20/0.43  fof(f322,plain,(
% 0.20/0.43    v1_partfun1(sK3,sK1) | v1_xboole_0(sK0) | (~spl6_6 | ~spl6_7 | ~spl6_8)),
% 0.20/0.43    inference(subsumption_resolution,[],[f321,f111])).
% 0.20/0.43  fof(f321,plain,(
% 0.20/0.43    ~v1_funct_1(sK3) | v1_partfun1(sK3,sK1) | v1_xboole_0(sK0) | (~spl6_6 | ~spl6_7)),
% 0.20/0.43    inference(subsumption_resolution,[],[f314,f106])).
% 0.20/0.43  fof(f314,plain,(
% 0.20/0.43    ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | v1_partfun1(sK3,sK1) | v1_xboole_0(sK0) | ~spl6_6),
% 0.20/0.43    inference(resolution,[],[f57,f101])).
% 0.20/0.43  fof(f57,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_partfun1(X2,X0) | v1_xboole_0(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f20])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.43    inference(flattening,[],[f19])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,axiom,(
% 0.20/0.43    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.20/0.43  fof(f285,plain,(
% 0.20/0.43    spl6_28 | ~spl6_2 | ~spl6_15 | ~spl6_17),
% 0.20/0.43    inference(avatar_split_clause,[],[f276,f183,f159,f79,f282])).
% 0.20/0.43  fof(f183,plain,(
% 0.20/0.43    spl6_17 <=> v4_relat_1(sK4,sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.20/0.43  fof(f276,plain,(
% 0.20/0.43    sK0 = k1_relat_1(sK4) | (~spl6_2 | ~spl6_15 | ~spl6_17)),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f161,f185,f81,f62])).
% 0.20/0.43  fof(f185,plain,(
% 0.20/0.43    v4_relat_1(sK4,sK0) | ~spl6_17),
% 0.20/0.43    inference(avatar_component_clause,[],[f183])).
% 0.20/0.43  fof(f225,plain,(
% 0.20/0.43    spl6_22 | ~spl6_20),
% 0.20/0.43    inference(avatar_split_clause,[],[f219,f208,f222])).
% 0.20/0.43  fof(f208,plain,(
% 0.20/0.43    spl6_20 <=> r1_tarski(k2_relat_1(sK3),sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.20/0.43  fof(f219,plain,(
% 0.20/0.43    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK0)) | ~spl6_20),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f210,f66])).
% 0.20/0.43  fof(f66,plain,(
% 0.20/0.43    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f44])).
% 0.20/0.43  fof(f44,plain,(
% 0.20/0.43    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.43    inference(nnf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.43  fof(f210,plain,(
% 0.20/0.43    r1_tarski(k2_relat_1(sK3),sK0) | ~spl6_20),
% 0.20/0.43    inference(avatar_component_clause,[],[f208])).
% 0.20/0.43  fof(f211,plain,(
% 0.20/0.43    spl6_20 | ~spl6_14 | ~spl6_18),
% 0.20/0.43    inference(avatar_split_clause,[],[f206,f195,f154,f208])).
% 0.20/0.43  fof(f195,plain,(
% 0.20/0.43    spl6_18 <=> v5_relat_1(sK3,sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.20/0.43  fof(f206,plain,(
% 0.20/0.43    r1_tarski(k2_relat_1(sK3),sK0) | (~spl6_14 | ~spl6_18)),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f156,f197,f58])).
% 0.20/0.43  fof(f58,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f42])).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(nnf_transformation,[],[f21])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.43  fof(f197,plain,(
% 0.20/0.43    v5_relat_1(sK3,sK0) | ~spl6_18),
% 0.20/0.43    inference(avatar_component_clause,[],[f195])).
% 0.20/0.43  fof(f205,plain,(
% 0.20/0.43    spl6_19 | ~spl6_4),
% 0.20/0.43    inference(avatar_split_clause,[],[f193,f89,f200])).
% 0.20/0.43  fof(f193,plain,(
% 0.20/0.43    v5_relat_1(sK4,sK2) | ~spl6_4),
% 0.20/0.43    inference(resolution,[],[f69,f91])).
% 0.20/0.43  fof(f69,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f31])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.43    inference(ennf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.43  fof(f204,plain,(
% 0.20/0.43    spl6_18 | ~spl6_6),
% 0.20/0.43    inference(avatar_split_clause,[],[f192,f99,f195])).
% 0.20/0.43  fof(f192,plain,(
% 0.20/0.43    v5_relat_1(sK3,sK0) | ~spl6_6),
% 0.20/0.43    inference(resolution,[],[f69,f101])).
% 0.20/0.43  fof(f188,plain,(
% 0.20/0.43    spl6_17 | ~spl6_4),
% 0.20/0.43    inference(avatar_split_clause,[],[f176,f89,f183])).
% 0.20/0.43  fof(f176,plain,(
% 0.20/0.43    v4_relat_1(sK4,sK0) | ~spl6_4),
% 0.20/0.43    inference(resolution,[],[f68,f91])).
% 0.20/0.43  fof(f68,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f31])).
% 0.20/0.43  fof(f187,plain,(
% 0.20/0.43    spl6_16 | ~spl6_6),
% 0.20/0.43    inference(avatar_split_clause,[],[f175,f99,f178])).
% 0.20/0.43  fof(f175,plain,(
% 0.20/0.43    v4_relat_1(sK3,sK1) | ~spl6_6),
% 0.20/0.43    inference(resolution,[],[f68,f101])).
% 0.20/0.43  fof(f164,plain,(
% 0.20/0.43    spl6_15 | ~spl6_4),
% 0.20/0.43    inference(avatar_split_clause,[],[f152,f89,f159])).
% 0.20/0.43  fof(f152,plain,(
% 0.20/0.43    v1_relat_1(sK4) | ~spl6_4),
% 0.20/0.43    inference(resolution,[],[f67,f91])).
% 0.20/0.43  fof(f67,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f30])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.43    inference(ennf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.43  fof(f163,plain,(
% 0.20/0.43    spl6_14 | ~spl6_6),
% 0.20/0.43    inference(avatar_split_clause,[],[f151,f99,f154])).
% 0.20/0.43  fof(f151,plain,(
% 0.20/0.43    v1_relat_1(sK3) | ~spl6_6),
% 0.20/0.43    inference(resolution,[],[f67,f101])).
% 0.20/0.43  fof(f147,plain,(
% 0.20/0.43    spl6_13 | ~spl6_3 | spl6_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f142,f114,f84,f144])).
% 0.20/0.43  fof(f142,plain,(
% 0.20/0.43    r2_hidden(sK5,sK1) | (~spl6_3 | spl6_9)),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f86,f116,f60])).
% 0.20/0.43  fof(f122,plain,(
% 0.20/0.43    ~spl6_10),
% 0.20/0.43    inference(avatar_split_clause,[],[f45,f119])).
% 0.20/0.43  fof(f45,plain,(
% 0.20/0.43    ~v1_xboole_0(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f41])).
% 0.20/0.43  fof(f41,plain,(
% 0.20/0.43    ((((k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) & v1_partfun1(sK4,sK0) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f16,f40,f39,f38,f37,f36])).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,sK0,X3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) & v1_funct_2(X3,X1,sK0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    ? [X1] : (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,sK0,X3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) & v1_funct_2(X3,X1,sK0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) => (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(sK1,X2,k8_funct_2(sK1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(sK1,sK0,X3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & ~v1_xboole_0(sK1))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f38,plain,(
% 0.20/0.43    ? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(sK1,X2,k8_funct_2(sK1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(sK1,sK0,X3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,X4),X5) != k7_partfun1(sK2,X4,k3_funct_2(sK1,sK0,sK3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f39,plain,(
% 0.20/0.43    ? [X4] : (? [X5] : (k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,X4),X5) != k7_partfun1(sK2,X4,k3_funct_2(sK1,sK0,sK3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(X4)) => (? [X5] : (k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,X5)) & v1_partfun1(sK4,sK0) & m1_subset_1(X5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(sK4))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    ? [X5] : (k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,X5)) & v1_partfun1(sK4,sK0) & m1_subset_1(X5,sK1)) => (k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) & v1_partfun1(sK4,sK0) & m1_subset_1(sK5,sK1))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.43    inference(flattening,[],[f15])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0)) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f14])).
% 0.20/0.43  fof(f14,negated_conjecture,(
% 0.20/0.43    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.20/0.43    inference(negated_conjecture,[],[f13])).
% 0.20/0.43  fof(f13,conjecture,(
% 0.20/0.43    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_funct_2)).
% 0.20/0.43  fof(f117,plain,(
% 0.20/0.43    ~spl6_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f46,f114])).
% 0.20/0.43  fof(f46,plain,(
% 0.20/0.43    ~v1_xboole_0(sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f41])).
% 0.20/0.43  fof(f112,plain,(
% 0.20/0.43    spl6_8),
% 0.20/0.43    inference(avatar_split_clause,[],[f47,f109])).
% 0.20/0.43  fof(f47,plain,(
% 0.20/0.43    v1_funct_1(sK3)),
% 0.20/0.43    inference(cnf_transformation,[],[f41])).
% 0.20/0.43  fof(f107,plain,(
% 0.20/0.43    spl6_7),
% 0.20/0.43    inference(avatar_split_clause,[],[f48,f104])).
% 0.20/0.43  fof(f48,plain,(
% 0.20/0.43    v1_funct_2(sK3,sK1,sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f41])).
% 0.20/0.43  fof(f102,plain,(
% 0.20/0.43    spl6_6),
% 0.20/0.43    inference(avatar_split_clause,[],[f49,f99])).
% 0.20/0.43  fof(f49,plain,(
% 0.20/0.43    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.43    inference(cnf_transformation,[],[f41])).
% 0.20/0.43  fof(f97,plain,(
% 0.20/0.43    spl6_5),
% 0.20/0.43    inference(avatar_split_clause,[],[f50,f94])).
% 0.20/0.43  fof(f50,plain,(
% 0.20/0.43    v1_funct_1(sK4)),
% 0.20/0.43    inference(cnf_transformation,[],[f41])).
% 0.20/0.43  fof(f92,plain,(
% 0.20/0.43    spl6_4),
% 0.20/0.43    inference(avatar_split_clause,[],[f51,f89])).
% 0.20/0.43  fof(f51,plain,(
% 0.20/0.43    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.20/0.43    inference(cnf_transformation,[],[f41])).
% 0.20/0.43  fof(f87,plain,(
% 0.20/0.43    spl6_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f52,f84])).
% 0.20/0.43  fof(f52,plain,(
% 0.20/0.43    m1_subset_1(sK5,sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f41])).
% 0.20/0.43  fof(f82,plain,(
% 0.20/0.43    spl6_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f53,f79])).
% 0.20/0.43  fof(f53,plain,(
% 0.20/0.43    v1_partfun1(sK4,sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f41])).
% 0.20/0.43  fof(f77,plain,(
% 0.20/0.43    ~spl6_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f54,f74])).
% 0.20/0.43  fof(f54,plain,(
% 0.20/0.43    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.20/0.43    inference(cnf_transformation,[],[f41])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (21494)------------------------------
% 0.20/0.43  % (21494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (21494)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (21494)Memory used [KB]: 11001
% 0.20/0.43  % (21494)Time elapsed: 0.016 s
% 0.20/0.43  % (21494)------------------------------
% 0.20/0.43  % (21494)------------------------------
% 0.20/0.44  % (21477)Success in time 0.082 s
%------------------------------------------------------------------------------
