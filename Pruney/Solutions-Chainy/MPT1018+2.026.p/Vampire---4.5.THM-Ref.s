%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 220 expanded)
%              Number of leaves         :   16 (  83 expanded)
%              Depth                    :   11
%              Number of atoms          :  314 (1048 expanded)
%              Number of equality atoms :   69 ( 266 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f111,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f44,f49,f54,f59,f66,f71,f85,f97,f101,f107,f109])).

fof(f109,plain,
    ( ~ spl4_4
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f103,f60])).

fof(f60,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f23,f28])).

fof(f28,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f23,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f103,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f48,f81])).

fof(f81,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl4_9
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f48,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl4_4
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f107,plain,
    ( ~ spl4_3
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f106])).

fof(f106,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f102,f60])).

fof(f102,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f43,f81])).

fof(f43,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl4_3
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f101,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | spl4_9 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | spl4_9 ),
    inference(subsumption_resolution,[],[f99,f53])).

fof(f53,plain,
    ( sK2 != sK3
    | spl4_5 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl4_5
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f99,plain,
    ( sK2 = sK3
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | spl4_9 ),
    inference(forward_demodulation,[],[f98,f88])).

fof(f88,plain,
    ( sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | spl4_9 ),
    inference(unit_resulting_resolution,[],[f33,f38,f43,f58,f65,f80,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_funct_1(X3)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

fof(f80,plain,
    ( k1_xboole_0 != sK0
    | spl4_9 ),
    inference(avatar_component_clause,[],[f79])).

fof(f65,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl4_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f58,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl4_6
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f38,plain,
    ( v2_funct_1(sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl4_2
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f33,plain,
    ( v1_funct_1(sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl4_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f98,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | spl4_9 ),
    inference(forward_demodulation,[],[f87,f70])).

fof(f70,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl4_8
  <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f87,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | spl4_9 ),
    inference(unit_resulting_resolution,[],[f48,f58,f65,f80,f75])).

fof(f75,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(sK1,X2,X0)
        | ~ r2_hidden(X1,X2)
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X1)) = X1
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | k1_xboole_0 = X0 )
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f74,f33])).

fof(f74,plain,
    ( ! [X2,X0,X1] :
        ( k1_xboole_0 = X0
        | ~ r2_hidden(X1,X2)
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X1)) = X1
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ v1_funct_2(sK1,X2,X0)
        | ~ v1_funct_1(sK1) )
    | ~ spl4_2 ),
    inference(resolution,[],[f27,f38])).

fof(f97,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | spl4_9 ),
    inference(avatar_contradiction_clause,[],[f96])).

fof(f96,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | spl4_9 ),
    inference(subsumption_resolution,[],[f95,f53])).

fof(f95,plain,
    ( sK2 = sK3
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | spl4_9 ),
    inference(backward_demodulation,[],[f94,f88])).

fof(f94,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | spl4_9 ),
    inference(forward_demodulation,[],[f89,f70])).

fof(f89,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | spl4_9 ),
    inference(unit_resulting_resolution,[],[f33,f38,f48,f58,f65,f80,f27])).

fof(f85,plain,
    ( spl4_9
    | spl4_10
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f77,f63,f56,f36,f31,f83,f79])).

fof(f83,plain,
    ( spl4_10
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f77,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0
        | k1_xboole_0 = sK0 )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f76,f65])).

fof(f76,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0 )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(resolution,[],[f75,f58])).

fof(f71,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f21,f68])).

fof(f21,plain,(
    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( sK2 != sK3
    & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    & r2_hidden(sK3,sK0)
    & r2_hidden(sK2,sK0)
    & v2_funct_1(sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f11,f10])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        & v2_funct_1(X1)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X3,X2] :
          ( X2 != X3
          & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3)
          & r2_hidden(X3,sK0)
          & r2_hidden(X2,sK0) )
      & v2_funct_1(sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ? [X3,X2] :
        ( X2 != X3
        & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3)
        & r2_hidden(X3,sK0)
        & r2_hidden(X2,sK0) )
   => ( sK2 != sK3
      & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
      & r2_hidden(sK3,sK0)
      & r2_hidden(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
         => ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_2)).

fof(f66,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f17,f63])).

fof(f17,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f59,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f16,f56])).

fof(f16,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f54,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f22,f51])).

fof(f22,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f12])).

fof(f49,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f20,f46])).

fof(f20,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f44,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f19,f41])).

fof(f19,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f39,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f18,f36])).

fof(f18,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f34,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f15,f31])).

fof(f15,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:06:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.42  % (16856)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.47  % (16849)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.47  % (16856)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f111,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f34,f39,f44,f49,f54,f59,f66,f71,f85,f97,f101,f107,f109])).
% 0.22/0.47  fof(f109,plain,(
% 0.22/0.47    ~spl4_4 | ~spl4_9),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f108])).
% 0.22/0.47  fof(f108,plain,(
% 0.22/0.47    $false | (~spl4_4 | ~spl4_9)),
% 0.22/0.47    inference(subsumption_resolution,[],[f103,f60])).
% 0.22/0.47  fof(f60,plain,(
% 0.22/0.47    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.47    inference(superposition,[],[f23,f28])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.47    inference(equality_resolution,[],[f26])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.22/0.47    inference(flattening,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.22/0.47    inference(nnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.22/0.48  fof(f103,plain,(
% 0.22/0.48    r2_hidden(sK3,k1_xboole_0) | (~spl4_4 | ~spl4_9)),
% 0.22/0.48    inference(backward_demodulation,[],[f48,f81])).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    k1_xboole_0 = sK0 | ~spl4_9),
% 0.22/0.48    inference(avatar_component_clause,[],[f79])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    spl4_9 <=> k1_xboole_0 = sK0),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    r2_hidden(sK3,sK0) | ~spl4_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f46])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    spl4_4 <=> r2_hidden(sK3,sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.48  fof(f107,plain,(
% 0.22/0.48    ~spl4_3 | ~spl4_9),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f106])).
% 0.22/0.48  fof(f106,plain,(
% 0.22/0.48    $false | (~spl4_3 | ~spl4_9)),
% 0.22/0.48    inference(subsumption_resolution,[],[f102,f60])).
% 0.22/0.48  fof(f102,plain,(
% 0.22/0.48    r2_hidden(sK2,k1_xboole_0) | (~spl4_3 | ~spl4_9)),
% 0.22/0.48    inference(backward_demodulation,[],[f43,f81])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    r2_hidden(sK2,sK0) | ~spl4_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f41])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    spl4_3 <=> r2_hidden(sK2,sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.48  fof(f101,plain,(
% 0.22/0.48    ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_8 | spl4_9),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f100])).
% 0.22/0.48  fof(f100,plain,(
% 0.22/0.48    $false | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_8 | spl4_9)),
% 0.22/0.48    inference(subsumption_resolution,[],[f99,f53])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    sK2 != sK3 | spl4_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f51])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    spl4_5 <=> sK2 = sK3),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.48  fof(f99,plain,(
% 0.22/0.48    sK2 = sK3 | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_8 | spl4_9)),
% 0.22/0.48    inference(forward_demodulation,[],[f98,f88])).
% 0.22/0.48  fof(f88,plain,(
% 0.22/0.48    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_6 | ~spl4_7 | spl4_9)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f33,f38,f43,f58,f65,f80,f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~v2_funct_1(X3) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.48    inference(flattening,[],[f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    k1_xboole_0 != sK0 | spl4_9),
% 0.22/0.48    inference(avatar_component_clause,[],[f79])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_7),
% 0.22/0.48    inference(avatar_component_clause,[],[f63])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    spl4_7 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    v1_funct_2(sK1,sK0,sK0) | ~spl4_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f56])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    spl4_6 <=> v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    v2_funct_1(sK1) | ~spl4_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    spl4_2 <=> v2_funct_1(sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    v1_funct_1(sK1) | ~spl4_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    spl4_1 <=> v1_funct_1(sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.48  fof(f98,plain,(
% 0.22/0.48    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_8 | spl4_9)),
% 0.22/0.48    inference(forward_demodulation,[],[f87,f70])).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | ~spl4_8),
% 0.22/0.48    inference(avatar_component_clause,[],[f68])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    spl4_8 <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.48  fof(f87,plain,(
% 0.22/0.48    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) | (~spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_7 | spl4_9)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f48,f58,f65,f80,f75])).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v1_funct_2(sK1,X2,X0) | ~r2_hidden(X1,X2) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X1)) = X1 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0) ) | (~spl4_1 | ~spl4_2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f74,f33])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r2_hidden(X1,X2) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X1)) = X1 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_2(sK1,X2,X0) | ~v1_funct_1(sK1)) ) | ~spl4_2),
% 0.22/0.48    inference(resolution,[],[f27,f38])).
% 0.22/0.48  fof(f97,plain,(
% 0.22/0.48    ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_8 | spl4_9),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f96])).
% 0.22/0.48  fof(f96,plain,(
% 0.22/0.48    $false | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_8 | spl4_9)),
% 0.22/0.48    inference(subsumption_resolution,[],[f95,f53])).
% 0.22/0.48  fof(f95,plain,(
% 0.22/0.48    sK2 = sK3 | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_8 | spl4_9)),
% 0.22/0.48    inference(backward_demodulation,[],[f94,f88])).
% 0.22/0.48  fof(f94,plain,(
% 0.22/0.48    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_8 | spl4_9)),
% 0.22/0.48    inference(forward_demodulation,[],[f89,f70])).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) | (~spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_7 | spl4_9)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f33,f38,f48,f58,f65,f80,f27])).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    spl4_9 | spl4_10 | ~spl4_1 | ~spl4_2 | ~spl4_6 | ~spl4_7),
% 0.22/0.48    inference(avatar_split_clause,[],[f77,f63,f56,f36,f31,f83,f79])).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    spl4_10 <=> ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 | k1_xboole_0 = sK0) ) | (~spl4_1 | ~spl4_2 | ~spl4_6 | ~spl4_7)),
% 0.22/0.48    inference(subsumption_resolution,[],[f76,f65])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_xboole_0 = sK0) ) | (~spl4_1 | ~spl4_2 | ~spl4_6)),
% 0.22/0.48    inference(resolution,[],[f75,f58])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    spl4_8),
% 0.22/0.48    inference(avatar_split_clause,[],[f21,f68])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    (sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0)) & v2_funct_1(sK1) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f11,f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) & v2_funct_1(sK1) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) => (sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f7,plain,(
% 0.22/0.48    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.22/0.48    inference(flattening,[],[f6])).
% 0.22/0.48  fof(f6,plain,(
% 0.22/0.48    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & (k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0))) & v2_funct_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.22/0.48    inference(negated_conjecture,[],[f4])).
% 0.22/0.48  fof(f4,conjecture,(
% 0.22/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_2)).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    spl4_7),
% 0.22/0.48    inference(avatar_split_clause,[],[f17,f63])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    spl4_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f16,f56])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    ~spl4_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f22,f51])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    sK2 != sK3),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    spl4_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f20,f46])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    r2_hidden(sK3,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    spl4_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f19,f41])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    r2_hidden(sK2,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    spl4_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f18,f36])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    v2_funct_1(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    spl4_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f15,f31])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    v1_funct_1(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (16856)------------------------------
% 0.22/0.48  % (16856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (16856)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (16856)Memory used [KB]: 1663
% 0.22/0.48  % (16856)Time elapsed: 0.061 s
% 0.22/0.48  % (16856)------------------------------
% 0.22/0.48  % (16856)------------------------------
% 0.22/0.48  % (16853)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.48  % (16848)Success in time 0.116 s
%------------------------------------------------------------------------------
