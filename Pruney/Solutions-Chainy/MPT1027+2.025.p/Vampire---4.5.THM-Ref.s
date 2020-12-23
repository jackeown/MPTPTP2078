%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 (1117 expanded)
%              Number of leaves         :    9 ( 267 expanded)
%              Depth                    :   22
%              Number of atoms          :  219 (5883 expanded)
%              Number of equality atoms :   67 (1797 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f125,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f45,f113,f124])).

fof(f124,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f123])).

fof(f123,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f122,f120])).

fof(f120,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f17,f119])).

fof(f119,plain,(
    k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f19,f16,f17,f118])).

fof(f118,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f64,f17])).

fof(f64,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(trivial_inequality_removal,[],[f63])).

fof(f63,plain,
    ( sK0 != sK0
    | v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f25,f18])).

fof(f18,plain,(
    sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) )
    & sK0 = k1_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & k1_relset_1(X0,X1,X2) = X0
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
      & sK0 = k1_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & k1_relset_1(X0,X1,X2) = X0
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & k1_relset_1(X0,X1,X2) = X0
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ( k1_relset_1(X0,X1,X2) = X0
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X2,X0,X1)
            & v1_funct_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( k1_relset_1(X0,X1,X2) = X0
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_funct_2)).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f16,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f19,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f17,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f122,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | spl3_3 ),
    inference(forward_demodulation,[],[f42,f119])).

fof(f42,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f113,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f111,f95])).

fof(f95,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl3_2 ),
    inference(backward_demodulation,[],[f79,f91])).

% (20381)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f91,plain,
    ( k1_xboole_0 = sK0
    | spl3_2 ),
    inference(subsumption_resolution,[],[f85,f80])).

fof(f80,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | spl3_2 ),
    inference(forward_demodulation,[],[f68,f75])).

fof(f75,plain,
    ( k1_xboole_0 = sK2
    | spl3_2 ),
    inference(subsumption_resolution,[],[f74,f20])).

fof(f20,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f74,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK2
    | spl3_2 ),
    inference(forward_demodulation,[],[f73,f66])).

fof(f66,plain,
    ( k1_xboole_0 = sK1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f65,f17])).

fof(f65,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl3_2 ),
    inference(subsumption_resolution,[],[f64,f39])).

fof(f39,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl3_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f73,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_xboole_0(sK1)
    | spl3_2 ),
    inference(forward_demodulation,[],[f61,f66])).

fof(f61,plain,
    ( sK1 = sK2
    | ~ v1_xboole_0(sK1) ),
    inference(resolution,[],[f58,f17])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(global_subsumption,[],[f22,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f21,f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f68,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | spl3_2 ),
    inference(backward_demodulation,[],[f39,f66])).

fof(f85,plain,
    ( k1_xboole_0 = sK0
    | v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | spl3_2 ),
    inference(resolution,[],[f79,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f79,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | spl3_2 ),
    inference(forward_demodulation,[],[f69,f75])).

fof(f69,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | spl3_2 ),
    inference(backward_demodulation,[],[f17,f66])).

fof(f111,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl3_2 ),
    inference(subsumption_resolution,[],[f110,f94])).

fof(f94,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl3_2 ),
    inference(backward_demodulation,[],[f80,f91])).

fof(f110,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl3_2 ),
    inference(trivial_inequality_removal,[],[f108])).

fof(f108,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl3_2 ),
    inference(superposition,[],[f32,f96])).

fof(f96,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl3_2 ),
    inference(backward_demodulation,[],[f78,f91])).

fof(f78,plain,
    ( sK0 = k1_relset_1(sK0,k1_xboole_0,k1_xboole_0)
    | spl3_2 ),
    inference(forward_demodulation,[],[f70,f75])).

fof(f70,plain,
    ( sK0 = k1_relset_1(sK0,k1_xboole_0,sK2)
    | spl3_2 ),
    inference(backward_demodulation,[],[f18,f66])).

fof(f32,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f45,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f44])).

fof(f44,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f36,f16])).

fof(f36,plain,
    ( ~ v1_funct_1(sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f43,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f19,f41,f38,f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:48:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (20368)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.46  % (20370)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.47  % (20368)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (20384)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f125,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f43,f45,f113,f124])).
% 0.20/0.47  fof(f124,plain,(
% 0.20/0.47    spl3_3),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f123])).
% 0.20/0.47  fof(f123,plain,(
% 0.20/0.47    $false | spl3_3),
% 0.20/0.47    inference(subsumption_resolution,[],[f122,f120])).
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.20/0.47    inference(backward_demodulation,[],[f17,f119])).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    k1_xboole_0 = sK1),
% 0.20/0.47    inference(global_subsumption,[],[f19,f16,f17,f118])).
% 0.20/0.47  fof(f118,plain,(
% 0.20/0.47    v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1),
% 0.20/0.47    inference(subsumption_resolution,[],[f64,f17])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f63])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    sK0 != sK0 | v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.47    inference(superposition,[],[f25,f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) & sK0 = k1_relset_1(sK0,sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & k1_relset_1(X0,X1,X2) = X0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) & sK0 = k1_relset_1(sK0,sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & k1_relset_1(X0,X1,X2) = X0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.20/0.47    inference(flattening,[],[f7])).
% 0.20/0.47  fof(f7,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & k1_relset_1(X0,X1,X2) = X0) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.20/0.47    inference(negated_conjecture,[],[f5])).
% 0.20/0.47  fof(f5,conjecture,(
% 0.20/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_funct_2)).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(nnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(flattening,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    v1_funct_1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f122,plain,(
% 0.20/0.47    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | spl3_3),
% 0.20/0.47    inference(forward_demodulation,[],[f42,f119])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl3_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f41])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.47  fof(f113,plain,(
% 0.20/0.47    spl3_2),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f112])).
% 0.20/0.47  fof(f112,plain,(
% 0.20/0.47    $false | spl3_2),
% 0.20/0.47    inference(subsumption_resolution,[],[f111,f95])).
% 0.20/0.47  fof(f95,plain,(
% 0.20/0.47    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | spl3_2),
% 0.20/0.47    inference(backward_demodulation,[],[f79,f91])).
% 0.20/0.47  % (20381)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.47  fof(f91,plain,(
% 0.20/0.47    k1_xboole_0 = sK0 | spl3_2),
% 0.20/0.47    inference(subsumption_resolution,[],[f85,f80])).
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    ~v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | spl3_2),
% 0.20/0.47    inference(forward_demodulation,[],[f68,f75])).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    k1_xboole_0 = sK2 | spl3_2),
% 0.20/0.47    inference(subsumption_resolution,[],[f74,f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = sK2 | spl3_2),
% 0.20/0.47    inference(forward_demodulation,[],[f73,f66])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    k1_xboole_0 = sK1 | spl3_2),
% 0.20/0.47    inference(subsumption_resolution,[],[f65,f17])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl3_2),
% 0.20/0.47    inference(subsumption_resolution,[],[f64,f39])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ~v1_funct_2(sK2,sK0,sK1) | spl3_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f38])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    spl3_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    k1_xboole_0 = sK2 | ~v1_xboole_0(sK1) | spl3_2),
% 0.20/0.47    inference(forward_demodulation,[],[f61,f66])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    sK1 = sK2 | ~v1_xboole_0(sK1)),
% 0.20/0.47    inference(resolution,[],[f58,f17])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.20/0.47    inference(global_subsumption,[],[f22,f46])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ( ! [X0,X1] : (X0 = X1 | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 0.20/0.47    inference(superposition,[],[f21,f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    ~v1_funct_2(sK2,sK0,k1_xboole_0) | spl3_2),
% 0.20/0.47    inference(backward_demodulation,[],[f39,f66])).
% 0.20/0.47  fof(f85,plain,(
% 0.20/0.47    k1_xboole_0 = sK0 | v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | spl3_2),
% 0.20/0.47    inference(resolution,[],[f79,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)) )),
% 0.20/0.47    inference(equality_resolution,[],[f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.47    inference(equality_resolution,[],[f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | spl3_2),
% 0.20/0.47    inference(forward_demodulation,[],[f69,f75])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | spl3_2),
% 0.20/0.47    inference(backward_demodulation,[],[f17,f66])).
% 0.20/0.47  fof(f111,plain,(
% 0.20/0.47    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | spl3_2),
% 0.20/0.47    inference(subsumption_resolution,[],[f110,f94])).
% 0.20/0.47  fof(f94,plain,(
% 0.20/0.47    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | spl3_2),
% 0.20/0.47    inference(backward_demodulation,[],[f80,f91])).
% 0.20/0.47  fof(f110,plain,(
% 0.20/0.47    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | spl3_2),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f108])).
% 0.20/0.47  fof(f108,plain,(
% 0.20/0.47    k1_xboole_0 != k1_xboole_0 | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | spl3_2),
% 0.20/0.47    inference(superposition,[],[f32,f96])).
% 0.20/0.47  fof(f96,plain,(
% 0.20/0.47    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | spl3_2),
% 0.20/0.47    inference(backward_demodulation,[],[f78,f91])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    sK0 = k1_relset_1(sK0,k1_xboole_0,k1_xboole_0) | spl3_2),
% 0.20/0.47    inference(forward_demodulation,[],[f70,f75])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    sK0 = k1_relset_1(sK0,k1_xboole_0,sK2) | spl3_2),
% 0.20/0.47    inference(backward_demodulation,[],[f18,f66])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.20/0.47    inference(equality_resolution,[],[f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    spl3_1),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f44])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    $false | spl3_1),
% 0.20/0.47    inference(subsumption_resolution,[],[f36,f16])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ~v1_funct_1(sK2) | spl3_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    spl3_1 <=> v1_funct_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f19,f41,f38,f35])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (20368)------------------------------
% 0.20/0.47  % (20368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (20368)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (20368)Memory used [KB]: 10618
% 0.20/0.47  % (20368)Time elapsed: 0.066 s
% 0.20/0.47  % (20368)------------------------------
% 0.20/0.47  % (20368)------------------------------
% 0.20/0.47  % (20363)Success in time 0.119 s
%------------------------------------------------------------------------------
