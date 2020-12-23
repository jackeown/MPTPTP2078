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
% DateTime   : Thu Dec  3 13:08:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 (  99 expanded)
%              Number of leaves         :   10 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  185 ( 354 expanded)
%              Number of equality atoms :   25 (  50 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f85,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f24,f32,f37,f42,f49,f67,f78,f84])).

fof(f84,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_8 ),
    inference(avatar_contradiction_clause,[],[f83])).

fof(f83,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_8 ),
    inference(subsumption_resolution,[],[f82,f41])).

fof(f41,plain,
    ( r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl5_4
  <=> r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f82,plain,
    ( ~ r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | spl5_8 ),
    inference(forward_demodulation,[],[f81,f48])).

fof(f48,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl5_5
  <=> k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f81,plain,
    ( ~ r2_hidden(sK0,k7_relset_1(sK1,sK2,sK3,sK1))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_8 ),
    inference(resolution,[],[f77,f56])).

fof(f56,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK4(sK1,X1,sK3,X0),sK1)
        | ~ r2_hidden(X0,k7_relset_1(sK1,sK2,sK3,X1)) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f55,f31])).

fof(f31,plain,
    ( v1_funct_2(sK3,sK1,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl5_2
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f55,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK3,sK1,sK2)
        | ~ r2_hidden(X0,k7_relset_1(sK1,sK2,sK3,X1))
        | m1_subset_1(sK4(sK1,X1,sK3,X0),sK1) )
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(resolution,[],[f25,f36])).

fof(f36,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl5_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f25,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK3,X0,X1)
        | ~ r2_hidden(X2,k7_relset_1(X0,X1,sK3,X3))
        | m1_subset_1(sK4(X0,X3,sK3,X2),X0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f23,f17])).

fof(f17,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
      | m1_subset_1(sK4(X0,X2,X3,X4),X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & m1_subset_1(X5,X0) )
          | ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & m1_subset_1(X5,X0) )
          | ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2) ) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

fof(f23,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f21])).

fof(f21,plain,
    ( spl5_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f77,plain,
    ( ~ m1_subset_1(sK4(sK1,sK1,sK3,sK0),sK1)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl5_8
  <=> m1_subset_1(sK4(sK1,sK1,sK3,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f78,plain,
    ( ~ spl5_8
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f71,f64,f75])).

fof(f64,plain,
    ( spl5_7
  <=> sK0 = k1_funct_1(sK3,sK4(sK1,sK1,sK3,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f71,plain,
    ( ~ m1_subset_1(sK4(sK1,sK1,sK3,sK0),sK1)
    | ~ spl5_7 ),
    inference(trivial_inequality_removal,[],[f70])).

fof(f70,plain,
    ( sK0 != sK0
    | ~ m1_subset_1(sK4(sK1,sK1,sK3,sK0),sK1)
    | ~ spl5_7 ),
    inference(superposition,[],[f10,f66])).

fof(f66,plain,
    ( sK0 = k1_funct_1(sK3,sK4(sK1,sK1,sK3,sK0))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f64])).

fof(f10,plain,(
    ! [X4] :
      ( sK0 != k1_funct_1(sK3,X4)
      | ~ m1_subset_1(X4,sK1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

fof(f67,plain,
    ( spl5_7
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f61,f46,f39,f34,f29,f21,f64])).

fof(f61,plain,
    ( sK0 = k1_funct_1(sK3,sK4(sK1,sK1,sK3,sK0))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(resolution,[],[f60,f41])).

fof(f60,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relset_1(sK1,sK2,sK3))
        | k1_funct_1(sK3,sK4(sK1,sK1,sK3,X0)) = X0 )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(superposition,[],[f58,f48])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k7_relset_1(sK1,sK2,sK3,X1))
        | k1_funct_1(sK3,sK4(sK1,X1,sK3,X0)) = X0 )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f57,f31])).

fof(f57,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK3,sK1,sK2)
        | ~ r2_hidden(X0,k7_relset_1(sK1,sK2,sK3,X1))
        | k1_funct_1(sK3,sK4(sK1,X1,sK3,X0)) = X0 )
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(resolution,[],[f27,f36])).

fof(f27,plain,
    ( ! [X10,X8,X11,X9] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | ~ v1_funct_2(sK3,X8,X9)
        | ~ r2_hidden(X10,k7_relset_1(X8,X9,sK3,X11))
        | k1_funct_1(sK3,sK4(X8,X11,sK3,X10)) = X10 )
    | ~ spl5_1 ),
    inference(resolution,[],[f23,f19])).

fof(f19,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
      | k1_funct_1(X3,sK4(X0,X2,X3,X4)) = X4 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f49,plain,
    ( spl5_5
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f43,f34,f46])).

fof(f43,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1)
    | ~ spl5_3 ),
    inference(resolution,[],[f36,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f42,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f14,f39])).

fof(f14,plain,(
    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f6])).

fof(f37,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f13,f34])).

fof(f13,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f6])).

fof(f32,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f12,f29])).

fof(f12,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f24,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f11,f21])).

fof(f11,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:15:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.45  % (20520)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % (20520)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (20533)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f24,f32,f37,f42,f49,f67,f78,f84])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    ~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | spl5_8),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f83])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    $false | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | spl5_8)),
% 0.21/0.48    inference(subsumption_resolution,[],[f82,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) | ~spl5_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    spl5_4 <=> r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    ~r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5 | spl5_8)),
% 0.21/0.48    inference(forward_demodulation,[],[f81,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1) | ~spl5_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    spl5_5 <=> k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ~r2_hidden(sK0,k7_relset_1(sK1,sK2,sK3,sK1)) | (~spl5_1 | ~spl5_2 | ~spl5_3 | spl5_8)),
% 0.21/0.48    inference(resolution,[],[f77,f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(sK4(sK1,X1,sK3,X0),sK1) | ~r2_hidden(X0,k7_relset_1(sK1,sK2,sK3,X1))) ) | (~spl5_1 | ~spl5_2 | ~spl5_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f55,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    v1_funct_2(sK3,sK1,sK2) | ~spl5_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    spl5_2 <=> v1_funct_2(sK3,sK1,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_funct_2(sK3,sK1,sK2) | ~r2_hidden(X0,k7_relset_1(sK1,sK2,sK3,X1)) | m1_subset_1(sK4(sK1,X1,sK3,X0),sK1)) ) | (~spl5_1 | ~spl5_3)),
% 0.21/0.48    inference(resolution,[],[f25,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    spl5_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK3,X0,X1) | ~r2_hidden(X2,k7_relset_1(X0,X1,sK3,X3)) | m1_subset_1(sK4(X0,X3,sK3,X2),X0)) ) | ~spl5_1),
% 0.21/0.48    inference(resolution,[],[f23,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) | m1_subset_1(sK4(X0,X2,X3,X4),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (! [X4] : (? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & m1_subset_1(X5,X0)) | ~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.48    inference(flattening,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (! [X4] : (? [X5] : ((k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2)) & m1_subset_1(X5,X0)) | ~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    v1_funct_1(sK3) | ~spl5_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    spl5_1 <=> v1_funct_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    ~m1_subset_1(sK4(sK1,sK1,sK3,sK0),sK1) | spl5_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f75])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    spl5_8 <=> m1_subset_1(sK4(sK1,sK1,sK3,sK0),sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    ~spl5_8 | ~spl5_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f71,f64,f75])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    spl5_7 <=> sK0 = k1_funct_1(sK3,sK4(sK1,sK1,sK3,sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ~m1_subset_1(sK4(sK1,sK1,sK3,sK0),sK1) | ~spl5_7),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f70])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    sK0 != sK0 | ~m1_subset_1(sK4(sK1,sK1,sK3,sK0),sK1) | ~spl5_7),
% 0.21/0.48    inference(superposition,[],[f10,f66])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    sK0 = k1_funct_1(sK3,sK4(sK1,sK1,sK3,sK0)) | ~spl5_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f64])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ( ! [X4] : (sK0 != k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))),
% 0.21/0.48    inference(flattening,[],[f5])).
% 0.21/0.48  fof(f5,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.21/0.48    inference(negated_conjecture,[],[f3])).
% 0.21/0.48  fof(f3,conjecture,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    spl5_7 | ~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f61,f46,f39,f34,f29,f21,f64])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    sK0 = k1_funct_1(sK3,sK4(sK1,sK1,sK3,sK0)) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.48    inference(resolution,[],[f60,f41])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,k2_relset_1(sK1,sK2,sK3)) | k1_funct_1(sK3,sK4(sK1,sK1,sK3,X0)) = X0) ) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5)),
% 0.21/0.48    inference(superposition,[],[f58,f48])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X0,k7_relset_1(sK1,sK2,sK3,X1)) | k1_funct_1(sK3,sK4(sK1,X1,sK3,X0)) = X0) ) | (~spl5_1 | ~spl5_2 | ~spl5_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f57,f31])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_funct_2(sK3,sK1,sK2) | ~r2_hidden(X0,k7_relset_1(sK1,sK2,sK3,X1)) | k1_funct_1(sK3,sK4(sK1,X1,sK3,X0)) = X0) ) | (~spl5_1 | ~spl5_3)),
% 0.21/0.48    inference(resolution,[],[f27,f36])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X10,X8,X11,X9] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_2(sK3,X8,X9) | ~r2_hidden(X10,k7_relset_1(X8,X9,sK3,X11)) | k1_funct_1(sK3,sK4(X8,X11,sK3,X10)) = X10) ) | ~spl5_1),
% 0.21/0.48    inference(resolution,[],[f23,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) | k1_funct_1(X3,sK4(X0,X2,X3,X4)) = X4) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    spl5_5 | ~spl5_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f43,f34,f46])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1) | ~spl5_3),
% 0.21/0.48    inference(resolution,[],[f36,f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    spl5_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f14,f39])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    spl5_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f13,f34])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    spl5_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f12,f29])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    v1_funct_2(sK3,sK1,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    spl5_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f11,f21])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    v1_funct_1(sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (20520)------------------------------
% 0.21/0.48  % (20520)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (20520)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (20520)Memory used [KB]: 10618
% 0.21/0.48  % (20520)Time elapsed: 0.055 s
% 0.21/0.48  % (20520)------------------------------
% 0.21/0.48  % (20520)------------------------------
% 0.21/0.48  % (20514)Success in time 0.121 s
%------------------------------------------------------------------------------
