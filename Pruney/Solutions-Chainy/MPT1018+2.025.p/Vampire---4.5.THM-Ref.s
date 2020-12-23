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
% DateTime   : Thu Dec  3 13:05:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 173 expanded)
%              Number of leaves         :   14 (  60 expanded)
%              Depth                    :   11
%              Number of atoms          :  230 (1032 expanded)
%              Number of equality atoms :   52 ( 278 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f176,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f83,f108,f123,f149,f162,f175])).

fof(f175,plain,
    ( ~ spl4_4
    | ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(resolution,[],[f164,f152])).

fof(f152,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f25,f64])).

fof(f64,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f25,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( sK2 != sK3
    & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    & r2_hidden(sK3,sK0)
    & r2_hidden(sK2,sK0)
    & v2_funct_1(sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f19,f18])).

fof(f18,plain,
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

fof(f19,plain,
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

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_2)).

fof(f164,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f118,f64])).

fof(f118,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl4_11
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f162,plain,
    ( ~ spl4_4
    | spl4_12 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | ~ spl4_4
    | spl4_12 ),
    inference(subsumption_resolution,[],[f160,f34])).

fof(f34,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f160,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_4
    | spl4_12 ),
    inference(backward_demodulation,[],[f122,f64])).

fof(f122,plain,
    ( ~ v1_xboole_0(sK0)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl4_12
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f149,plain,(
    ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f147,f28])).

fof(f28,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f20])).

fof(f147,plain,
    ( sK2 = sK3
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f128,f126])).

fof(f126,plain,
    ( sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl4_5 ),
    inference(resolution,[],[f67,f25])).

fof(f67,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl4_5
  <=> ! [X0] :
        ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f128,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f127,f27])).

fof(f27,plain,(
    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f127,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))
    | ~ spl4_5 ),
    inference(resolution,[],[f67,f26])).

fof(f26,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f123,plain,
    ( spl4_11
    | ~ spl4_12
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f115,f71,f120,f117])).

fof(f71,plain,
    ( spl4_6
  <=> sK0 = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f115,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(sK0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl4_6 ),
    inference(resolution,[],[f113,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f113,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f110,f23])).

fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f110,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_6 ),
    inference(superposition,[],[f33,f73])).

fof(f73,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f71])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f108,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f107])).

fof(f107,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f60,f23])).

fof(f60,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f83,plain,
    ( spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f82,f66,f62])).

fof(f82,plain,(
    ! [X0] :
      ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0
      | k1_xboole_0 = sK0
      | ~ r2_hidden(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f81,f21])).

fof(f21,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f81,plain,(
    ! [X0] :
      ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0
      | k1_xboole_0 = sK0
      | ~ r2_hidden(X0,sK0)
      | ~ v1_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f80,f22])).

fof(f22,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f80,plain,(
    ! [X0] :
      ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0
      | k1_xboole_0 = sK0
      | ~ r2_hidden(X0,sK0)
      | ~ v1_funct_2(sK1,sK0,sK0)
      | ~ v1_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f77,f24])).

fof(f24,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f77,plain,(
    ! [X0] :
      ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0
      | k1_xboole_0 = sK0
      | ~ r2_hidden(X0,sK0)
      | ~ v2_funct_1(sK1)
      | ~ v1_funct_2(sK1,sK0,sK0)
      | ~ v1_funct_1(sK1) ) ),
    inference(resolution,[],[f23,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

fof(f74,plain,
    ( ~ spl4_3
    | spl4_6 ),
    inference(avatar_split_clause,[],[f69,f71,f58])).

fof(f69,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f54,f21])).

fof(f54,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f22,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:07:55 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.44  % (31146)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.44  % (31146)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f176,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f74,f83,f108,f123,f149,f162,f175])).
% 0.21/0.44  fof(f175,plain,(
% 0.21/0.44    ~spl4_4 | ~spl4_11),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f171])).
% 0.21/0.44  fof(f171,plain,(
% 0.21/0.44    $false | (~spl4_4 | ~spl4_11)),
% 0.21/0.44    inference(resolution,[],[f164,f152])).
% 0.21/0.44  fof(f152,plain,(
% 0.21/0.44    r2_hidden(sK2,k1_xboole_0) | ~spl4_4),
% 0.21/0.44    inference(backward_demodulation,[],[f25,f64])).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    k1_xboole_0 = sK0 | ~spl4_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f62])).
% 0.21/0.44  fof(f62,plain,(
% 0.21/0.44    spl4_4 <=> k1_xboole_0 = sK0),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    r2_hidden(sK2,sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    (sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0)) & v2_funct_1(sK1) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f19,f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) & v2_funct_1(sK1) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) => (sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.21/0.44    inference(flattening,[],[f9])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & (k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0))) & v2_funct_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.21/0.44    inference(ennf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.21/0.44    inference(negated_conjecture,[],[f7])).
% 0.21/0.44  fof(f7,conjecture,(
% 0.21/0.44    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_2)).
% 0.21/0.44  fof(f164,plain,(
% 0.21/0.44    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl4_4 | ~spl4_11)),
% 0.21/0.44    inference(forward_demodulation,[],[f118,f64])).
% 0.21/0.44  fof(f118,plain,(
% 0.21/0.44    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl4_11),
% 0.21/0.44    inference(avatar_component_clause,[],[f117])).
% 0.21/0.44  fof(f117,plain,(
% 0.21/0.44    spl4_11 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.44  fof(f162,plain,(
% 0.21/0.44    ~spl4_4 | spl4_12),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f161])).
% 0.21/0.44  fof(f161,plain,(
% 0.21/0.44    $false | (~spl4_4 | spl4_12)),
% 0.21/0.44    inference(subsumption_resolution,[],[f160,f34])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    v1_xboole_0(k1_xboole_0)),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    v1_xboole_0(k1_xboole_0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.44  fof(f160,plain,(
% 0.21/0.44    ~v1_xboole_0(k1_xboole_0) | (~spl4_4 | spl4_12)),
% 0.21/0.44    inference(backward_demodulation,[],[f122,f64])).
% 0.21/0.44  fof(f122,plain,(
% 0.21/0.44    ~v1_xboole_0(sK0) | spl4_12),
% 0.21/0.44    inference(avatar_component_clause,[],[f120])).
% 0.21/0.44  fof(f120,plain,(
% 0.21/0.44    spl4_12 <=> v1_xboole_0(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.44  fof(f149,plain,(
% 0.21/0.44    ~spl4_5),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f148])).
% 0.21/0.44  fof(f148,plain,(
% 0.21/0.44    $false | ~spl4_5),
% 0.21/0.44    inference(subsumption_resolution,[],[f147,f28])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    sK2 != sK3),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f147,plain,(
% 0.21/0.44    sK2 = sK3 | ~spl4_5),
% 0.21/0.44    inference(forward_demodulation,[],[f128,f126])).
% 0.21/0.44  fof(f126,plain,(
% 0.21/0.44    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~spl4_5),
% 0.21/0.44    inference(resolution,[],[f67,f25])).
% 0.21/0.44  fof(f67,plain,(
% 0.21/0.44    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) ) | ~spl4_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f66])).
% 0.21/0.44  fof(f66,plain,(
% 0.21/0.44    spl4_5 <=> ! [X0] : (k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 | ~r2_hidden(X0,sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.44  fof(f128,plain,(
% 0.21/0.44    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~spl4_5),
% 0.21/0.44    inference(forward_demodulation,[],[f127,f27])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f127,plain,(
% 0.21/0.44    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) | ~spl4_5),
% 0.21/0.44    inference(resolution,[],[f67,f26])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    r2_hidden(sK3,sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f123,plain,(
% 0.21/0.44    spl4_11 | ~spl4_12 | ~spl4_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f115,f71,f120,f117])).
% 0.21/0.44  fof(f71,plain,(
% 0.21/0.44    spl4_6 <=> sK0 = k1_relset_1(sK0,sK0,sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.44  fof(f115,plain,(
% 0.21/0.44    ( ! [X0] : (~v1_xboole_0(sK0) | ~r2_hidden(X0,sK0)) ) | ~spl4_6),
% 0.21/0.44    inference(resolution,[],[f113,f32])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.44  fof(f113,plain,(
% 0.21/0.44    m1_subset_1(sK0,k1_zfmisc_1(sK0)) | ~spl4_6),
% 0.21/0.44    inference(subsumption_resolution,[],[f110,f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f110,plain,(
% 0.21/0.44    m1_subset_1(sK0,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_6),
% 0.21/0.44    inference(superposition,[],[f33,f73])).
% 0.21/0.44  fof(f73,plain,(
% 0.21/0.44    sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl4_6),
% 0.21/0.44    inference(avatar_component_clause,[],[f71])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.21/0.44  fof(f108,plain,(
% 0.21/0.44    spl4_3),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f107])).
% 0.21/0.44  fof(f107,plain,(
% 0.21/0.44    $false | spl4_3),
% 0.21/0.44    inference(subsumption_resolution,[],[f60,f23])).
% 0.21/0.44  fof(f60,plain,(
% 0.21/0.44    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f58])).
% 0.21/0.44  fof(f58,plain,(
% 0.21/0.44    spl4_3 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.44  fof(f83,plain,(
% 0.21/0.44    spl4_4 | spl4_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f82,f66,f62])).
% 0.21/0.44  fof(f82,plain,(
% 0.21/0.44    ( ! [X0] : (k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 | k1_xboole_0 = sK0 | ~r2_hidden(X0,sK0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f81,f21])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    v1_funct_1(sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f81,plain,(
% 0.21/0.44    ( ! [X0] : (k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 | k1_xboole_0 = sK0 | ~r2_hidden(X0,sK0) | ~v1_funct_1(sK1)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f80,f22])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f80,plain,(
% 0.21/0.44    ( ! [X0] : (k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 | k1_xboole_0 = sK0 | ~r2_hidden(X0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f77,f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    v2_funct_1(sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f77,plain,(
% 0.21/0.44    ( ! [X0] : (k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 | k1_xboole_0 = sK0 | ~r2_hidden(X0,sK0) | ~v2_funct_1(sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)) )),
% 0.21/0.44    inference(resolution,[],[f23,f29])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.44    inference(flattening,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).
% 0.21/0.44  fof(f74,plain,(
% 0.21/0.44    ~spl4_3 | spl4_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f69,f71,f58])).
% 0.21/0.44  fof(f69,plain,(
% 0.21/0.44    sK0 = k1_relset_1(sK0,sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.44    inference(subsumption_resolution,[],[f54,f21])).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    sK0 = k1_relset_1(sK0,sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1)),
% 0.21/0.44    inference(resolution,[],[f22,f31])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.21/0.44    inference(flattening,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (31146)------------------------------
% 0.21/0.44  % (31146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (31146)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (31146)Memory used [KB]: 6140
% 0.21/0.44  % (31146)Time elapsed: 0.041 s
% 0.21/0.44  % (31146)------------------------------
% 0.21/0.44  % (31146)------------------------------
% 0.21/0.45  % (31126)Success in time 0.085 s
%------------------------------------------------------------------------------
