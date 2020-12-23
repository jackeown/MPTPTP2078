%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:29 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 117 expanded)
%              Number of leaves         :   10 (  25 expanded)
%              Depth                    :   13
%              Number of atoms          :  195 ( 564 expanded)
%              Number of equality atoms :   55 ( 143 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f152,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f94,f104,f150])).

fof(f150,plain,(
    ~ spl9_4 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f147,f20])).

fof(f20,plain,(
    r2_hidden(sK5,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
          & ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & r2_hidden(X5,X0) ) )
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
          & ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & r2_hidden(X5,X0) ) )
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => ! [X4] :
              ( ? [X5] :
                  ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
             => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

% (410)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => ! [X4] :
            ( ? [X5] :
                ( k1_funct_1(X3,X5) = X4
                & r2_hidden(X5,X2)
                & r2_hidden(X5,X0) )
           => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_2)).

fof(f147,plain,
    ( ~ r2_hidden(sK5,sK2)
    | ~ spl9_4 ),
    inference(resolution,[],[f146,f86])).

fof(f86,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl9_4
  <=> r2_hidden(k4_tarski(sK5,sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f146,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(X0,sK4),sK3)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f145,f90])).

fof(f90,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f25,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f25,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f10])).

fof(f145,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(X0,sK4),sK3)
      | ~ r2_hidden(X0,sK2)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f144,f46])).

fof(f46,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(X3,k9_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(X4,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

fof(f144,plain,(
    ~ r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    inference(subsumption_resolution,[],[f143,f25])).

fof(f143,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f22,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f22,plain,(
    ~ r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f104,plain,(
    spl9_2 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | spl9_2 ),
    inference(subsumption_resolution,[],[f102,f19])).

fof(f19,plain,(
    r2_hidden(sK5,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f102,plain,
    ( ~ r2_hidden(sK5,sK0)
    | spl9_2 ),
    inference(backward_demodulation,[],[f69,f101])).

fof(f101,plain,(
    sK0 = k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f99,f25])).

fof(f99,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f92,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f92,plain,(
    sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f91,f24])).

fof(f24,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f91,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1) ),
    inference(subsumption_resolution,[],[f89,f26])).

fof(f26,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f10])).

fof(f89,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1) ),
    inference(resolution,[],[f25,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f69,plain,
    ( ~ r2_hidden(sK5,k1_relat_1(sK3))
    | spl9_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl9_2
  <=> r2_hidden(sK5,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f94,plain,(
    spl9_1 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | spl9_1 ),
    inference(subsumption_resolution,[],[f90,f66])).

fof(f66,plain,
    ( ~ v1_relat_1(sK3)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl9_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f87,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | spl9_4 ),
    inference(avatar_split_clause,[],[f82,f84,f68,f64])).

fof(f82,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f61,f23])).

fof(f23,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f61,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | ~ v1_funct_1(sK3)
    | ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f49,f21])).

fof(f21,plain,(
    sK4 = k1_funct_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f10])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:28:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.48  % (401)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (415)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.48  % (401)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f152,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f87,f94,f104,f150])).
% 0.22/0.48  fof(f150,plain,(
% 0.22/0.48    ~spl9_4),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f149])).
% 0.22/0.48  fof(f149,plain,(
% 0.22/0.48    $false | ~spl9_4),
% 0.22/0.48    inference(subsumption_resolution,[],[f147,f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    r2_hidden(sK5,sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ? [X0,X1,X2,X3] : (? [X4] : (~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) & ? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.22/0.48    inference(flattening,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ? [X0,X1,X2,X3] : ((? [X4] : (~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) & ? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => ! [X4] : (? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)))))),
% 0.22/0.48    inference(negated_conjecture,[],[f7])).
% 0.22/0.48  % (410)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.48  fof(f7,conjecture,(
% 0.22/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => ! [X4] : (? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_2)).
% 0.22/0.48  fof(f147,plain,(
% 0.22/0.48    ~r2_hidden(sK5,sK2) | ~spl9_4),
% 0.22/0.48    inference(resolution,[],[f146,f86])).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    r2_hidden(k4_tarski(sK5,sK4),sK3) | ~spl9_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f84])).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    spl9_4 <=> r2_hidden(k4_tarski(sK5,sK4),sK3)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.22/0.48  fof(f146,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK4),sK3) | ~r2_hidden(X0,sK2)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f145,f90])).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    v1_relat_1(sK3)),
% 0.22/0.49    inference(resolution,[],[f25,f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f145,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK4),sK3) | ~r2_hidden(X0,sK2) | ~v1_relat_1(sK3)) )),
% 0.22/0.49    inference(resolution,[],[f144,f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X4,X0,X3,X1] : (r2_hidden(X3,k9_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(X4,X1) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(equality_resolution,[],[f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(X4,X1) | r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).
% 0.22/0.49  fof(f144,plain,(
% 0.22/0.49    ~r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.22/0.49    inference(subsumption_resolution,[],[f143,f25])).
% 0.22/0.49  fof(f143,plain,(
% 0.22/0.49    ~r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.49    inference(superposition,[],[f22,f45])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ~r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    spl9_2),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f103])).
% 0.22/0.49  fof(f103,plain,(
% 0.22/0.49    $false | spl9_2),
% 0.22/0.49    inference(subsumption_resolution,[],[f102,f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    r2_hidden(sK5,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    ~r2_hidden(sK5,sK0) | spl9_2),
% 0.22/0.49    inference(backward_demodulation,[],[f69,f101])).
% 0.22/0.49  fof(f101,plain,(
% 0.22/0.49    sK0 = k1_relat_1(sK3)),
% 0.22/0.49    inference(subsumption_resolution,[],[f99,f25])).
% 0.22/0.49  fof(f99,plain,(
% 0.22/0.49    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.49    inference(superposition,[],[f92,f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.22/0.49    inference(subsumption_resolution,[],[f91,f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f89,f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    k1_xboole_0 != sK1),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.49    inference(resolution,[],[f25,f44])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(flattening,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    ~r2_hidden(sK5,k1_relat_1(sK3)) | spl9_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f68])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    spl9_2 <=> r2_hidden(sK5,k1_relat_1(sK3))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    spl9_1),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f93])).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    $false | spl9_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f90,f66])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    ~v1_relat_1(sK3) | spl9_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f64])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    spl9_1 <=> v1_relat_1(sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    ~spl9_1 | ~spl9_2 | spl9_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f82,f84,f68,f64])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    r2_hidden(k4_tarski(sK5,sK4),sK3) | ~r2_hidden(sK5,k1_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 0.22/0.49    inference(subsumption_resolution,[],[f61,f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    v1_funct_1(sK3)),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    r2_hidden(k4_tarski(sK5,sK4),sK3) | ~v1_funct_1(sK3) | ~r2_hidden(sK5,k1_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 0.22/0.49    inference(superposition,[],[f49,f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    sK4 = k1_funct_1(sK3,sK5)),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) | ~v1_funct_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(equality_resolution,[],[f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2) )),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (401)------------------------------
% 0.22/0.49  % (401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (401)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (401)Memory used [KB]: 10618
% 0.22/0.49  % (401)Time elapsed: 0.066 s
% 0.22/0.49  % (401)------------------------------
% 0.22/0.49  % (401)------------------------------
% 0.22/0.49  % (399)Success in time 0.125 s
%------------------------------------------------------------------------------
