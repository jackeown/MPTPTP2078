%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 129 expanded)
%              Number of leaves         :   15 (  41 expanded)
%              Depth                    :   13
%              Number of atoms          :  225 ( 432 expanded)
%              Number of equality atoms :   25 (  57 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f171,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f63,f68,f78,f87,f118,f130,f170])).

fof(f170,plain,
    ( ~ spl8_1
    | ~ spl8_3
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f168,f86])).

fof(f86,plain,
    ( r2_hidden(sK0,k2_relat_1(sK3))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl8_6
  <=> r2_hidden(sK0,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f168,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK3))
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(equality_resolution,[],[f151])).

fof(f151,plain,
    ( ! [X0] :
        ( sK0 != X0
        | ~ r2_hidden(X0,k2_relat_1(sK3)) )
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f149,f72])).

fof(f72,plain,
    ( ! [X1] :
        ( sP5(X1,sK3)
        | ~ r2_hidden(X1,k2_relat_1(sK3)) )
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f51,f69])).

fof(f69,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_3 ),
    inference(resolution,[],[f62,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f62,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl8_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f51,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(sK3)
        | sP5(X1,sK3)
        | ~ r2_hidden(X1,k2_relat_1(sK3)) )
    | ~ spl8_1 ),
    inference(resolution,[],[f48,f42])).

fof(f42,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sP5(X2,X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sP5(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f48,plain,
    ( v1_funct_1(sK3)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl8_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f149,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | sK0 != X0
        | ~ sP5(X0,sK3) )
    | ~ spl8_8 ),
    inference(resolution,[],[f117,f26])).

fof(f26,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK6(X0,X2),k1_relat_1(X0))
      | ~ sP5(X2,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f117,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK6(sK3,X2),k1_relat_1(sK3))
        | ~ r2_hidden(X2,k2_relat_1(sK3))
        | sK0 != X2 )
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl8_8
  <=> ! [X2] :
        ( sK0 != X2
        | ~ r2_hidden(X2,k2_relat_1(sK3))
        | ~ r2_hidden(sK6(sK3,X2),k1_relat_1(sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f130,plain,
    ( ~ spl8_3
    | spl8_7 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | ~ spl8_3
    | spl8_7 ),
    inference(subsumption_resolution,[],[f62,f128])).

fof(f128,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
    | spl8_7 ),
    inference(resolution,[],[f114,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f114,plain,
    ( ~ v4_relat_1(sK3,sK1)
    | spl8_7 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl8_7
  <=> v4_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f118,plain,
    ( ~ spl8_7
    | spl8_8
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f104,f75,f60,f46,f116,f112])).

fof(f75,plain,
    ( spl8_5
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f104,plain,
    ( ! [X2] :
        ( sK0 != X2
        | ~ r2_hidden(sK6(sK3,X2),k1_relat_1(sK3))
        | ~ r2_hidden(X2,k2_relat_1(sK3))
        | ~ v4_relat_1(sK3,sK1) )
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(resolution,[],[f98,f82])).

fof(f82,plain,
    ( ! [X1] :
        ( r1_tarski(k1_relat_1(sK3),X1)
        | ~ v4_relat_1(sK3,X1) )
    | ~ spl8_5 ),
    inference(resolution,[],[f77,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f77,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,sK1)
        | sK0 != X0
        | ~ r2_hidden(sK6(sK3,X0),X1)
        | ~ r2_hidden(X0,k2_relat_1(sK3)) )
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(resolution,[],[f93,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f93,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6(sK3,X0),sK1)
        | ~ r2_hidden(X0,k2_relat_1(sK3))
        | sK0 != X0 )
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(resolution,[],[f91,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f91,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK6(sK3,X0),sK1)
        | sK0 != X0
        | ~ r2_hidden(X0,k2_relat_1(sK3)) )
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(superposition,[],[f20,f88])).

fof(f88,plain,
    ( ! [X0] :
        ( k1_funct_1(sK3,sK6(sK3,X0)) = X0
        | ~ r2_hidden(X0,k2_relat_1(sK3)) )
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(resolution,[],[f72,f27])).

fof(f27,plain,(
    ! [X2,X0] :
      ( ~ sP5(X2,X0)
      | k1_funct_1(X0,sK6(X0,X2)) = X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f20,plain,(
    ! [X4] :
      ( sK0 != k1_funct_1(sK3,X4)
      | ~ m1_subset_1(X4,sK1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

fof(f87,plain,
    ( spl8_6
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f80,f65,f60,f84])).

fof(f65,plain,
    ( spl8_4
  <=> r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f80,plain,
    ( r2_hidden(sK0,k2_relat_1(sK3))
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f79,f62])).

fof(f79,plain,
    ( r2_hidden(sK0,k2_relat_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl8_4 ),
    inference(superposition,[],[f67,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f67,plain,
    ( r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f78,plain,
    ( spl8_5
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f69,f60,f75])).

fof(f68,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f24,f65])).

fof(f24,plain,(
    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f63,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f23,f60])).

fof(f23,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f11])).

fof(f49,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f21,f46])).

fof(f21,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:58:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (22430)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.49  % (22439)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.49  % (22430)Refutation not found, incomplete strategy% (22430)------------------------------
% 0.21/0.49  % (22430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (22430)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (22430)Memory used [KB]: 10746
% 0.21/0.49  % (22430)Time elapsed: 0.075 s
% 0.21/0.49  % (22430)------------------------------
% 0.21/0.49  % (22430)------------------------------
% 0.21/0.50  % (22439)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f171,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f49,f63,f68,f78,f87,f118,f130,f170])).
% 0.21/0.50  fof(f170,plain,(
% 0.21/0.50    ~spl8_1 | ~spl8_3 | ~spl8_6 | ~spl8_8),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f169])).
% 0.21/0.50  fof(f169,plain,(
% 0.21/0.50    $false | (~spl8_1 | ~spl8_3 | ~spl8_6 | ~spl8_8)),
% 0.21/0.50    inference(subsumption_resolution,[],[f168,f86])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    r2_hidden(sK0,k2_relat_1(sK3)) | ~spl8_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f84])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    spl8_6 <=> r2_hidden(sK0,k2_relat_1(sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.50  fof(f168,plain,(
% 0.21/0.50    ~r2_hidden(sK0,k2_relat_1(sK3)) | (~spl8_1 | ~spl8_3 | ~spl8_8)),
% 0.21/0.50    inference(equality_resolution,[],[f151])).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    ( ! [X0] : (sK0 != X0 | ~r2_hidden(X0,k2_relat_1(sK3))) ) | (~spl8_1 | ~spl8_3 | ~spl8_8)),
% 0.21/0.50    inference(subsumption_resolution,[],[f149,f72])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ( ! [X1] : (sP5(X1,sK3) | ~r2_hidden(X1,k2_relat_1(sK3))) ) | (~spl8_1 | ~spl8_3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f51,f69])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    v1_relat_1(sK3) | ~spl8_3),
% 0.21/0.50    inference(resolution,[],[f62,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl8_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    spl8_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X1] : (~v1_relat_1(sK3) | sP5(X1,sK3) | ~r2_hidden(X1,k2_relat_1(sK3))) ) | ~spl8_1),
% 0.21/0.50    inference(resolution,[],[f48,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X2,X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | sP5(X2,X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.21/0.50    inference(equality_resolution,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | sP5(X2,X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    v1_funct_1(sK3) | ~spl8_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    spl8_1 <=> v1_funct_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.50  fof(f149,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | sK0 != X0 | ~sP5(X0,sK3)) ) | ~spl8_8),
% 0.21/0.50    inference(resolution,[],[f117,f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ( ! [X2,X0] : (r2_hidden(sK6(X0,X2),k1_relat_1(X0)) | ~sP5(X2,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    ( ! [X2] : (~r2_hidden(sK6(sK3,X2),k1_relat_1(sK3)) | ~r2_hidden(X2,k2_relat_1(sK3)) | sK0 != X2) ) | ~spl8_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f116])).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    spl8_8 <=> ! [X2] : (sK0 != X2 | ~r2_hidden(X2,k2_relat_1(sK3)) | ~r2_hidden(sK6(sK3,X2),k1_relat_1(sK3)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    ~spl8_3 | spl8_7),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f129])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    $false | (~spl8_3 | spl8_7)),
% 0.21/0.50    inference(subsumption_resolution,[],[f62,f128])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | spl8_7),
% 0.21/0.50    inference(resolution,[],[f114,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    ~v4_relat_1(sK3,sK1) | spl8_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f112])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    spl8_7 <=> v4_relat_1(sK3,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    ~spl8_7 | spl8_8 | ~spl8_1 | ~spl8_3 | ~spl8_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f104,f75,f60,f46,f116,f112])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    spl8_5 <=> v1_relat_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    ( ! [X2] : (sK0 != X2 | ~r2_hidden(sK6(sK3,X2),k1_relat_1(sK3)) | ~r2_hidden(X2,k2_relat_1(sK3)) | ~v4_relat_1(sK3,sK1)) ) | (~spl8_1 | ~spl8_3 | ~spl8_5)),
% 0.21/0.50    inference(resolution,[],[f98,f82])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ( ! [X1] : (r1_tarski(k1_relat_1(sK3),X1) | ~v4_relat_1(sK3,X1)) ) | ~spl8_5),
% 0.21/0.50    inference(resolution,[],[f77,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    v1_relat_1(sK3) | ~spl8_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f75])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X1,sK1) | sK0 != X0 | ~r2_hidden(sK6(sK3,X0),X1) | ~r2_hidden(X0,k2_relat_1(sK3))) ) | (~spl8_1 | ~spl8_3)),
% 0.21/0.50    inference(resolution,[],[f93,f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(sK6(sK3,X0),sK1) | ~r2_hidden(X0,k2_relat_1(sK3)) | sK0 != X0) ) | (~spl8_1 | ~spl8_3)),
% 0.21/0.50    inference(resolution,[],[f91,f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(sK6(sK3,X0),sK1) | sK0 != X0 | ~r2_hidden(X0,k2_relat_1(sK3))) ) | (~spl8_1 | ~spl8_3)),
% 0.21/0.50    inference(superposition,[],[f20,f88])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    ( ! [X0] : (k1_funct_1(sK3,sK6(sK3,X0)) = X0 | ~r2_hidden(X0,k2_relat_1(sK3))) ) | (~spl8_1 | ~spl8_3)),
% 0.21/0.50    inference(resolution,[],[f72,f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X2,X0] : (~sP5(X2,X0) | k1_funct_1(X0,sK6(X0,X2)) = X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ( ! [X4] : (sK0 != k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))),
% 0.21/0.50    inference(flattening,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.21/0.50    inference(negated_conjecture,[],[f8])).
% 0.21/0.50  fof(f8,conjecture,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    spl8_6 | ~spl8_3 | ~spl8_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f80,f65,f60,f84])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    spl8_4 <=> r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    r2_hidden(sK0,k2_relat_1(sK3)) | (~spl8_3 | ~spl8_4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f79,f62])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    r2_hidden(sK0,k2_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl8_4),
% 0.21/0.50    inference(superposition,[],[f67,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) | ~spl8_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f65])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    spl8_5 | ~spl8_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f69,f60,f75])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    spl8_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f24,f65])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    spl8_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f23,f60])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    spl8_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f21,f46])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    v1_funct_1(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (22439)------------------------------
% 0.21/0.50  % (22439)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (22439)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (22439)Memory used [KB]: 10874
% 0.21/0.50  % (22439)Time elapsed: 0.081 s
% 0.21/0.50  % (22439)------------------------------
% 0.21/0.50  % (22439)------------------------------
% 0.21/0.50  % (22417)Success in time 0.142 s
%------------------------------------------------------------------------------
