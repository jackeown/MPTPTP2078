%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 109 expanded)
%              Number of leaves         :   14 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  210 ( 374 expanded)
%              Number of equality atoms :   17 (  27 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f166,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f51,f59,f65,f70,f82,f93,f132,f160,f165])).

fof(f165,plain,
    ( spl7_5
    | ~ spl7_10 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | spl7_5
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f163,f69])).

fof(f69,plain,
    ( ~ m1_subset_1(k1_funct_1(sK2,sK1),sK0)
    | spl7_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl7_5
  <=> m1_subset_1(k1_funct_1(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f163,plain,
    ( m1_subset_1(k1_funct_1(sK2,sK1),sK0)
    | ~ spl7_10 ),
    inference(resolution,[],[f159,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f159,plain,
    ( r2_hidden(k1_funct_1(sK2,sK1),sK0)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl7_10
  <=> r2_hidden(k1_funct_1(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f160,plain,
    ( spl7_10
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f143,f130,f158])).

fof(f130,plain,
    ( spl7_9
  <=> sP6(sK1,sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f143,plain,
    ( r2_hidden(k1_funct_1(sK2,sK1),sK0)
    | ~ spl7_9 ),
    inference(resolution,[],[f131,f27])).

fof(f27,plain,(
    ! [X4,X2,X0] :
      ( ~ sP6(X4,X2,X0)
      | r2_hidden(k1_funct_1(X2,X4),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( k1_funct_1(X2,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( k1_funct_1(X2,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X2,X3) = k1_funct_1(X1,X3) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) ) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X2,X3) = k1_funct_1(X1,X3) )
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X3),X0)
                    & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_1)).

fof(f131,plain,
    ( sP6(sK1,sK2,sK0)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f130])).

fof(f132,plain,
    ( spl7_9
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f127,f91,f63,f49,f45,f130])).

fof(f45,plain,
    ( spl7_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f49,plain,
    ( spl7_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f63,plain,
    ( spl7_4
  <=> r2_hidden(sK1,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f91,plain,
    ( spl7_8
  <=> sK2 = k8_relat_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f127,plain,
    ( sP6(sK1,sK2,sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(resolution,[],[f101,f64])).

fof(f64,plain,
    ( r2_hidden(sK1,k1_relat_1(sK2))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f63])).

fof(f101,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | sP6(X0,sK2,sK0) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f100,f46])).

fof(f46,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f100,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ v1_relat_1(sK2)
        | sP6(X0,sK2,sK0) )
    | ~ spl7_2
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f99,f50])).

fof(f50,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f99,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | sP6(X0,sK2,sK0) )
    | ~ spl7_8 ),
    inference(duplicate_literal_removal,[],[f96])).

fof(f96,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(sK2)
        | sP6(X0,sK2,sK0)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_8 ),
    inference(superposition,[],[f42,f92])).

fof(f92,plain,
    ( sK2 = k8_relat_1(sK0,sK2)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f91])).

fof(f42,plain,(
    ! [X4,X2,X0] :
      ( ~ r2_hidden(X4,k1_relat_1(k8_relat_1(X0,X2)))
      | ~ v1_funct_1(k8_relat_1(X0,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | sP6(X4,X2,X0)
      | ~ v1_relat_1(k8_relat_1(X0,X2)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | sP6(X4,X2,X0)
      | ~ r2_hidden(X4,k1_relat_1(X1))
      | k8_relat_1(X0,X2) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f93,plain,
    ( spl7_8
    | ~ spl7_1
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f89,f80,f45,f91])).

fof(f80,plain,
    ( spl7_6
  <=> r1_tarski(k2_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f89,plain,
    ( sK2 = k8_relat_1(sK0,sK2)
    | ~ spl7_1
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f87,f46])).

fof(f87,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k8_relat_1(sK0,sK2)
    | ~ spl7_6 ),
    inference(resolution,[],[f81,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(f81,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f80])).

fof(f82,plain,
    ( spl7_6
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f61,f57,f45,f80])).

fof(f57,plain,
    ( spl7_3
  <=> v5_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f61,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0)
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f60,f46])).

fof(f60,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2)
    | ~ spl7_3 ),
    inference(resolution,[],[f58,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f58,plain,
    ( v5_relat_1(sK2,sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f70,plain,(
    ~ spl7_5 ),
    inference(avatar_split_clause,[],[f23,f68])).

fof(f23,plain,(
    ~ m1_subset_1(k1_funct_1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ m1_subset_1(k1_funct_1(X2,X1),X0)
      & r2_hidden(X1,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v5_relat_1(X2,X0)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ m1_subset_1(k1_funct_1(X2,X1),X0)
      & r2_hidden(X1,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v5_relat_1(X2,X0)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
       => ( r2_hidden(X1,k1_relat_1(X2))
         => m1_subset_1(k1_funct_1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => m1_subset_1(k1_funct_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).

fof(f65,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f22,f63])).

fof(f22,plain,(
    r2_hidden(sK1,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f59,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f20,f57])).

fof(f20,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f51,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f21,f49])).

fof(f21,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f47,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f19,f45])).

fof(f19,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:15:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (9608)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.47  % (9601)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (9609)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.47  % (9601)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f166,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f47,f51,f59,f65,f70,f82,f93,f132,f160,f165])).
% 0.20/0.47  fof(f165,plain,(
% 0.20/0.47    spl7_5 | ~spl7_10),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f164])).
% 0.20/0.47  fof(f164,plain,(
% 0.20/0.47    $false | (spl7_5 | ~spl7_10)),
% 0.20/0.47    inference(subsumption_resolution,[],[f163,f69])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    ~m1_subset_1(k1_funct_1(sK2,sK1),sK0) | spl7_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f68])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    spl7_5 <=> m1_subset_1(k1_funct_1(sK2,sK1),sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.47  fof(f163,plain,(
% 0.20/0.47    m1_subset_1(k1_funct_1(sK2,sK1),sK0) | ~spl7_10),
% 0.20/0.47    inference(resolution,[],[f159,f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.47  fof(f159,plain,(
% 0.20/0.47    r2_hidden(k1_funct_1(sK2,sK1),sK0) | ~spl7_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f158])).
% 0.20/0.47  fof(f158,plain,(
% 0.20/0.47    spl7_10 <=> r2_hidden(k1_funct_1(sK2,sK1),sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.20/0.47  fof(f160,plain,(
% 0.20/0.47    spl7_10 | ~spl7_9),
% 0.20/0.47    inference(avatar_split_clause,[],[f143,f130,f158])).
% 0.20/0.47  fof(f130,plain,(
% 0.20/0.47    spl7_9 <=> sP6(sK1,sK2,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.20/0.47  fof(f143,plain,(
% 0.20/0.47    r2_hidden(k1_funct_1(sK2,sK1),sK0) | ~spl7_9),
% 0.20/0.47    inference(resolution,[],[f131,f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ( ! [X4,X2,X0] : (~sP6(X4,X2,X0) | r2_hidden(k1_funct_1(X2,X4),X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0,X1] : (! [X2] : ((k8_relat_1(X0,X2) = X1 <=> (! [X3] : (k1_funct_1(X2,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X1))) & ! [X4] : (r2_hidden(X4,k1_relat_1(X1)) <=> (r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2)))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0,X1] : (! [X2] : ((k8_relat_1(X0,X2) = X1 <=> (! [X3] : (k1_funct_1(X2,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X1))) & ! [X4] : (r2_hidden(X4,k1_relat_1(X1)) <=> (r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2)))))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (k8_relat_1(X0,X2) = X1 <=> (! [X3] : (r2_hidden(X3,k1_relat_1(X1)) => k1_funct_1(X2,X3) = k1_funct_1(X1,X3)) & ! [X4] : (r2_hidden(X4,k1_relat_1(X1)) <=> (r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2))))))))),
% 0.20/0.47    inference(rectify,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (k8_relat_1(X0,X2) = X1 <=> (! [X3] : (r2_hidden(X3,k1_relat_1(X1)) => k1_funct_1(X2,X3) = k1_funct_1(X1,X3)) & ! [X3] : (r2_hidden(X3,k1_relat_1(X1)) <=> (r2_hidden(k1_funct_1(X2,X3),X0) & r2_hidden(X3,k1_relat_1(X2))))))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_1)).
% 0.20/0.47  fof(f131,plain,(
% 0.20/0.47    sP6(sK1,sK2,sK0) | ~spl7_9),
% 0.20/0.47    inference(avatar_component_clause,[],[f130])).
% 0.20/0.47  fof(f132,plain,(
% 0.20/0.47    spl7_9 | ~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f127,f91,f63,f49,f45,f130])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    spl7_1 <=> v1_relat_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    spl7_2 <=> v1_funct_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    spl7_4 <=> r2_hidden(sK1,k1_relat_1(sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.47  fof(f91,plain,(
% 0.20/0.47    spl7_8 <=> sK2 = k8_relat_1(sK0,sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.20/0.47  fof(f127,plain,(
% 0.20/0.47    sP6(sK1,sK2,sK0) | (~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_8)),
% 0.20/0.47    inference(resolution,[],[f101,f64])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    r2_hidden(sK1,k1_relat_1(sK2)) | ~spl7_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f63])).
% 0.20/0.47  fof(f101,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | sP6(X0,sK2,sK0)) ) | (~spl7_1 | ~spl7_2 | ~spl7_8)),
% 0.20/0.47    inference(subsumption_resolution,[],[f100,f46])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    v1_relat_1(sK2) | ~spl7_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f45])).
% 0.20/0.47  fof(f100,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | sP6(X0,sK2,sK0)) ) | (~spl7_2 | ~spl7_8)),
% 0.20/0.47    inference(subsumption_resolution,[],[f99,f50])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    v1_funct_1(sK2) | ~spl7_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f49])).
% 0.20/0.47  fof(f99,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sP6(X0,sK2,sK0)) ) | ~spl7_8),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f96])).
% 0.20/0.47  fof(f96,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | sP6(X0,sK2,sK0) | ~v1_relat_1(sK2)) ) | ~spl7_8),
% 0.20/0.47    inference(superposition,[],[f42,f92])).
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    sK2 = k8_relat_1(sK0,sK2) | ~spl7_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f91])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ( ! [X4,X2,X0] : (~r2_hidden(X4,k1_relat_1(k8_relat_1(X0,X2))) | ~v1_funct_1(k8_relat_1(X0,X2)) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | sP6(X4,X2,X0) | ~v1_relat_1(k8_relat_1(X0,X2))) )),
% 0.20/0.47    inference(equality_resolution,[],[f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | sP6(X4,X2,X0) | ~r2_hidden(X4,k1_relat_1(X1)) | k8_relat_1(X0,X2) != X1) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f93,plain,(
% 0.20/0.47    spl7_8 | ~spl7_1 | ~spl7_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f89,f80,f45,f91])).
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    spl7_6 <=> r1_tarski(k2_relat_1(sK2),sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.47  fof(f89,plain,(
% 0.20/0.47    sK2 = k8_relat_1(sK0,sK2) | (~spl7_1 | ~spl7_6)),
% 0.20/0.47    inference(subsumption_resolution,[],[f87,f46])).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    ~v1_relat_1(sK2) | sK2 = k8_relat_1(sK0,sK2) | ~spl7_6),
% 0.20/0.47    inference(resolution,[],[f81,f40])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | k8_relat_1(X0,X1) = X1) )),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    r1_tarski(k2_relat_1(sK2),sK0) | ~spl7_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f80])).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    spl7_6 | ~spl7_1 | ~spl7_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f61,f57,f45,f80])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    spl7_3 <=> v5_relat_1(sK2,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    r1_tarski(k2_relat_1(sK2),sK0) | (~spl7_1 | ~spl7_3)),
% 0.20/0.47    inference(subsumption_resolution,[],[f60,f46])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    r1_tarski(k2_relat_1(sK2),sK0) | ~v1_relat_1(sK2) | ~spl7_3),
% 0.20/0.47    inference(resolution,[],[f58,f39])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    v5_relat_1(sK2,sK0) | ~spl7_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f57])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    ~spl7_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f23,f68])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ~m1_subset_1(k1_funct_1(sK2,sK1),sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (~m1_subset_1(k1_funct_1(X2,X1),X0) & r2_hidden(X1,k1_relat_1(X2)) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2))),
% 0.20/0.47    inference(flattening,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ? [X0,X1,X2] : ((~m1_subset_1(k1_funct_1(X2,X1),X0) & r2_hidden(X1,k1_relat_1(X2))) & (v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (r2_hidden(X1,k1_relat_1(X2)) => m1_subset_1(k1_funct_1(X2,X1),X0)))),
% 0.20/0.47    inference(negated_conjecture,[],[f6])).
% 0.20/0.47  fof(f6,conjecture,(
% 0.20/0.47    ! [X0,X1,X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (r2_hidden(X1,k1_relat_1(X2)) => m1_subset_1(k1_funct_1(X2,X1),X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    spl7_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f22,f63])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    r2_hidden(sK1,k1_relat_1(sK2))),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    spl7_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f20,f57])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    v5_relat_1(sK2,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    spl7_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f21,f49])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    v1_funct_1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    spl7_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f19,f45])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    v1_relat_1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (9601)------------------------------
% 0.20/0.47  % (9601)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (9601)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (9601)Memory used [KB]: 6268
% 0.20/0.47  % (9601)Time elapsed: 0.056 s
% 0.20/0.47  % (9601)------------------------------
% 0.20/0.47  % (9601)------------------------------
% 0.20/0.48  % (9600)Success in time 0.115 s
%------------------------------------------------------------------------------
