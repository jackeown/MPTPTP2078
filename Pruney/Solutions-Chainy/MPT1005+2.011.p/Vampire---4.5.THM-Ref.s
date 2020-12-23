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
% DateTime   : Thu Dec  3 13:03:40 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   54 (  73 expanded)
%              Number of leaves         :   15 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :  139 ( 184 expanded)
%              Number of equality atoms :   36 (  51 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f75,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f41,f45,f56,f62,f73])).

fof(f73,plain,
    ( ~ spl5_2
    | ~ spl5_4
    | spl5_5 ),
    inference(avatar_contradiction_clause,[],[f72])).

fof(f72,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_4
    | spl5_5 ),
    inference(subsumption_resolution,[],[f61,f71])).

fof(f71,plain,
    ( ! [X0] : k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,X0)
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f70,f26])).

fof(f26,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

fof(f70,plain,
    ( ! [X0] : k9_relat_1(k1_xboole_0,X0) = k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,X0)
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f68,f54])).

fof(f54,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl5_4
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f68,plain,
    ( ! [X0] : k7_relset_1(k1_xboole_0,sK0,sK2,X0) = k9_relat_1(sK2,X0)
    | ~ spl5_2 ),
    inference(resolution,[],[f33,f40])).

fof(f40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl5_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f61,plain,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl5_5
  <=> k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f62,plain,
    ( ~ spl5_5
    | spl5_1
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f57,f53,f35,f60])).

fof(f35,plain,
    ( spl5_1
  <=> k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f57,plain,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)
    | spl5_1
    | ~ spl5_4 ),
    inference(superposition,[],[f36,f54])).

fof(f36,plain,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f56,plain,
    ( spl5_4
    | ~ spl5_3
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f51,f39,f43,f53])).

fof(f43,plain,
    ( spl5_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f51,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK2
    | ~ spl5_2 ),
    inference(resolution,[],[f50,f40])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_xboole_0(X1)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f32,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f29,f27])).

fof(f27,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f45,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f25,f43])).

fof(f25,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f41,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f23,f39])).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
   => ( k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_1(X2) )
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_2)).

fof(f37,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f24,f35])).

fof(f24,plain,(
    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:06:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.44  % (3420)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.44  % (3428)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.19/0.45  % (3420)Refutation found. Thanks to Tanya!
% 0.19/0.45  % SZS status Theorem for theBenchmark
% 0.19/0.45  % SZS output start Proof for theBenchmark
% 0.19/0.45  fof(f75,plain,(
% 0.19/0.45    $false),
% 0.19/0.45    inference(avatar_sat_refutation,[],[f37,f41,f45,f56,f62,f73])).
% 0.19/0.45  fof(f73,plain,(
% 0.19/0.45    ~spl5_2 | ~spl5_4 | spl5_5),
% 0.19/0.45    inference(avatar_contradiction_clause,[],[f72])).
% 0.19/0.45  fof(f72,plain,(
% 0.19/0.45    $false | (~spl5_2 | ~spl5_4 | spl5_5)),
% 0.19/0.45    inference(subsumption_resolution,[],[f61,f71])).
% 0.19/0.45  fof(f71,plain,(
% 0.19/0.45    ( ! [X0] : (k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,X0)) ) | (~spl5_2 | ~spl5_4)),
% 0.19/0.45    inference(forward_demodulation,[],[f70,f26])).
% 0.19/0.45  fof(f26,plain,(
% 0.19/0.45    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f3])).
% 0.19/0.45  fof(f3,axiom,(
% 0.19/0.45    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).
% 0.19/0.45  fof(f70,plain,(
% 0.19/0.45    ( ! [X0] : (k9_relat_1(k1_xboole_0,X0) = k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,X0)) ) | (~spl5_2 | ~spl5_4)),
% 0.19/0.45    inference(forward_demodulation,[],[f68,f54])).
% 0.19/0.45  fof(f54,plain,(
% 0.19/0.45    k1_xboole_0 = sK2 | ~spl5_4),
% 0.19/0.45    inference(avatar_component_clause,[],[f53])).
% 0.19/0.45  fof(f53,plain,(
% 0.19/0.45    spl5_4 <=> k1_xboole_0 = sK2),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.19/0.45  fof(f68,plain,(
% 0.19/0.45    ( ! [X0] : (k7_relset_1(k1_xboole_0,sK0,sK2,X0) = k9_relat_1(sK2,X0)) ) | ~spl5_2),
% 0.19/0.45    inference(resolution,[],[f33,f40])).
% 0.19/0.45  fof(f40,plain,(
% 0.19/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~spl5_2),
% 0.19/0.45    inference(avatar_component_clause,[],[f39])).
% 0.19/0.45  fof(f39,plain,(
% 0.19/0.45    spl5_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.19/0.45  fof(f33,plain,(
% 0.19/0.45    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f14])).
% 0.19/0.45  fof(f14,plain,(
% 0.19/0.45    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.45    inference(ennf_transformation,[],[f5])).
% 0.19/0.45  fof(f5,axiom,(
% 0.19/0.45    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.19/0.45  fof(f61,plain,(
% 0.19/0.45    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) | spl5_5),
% 0.19/0.45    inference(avatar_component_clause,[],[f60])).
% 0.19/0.45  fof(f60,plain,(
% 0.19/0.45    spl5_5 <=> k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.19/0.45  fof(f62,plain,(
% 0.19/0.45    ~spl5_5 | spl5_1 | ~spl5_4),
% 0.19/0.45    inference(avatar_split_clause,[],[f57,f53,f35,f60])).
% 0.19/0.45  fof(f35,plain,(
% 0.19/0.45    spl5_1 <=> k1_xboole_0 = k7_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.19/0.45  fof(f57,plain,(
% 0.19/0.45    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) | (spl5_1 | ~spl5_4)),
% 0.19/0.45    inference(superposition,[],[f36,f54])).
% 0.19/0.45  fof(f36,plain,(
% 0.19/0.45    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) | spl5_1),
% 0.19/0.45    inference(avatar_component_clause,[],[f35])).
% 0.19/0.45  fof(f56,plain,(
% 0.19/0.45    spl5_4 | ~spl5_3 | ~spl5_2),
% 0.19/0.45    inference(avatar_split_clause,[],[f51,f39,f43,f53])).
% 0.19/0.45  fof(f43,plain,(
% 0.19/0.45    spl5_3 <=> v1_xboole_0(k1_xboole_0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.19/0.45  fof(f51,plain,(
% 0.19/0.45    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = sK2 | ~spl5_2),
% 0.19/0.45    inference(resolution,[],[f50,f40])).
% 0.19/0.45  fof(f50,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_xboole_0(X1) | k1_xboole_0 = X0) )),
% 0.19/0.45    inference(resolution,[],[f32,f46])).
% 0.19/0.45  fof(f46,plain,(
% 0.19/0.45    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.19/0.45    inference(resolution,[],[f29,f27])).
% 0.19/0.45  fof(f27,plain,(
% 0.19/0.45    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f20])).
% 0.19/0.45  fof(f20,plain,(
% 0.19/0.45    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.19/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).
% 0.19/0.45  fof(f19,plain,(
% 0.19/0.45    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.19/0.45    introduced(choice_axiom,[])).
% 0.19/0.45  fof(f18,plain,(
% 0.19/0.45    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.19/0.45    inference(rectify,[],[f17])).
% 0.19/0.45  fof(f17,plain,(
% 0.19/0.45    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.19/0.45    inference(nnf_transformation,[],[f1])).
% 0.19/0.45  fof(f1,axiom,(
% 0.19/0.45    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.19/0.45  fof(f29,plain,(
% 0.19/0.45    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.19/0.45    inference(cnf_transformation,[],[f22])).
% 0.19/0.45  fof(f22,plain,(
% 0.19/0.45    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)) | k1_xboole_0 = X0)),
% 0.19/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f21])).
% 0.19/0.45  fof(f21,plain,(
% 0.19/0.45    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)))),
% 0.19/0.45    introduced(choice_axiom,[])).
% 0.19/0.45  fof(f12,plain,(
% 0.19/0.45    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.19/0.45    inference(ennf_transformation,[],[f6])).
% 0.19/0.45  fof(f6,axiom,(
% 0.19/0.45    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).
% 0.19/0.45  fof(f32,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f13])).
% 0.19/0.45  fof(f13,plain,(
% 0.19/0.45    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.19/0.45    inference(ennf_transformation,[],[f4])).
% 0.19/0.45  fof(f4,axiom,(
% 0.19/0.45    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).
% 0.19/0.45  fof(f45,plain,(
% 0.19/0.45    spl5_3),
% 0.19/0.45    inference(avatar_split_clause,[],[f25,f43])).
% 0.19/0.45  fof(f25,plain,(
% 0.19/0.45    v1_xboole_0(k1_xboole_0)),
% 0.19/0.45    inference(cnf_transformation,[],[f2])).
% 0.19/0.45  fof(f2,axiom,(
% 0.19/0.45    v1_xboole_0(k1_xboole_0)),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.19/0.45  fof(f41,plain,(
% 0.19/0.45    spl5_2),
% 0.19/0.45    inference(avatar_split_clause,[],[f23,f39])).
% 0.19/0.45  fof(f23,plain,(
% 0.19/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.19/0.45    inference(cnf_transformation,[],[f16])).
% 0.19/0.45  fof(f16,plain,(
% 0.19/0.45    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.19/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f15])).
% 0.19/0.45  fof(f15,plain,(
% 0.19/0.45    ? [X0,X1,X2] : (k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) => (k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))))),
% 0.19/0.45    introduced(choice_axiom,[])).
% 0.19/0.45  fof(f11,plain,(
% 0.19/0.45    ? [X0,X1,X2] : (k1_xboole_0 != k7_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))))),
% 0.19/0.45    inference(ennf_transformation,[],[f10])).
% 0.19/0.45  fof(f10,plain,(
% 0.19/0.45    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.19/0.45    inference(pure_predicate_removal,[],[f9])).
% 0.19/0.45  fof(f9,plain,(
% 0.19/0.45    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.19/0.45    inference(pure_predicate_removal,[],[f8])).
% 0.19/0.45  fof(f8,negated_conjecture,(
% 0.19/0.45    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.19/0.45    inference(negated_conjecture,[],[f7])).
% 0.19/0.45  fof(f7,conjecture,(
% 0.19/0.45    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k7_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_2)).
% 0.19/0.45  fof(f37,plain,(
% 0.19/0.45    ~spl5_1),
% 0.19/0.45    inference(avatar_split_clause,[],[f24,f35])).
% 0.19/0.45  fof(f24,plain,(
% 0.19/0.45    k1_xboole_0 != k7_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.19/0.45    inference(cnf_transformation,[],[f16])).
% 0.19/0.45  % SZS output end Proof for theBenchmark
% 0.19/0.45  % (3420)------------------------------
% 0.19/0.45  % (3420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.45  % (3420)Termination reason: Refutation
% 0.19/0.45  
% 0.19/0.45  % (3420)Memory used [KB]: 10618
% 0.19/0.45  % (3420)Time elapsed: 0.048 s
% 0.19/0.45  % (3420)------------------------------
% 0.19/0.45  % (3420)------------------------------
% 0.19/0.45  % (3412)Success in time 0.102 s
%------------------------------------------------------------------------------
