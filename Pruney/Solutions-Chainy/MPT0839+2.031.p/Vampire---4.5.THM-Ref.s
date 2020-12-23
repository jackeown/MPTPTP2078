%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 130 expanded)
%              Number of leaves         :    9 (  26 expanded)
%              Depth                    :   14
%              Number of atoms          :  141 ( 411 expanded)
%              Number of equality atoms :   38 ( 104 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f67,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f52,f66])).

fof(f66,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f65])).

fof(f65,plain,
    ( $false
    | ~ spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f64,f57])).

fof(f57,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | spl4_2 ),
    inference(superposition,[],[f36,f44])).

fof(f44,plain,(
    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f28,f20])).

fof(f20,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k2_relset_1(X1,X0,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k2_relset_1(X1,X0,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ~ ( ! [X3] :
                ( m1_subset_1(X3,X1)
               => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
            & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                    & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                  & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relset_1)).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f36,plain,
    ( k1_xboole_0 != k1_relset_1(sK1,sK0,sK2)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl4_2
  <=> k1_xboole_0 = k1_relset_1(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f64,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f63,f60])).

fof(f60,plain,(
    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(subsumption_resolution,[],[f59,f20])).

fof(f59,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(superposition,[],[f29,f44])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f63,plain,
    ( ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1))
    | k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl4_1 ),
    inference(duplicate_literal_removal,[],[f62])).

fof(f62,plain,
    ( ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1))
    | k1_xboole_0 = k1_relat_1(sK2)
    | ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl4_1 ),
    inference(resolution,[],[f54,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

fof(f54,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(X0,k1_relat_1(sK2)),sK1)
        | ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(X0)) )
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f53,f44])).

fof(f53,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK3(X0,k1_relset_1(sK1,sK0,sK2)),sK1) )
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f33,f44])).

fof(f33,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK3(X0,k1_relset_1(sK1,sK0,sK2)),sK1) )
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl4_1
  <=> ! [X0] :
        ( ~ m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK3(X0,k1_relset_1(sK1,sK0,sK2)),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f52,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f51])).

fof(f51,plain,
    ( $false
    | ~ spl4_2 ),
    inference(resolution,[],[f50,f20])).

fof(f50,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ spl4_2 ),
    inference(resolution,[],[f49,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f49,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f48,f43])).

fof(f43,plain,(
    k1_xboole_0 != k2_relat_1(sK2) ),
    inference(superposition,[],[f21,f40])).

fof(f40,plain,(
    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f27,f20])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f21,plain,(
    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f48,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_2 ),
    inference(trivial_inequality_removal,[],[f47])).

fof(f47,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_2 ),
    inference(superposition,[],[f23,f46])).

fof(f46,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f44,f37])).

fof(f37,plain,
    ( k1_xboole_0 = k1_relset_1(sK1,sK0,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f38,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f30,f35,f32])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relset_1(sK1,sK0,sK2)
      | ~ m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK3(X0,k1_relset_1(sK1,sK0,sK2)),sK1) ) ),
    inference(resolution,[],[f25,f19])).

fof(f19,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:50:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.40  % (18128)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.41  % (18128)Refutation found. Thanks to Tanya!
% 0.20/0.41  % SZS status Theorem for theBenchmark
% 0.20/0.41  % SZS output start Proof for theBenchmark
% 0.20/0.41  fof(f67,plain,(
% 0.20/0.41    $false),
% 0.20/0.41    inference(avatar_sat_refutation,[],[f38,f52,f66])).
% 0.20/0.41  fof(f66,plain,(
% 0.20/0.41    ~spl4_1 | spl4_2),
% 0.20/0.41    inference(avatar_contradiction_clause,[],[f65])).
% 0.20/0.41  fof(f65,plain,(
% 0.20/0.41    $false | (~spl4_1 | spl4_2)),
% 0.20/0.41    inference(subsumption_resolution,[],[f64,f57])).
% 0.20/0.41  fof(f57,plain,(
% 0.20/0.41    k1_xboole_0 != k1_relat_1(sK2) | spl4_2),
% 0.20/0.41    inference(superposition,[],[f36,f44])).
% 0.20/0.41  fof(f44,plain,(
% 0.20/0.41    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)),
% 0.20/0.41    inference(resolution,[],[f28,f20])).
% 0.20/0.41  fof(f20,plain,(
% 0.20/0.41    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.41    inference(cnf_transformation,[],[f11])).
% 0.20/0.41  fof(f11,plain,(
% 0.20/0.41    ? [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.41    inference(flattening,[],[f10])).
% 0.20/0.41  fof(f10,plain,(
% 0.20/0.41    ? [X0,X1,X2] : ((! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.41    inference(ennf_transformation,[],[f9])).
% 0.20/0.41  fof(f9,plain,(
% 0.20/0.41    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))),
% 0.20/0.41    inference(pure_predicate_removal,[],[f8])).
% 0.20/0.41  fof(f8,negated_conjecture,(
% 0.20/0.41    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 0.20/0.41    inference(negated_conjecture,[],[f7])).
% 0.20/0.41  fof(f7,conjecture,(
% 0.20/0.41    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relset_1)).
% 0.20/0.41  fof(f28,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f17])).
% 0.20/0.41  fof(f17,plain,(
% 0.20/0.41    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.41    inference(ennf_transformation,[],[f5])).
% 0.20/0.41  fof(f5,axiom,(
% 0.20/0.41    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.41  fof(f36,plain,(
% 0.20/0.41    k1_xboole_0 != k1_relset_1(sK1,sK0,sK2) | spl4_2),
% 0.20/0.41    inference(avatar_component_clause,[],[f35])).
% 0.20/0.41  fof(f35,plain,(
% 0.20/0.41    spl4_2 <=> k1_xboole_0 = k1_relset_1(sK1,sK0,sK2)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.41  fof(f64,plain,(
% 0.20/0.41    k1_xboole_0 = k1_relat_1(sK2) | ~spl4_1),
% 0.20/0.41    inference(subsumption_resolution,[],[f63,f60])).
% 0.20/0.41  fof(f60,plain,(
% 0.20/0.41    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.20/0.41    inference(subsumption_resolution,[],[f59,f20])).
% 0.20/0.41  fof(f59,plain,(
% 0.20/0.41    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.41    inference(superposition,[],[f29,f44])).
% 0.20/0.41  fof(f29,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f18])).
% 0.20/0.41  fof(f18,plain,(
% 0.20/0.41    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.41    inference(ennf_transformation,[],[f4])).
% 0.20/0.41  fof(f4,axiom,(
% 0.20/0.41    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.20/0.41  fof(f63,plain,(
% 0.20/0.41    ~m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) | k1_xboole_0 = k1_relat_1(sK2) | ~spl4_1),
% 0.20/0.41    inference(duplicate_literal_removal,[],[f62])).
% 0.20/0.41  fof(f62,plain,(
% 0.20/0.41    ~m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) | k1_xboole_0 = k1_relat_1(sK2) | ~m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) | ~spl4_1),
% 0.20/0.41    inference(resolution,[],[f54,f24])).
% 0.20/0.41  fof(f24,plain,(
% 0.20/0.41    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),X0) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f14])).
% 0.20/0.41  fof(f14,plain,(
% 0.20/0.41    ! [X0,X1] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.41    inference(flattening,[],[f13])).
% 0.20/0.41  fof(f13,plain,(
% 0.20/0.41    ! [X0,X1] : ((? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.41    inference(ennf_transformation,[],[f1])).
% 0.20/0.41  fof(f1,axiom,(
% 0.20/0.41    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).
% 0.20/0.41  fof(f54,plain,(
% 0.20/0.41    ( ! [X0] : (~m1_subset_1(sK3(X0,k1_relat_1(sK2)),sK1) | ~m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(X0))) ) | ~spl4_1),
% 0.20/0.41    inference(forward_demodulation,[],[f53,f44])).
% 0.20/0.41  fof(f53,plain,(
% 0.20/0.41    ( ! [X0] : (~m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(X0)) | ~m1_subset_1(sK3(X0,k1_relset_1(sK1,sK0,sK2)),sK1)) ) | ~spl4_1),
% 0.20/0.41    inference(forward_demodulation,[],[f33,f44])).
% 0.20/0.41  fof(f33,plain,(
% 0.20/0.41    ( ! [X0] : (~m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(X0)) | ~m1_subset_1(sK3(X0,k1_relset_1(sK1,sK0,sK2)),sK1)) ) | ~spl4_1),
% 0.20/0.41    inference(avatar_component_clause,[],[f32])).
% 0.20/0.41  fof(f32,plain,(
% 0.20/0.41    spl4_1 <=> ! [X0] : (~m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(X0)) | ~m1_subset_1(sK3(X0,k1_relset_1(sK1,sK0,sK2)),sK1))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.41  fof(f52,plain,(
% 0.20/0.41    ~spl4_2),
% 0.20/0.41    inference(avatar_contradiction_clause,[],[f51])).
% 0.20/0.41  fof(f51,plain,(
% 0.20/0.41    $false | ~spl4_2),
% 0.20/0.41    inference(resolution,[],[f50,f20])).
% 0.20/0.41  fof(f50,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_2),
% 0.20/0.41    inference(resolution,[],[f49,f26])).
% 0.20/0.41  fof(f26,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f15])).
% 0.20/0.41  fof(f15,plain,(
% 0.20/0.41    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.41    inference(ennf_transformation,[],[f3])).
% 0.20/0.41  fof(f3,axiom,(
% 0.20/0.41    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.41  fof(f49,plain,(
% 0.20/0.41    ~v1_relat_1(sK2) | ~spl4_2),
% 0.20/0.41    inference(subsumption_resolution,[],[f48,f43])).
% 0.20/0.41  fof(f43,plain,(
% 0.20/0.41    k1_xboole_0 != k2_relat_1(sK2)),
% 0.20/0.41    inference(superposition,[],[f21,f40])).
% 0.20/0.41  fof(f40,plain,(
% 0.20/0.41    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)),
% 0.20/0.41    inference(resolution,[],[f27,f20])).
% 0.20/0.41  fof(f27,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f16])).
% 0.20/0.41  fof(f16,plain,(
% 0.20/0.41    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.41    inference(ennf_transformation,[],[f6])).
% 0.20/0.41  fof(f6,axiom,(
% 0.20/0.41    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.41  fof(f21,plain,(
% 0.20/0.41    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)),
% 0.20/0.41    inference(cnf_transformation,[],[f11])).
% 0.20/0.41  fof(f48,plain,(
% 0.20/0.41    k1_xboole_0 = k2_relat_1(sK2) | ~v1_relat_1(sK2) | ~spl4_2),
% 0.20/0.41    inference(trivial_inequality_removal,[],[f47])).
% 0.20/0.41  fof(f47,plain,(
% 0.20/0.41    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_relat_1(sK2) | ~v1_relat_1(sK2) | ~spl4_2),
% 0.20/0.41    inference(superposition,[],[f23,f46])).
% 0.20/0.41  fof(f46,plain,(
% 0.20/0.41    k1_xboole_0 = k1_relat_1(sK2) | ~spl4_2),
% 0.20/0.41    inference(forward_demodulation,[],[f44,f37])).
% 0.20/0.41  fof(f37,plain,(
% 0.20/0.41    k1_xboole_0 = k1_relset_1(sK1,sK0,sK2) | ~spl4_2),
% 0.20/0.41    inference(avatar_component_clause,[],[f35])).
% 0.20/0.41  fof(f23,plain,(
% 0.20/0.41    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f12])).
% 0.20/0.41  fof(f12,plain,(
% 0.20/0.41    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.41    inference(ennf_transformation,[],[f2])).
% 0.20/0.41  fof(f2,axiom,(
% 0.20/0.41    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 0.20/0.41  fof(f38,plain,(
% 0.20/0.41    spl4_1 | spl4_2),
% 0.20/0.41    inference(avatar_split_clause,[],[f30,f35,f32])).
% 0.20/0.41  fof(f30,plain,(
% 0.20/0.41    ( ! [X0] : (k1_xboole_0 = k1_relset_1(sK1,sK0,sK2) | ~m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(X0)) | ~m1_subset_1(sK3(X0,k1_relset_1(sK1,sK0,sK2)),sK1)) )),
% 0.20/0.41    inference(resolution,[],[f25,f19])).
% 0.20/0.41  fof(f19,plain,(
% 0.20/0.41    ( ! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) | ~m1_subset_1(X3,sK1)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f11])).
% 0.20/0.41  fof(f25,plain,(
% 0.20/0.41    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f14])).
% 0.20/0.41  % SZS output end Proof for theBenchmark
% 0.20/0.41  % (18128)------------------------------
% 0.20/0.41  % (18128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (18128)Termination reason: Refutation
% 0.20/0.41  
% 0.20/0.41  % (18128)Memory used [KB]: 10618
% 0.20/0.41  % (18128)Time elapsed: 0.004 s
% 0.20/0.41  % (18128)------------------------------
% 0.20/0.41  % (18128)------------------------------
% 0.20/0.41  % (18127)Success in time 0.059 s
%------------------------------------------------------------------------------
