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
% DateTime   : Thu Dec  3 12:53:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 112 expanded)
%              Number of leaves         :   13 (  42 expanded)
%              Depth                    :    7
%              Number of atoms          :  137 ( 271 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f83,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f38,f47,f56,f57,f64,f74,f75,f76,f82])).

fof(f82,plain,
    ( ~ spl3_3
    | spl3_7 ),
    inference(avatar_contradiction_clause,[],[f80])).

fof(f80,plain,
    ( $false
    | ~ spl3_3
    | spl3_7 ),
    inference(unit_resulting_resolution,[],[f39,f63,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f63,plain,
    ( ~ m1_subset_1(k8_relat_1(sK0,sK2),k1_zfmisc_1(sK2))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl3_7
  <=> m1_subset_1(k8_relat_1(sK0,sK2),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f39,plain,
    ( ! [X0] : r1_tarski(k8_relat_1(X0,sK2),sK2)
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f37,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

fof(f37,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f76,plain,
    ( ~ spl3_3
    | spl3_6 ),
    inference(avatar_contradiction_clause,[],[f69])).

fof(f69,plain,
    ( $false
    | ~ spl3_3
    | spl3_6 ),
    inference(unit_resulting_resolution,[],[f37,f55,f20])).

fof(f55,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK2),sK2)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl3_6
  <=> r1_tarski(k8_relat_1(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f75,plain,
    ( ~ spl3_3
    | spl3_6 ),
    inference(avatar_contradiction_clause,[],[f67])).

fof(f67,plain,
    ( $false
    | ~ spl3_3
    | spl3_6 ),
    inference(unit_resulting_resolution,[],[f39,f55])).

fof(f74,plain,
    ( ~ spl3_3
    | spl3_6 ),
    inference(avatar_contradiction_clause,[],[f71])).

fof(f71,plain,
    ( $false
    | ~ spl3_3
    | spl3_6 ),
    inference(resolution,[],[f55,f39])).

fof(f64,plain,
    ( ~ spl3_7
    | ~ spl3_3
    | spl3_5 ),
    inference(avatar_split_clause,[],[f58,f49,f35,f61])).

fof(f49,plain,
    ( spl3_5
  <=> v1_relat_1(k8_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f58,plain,
    ( ~ m1_subset_1(k8_relat_1(sK0,sK2),k1_zfmisc_1(sK2))
    | ~ spl3_3
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f37,f51,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f51,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f49])).

fof(f57,plain,
    ( ~ spl3_4
    | spl3_1 ),
    inference(avatar_split_clause,[],[f42,f25,f44])).

fof(f44,plain,
    ( spl3_4
  <=> m1_subset_1(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k1_zfmisc_1(k9_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f25,plain,
    ( spl3_1
  <=> r1_tarski(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f42,plain,
    ( ~ m1_subset_1(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k1_zfmisc_1(k9_relat_1(sK2,sK1)))
    | spl3_1 ),
    inference(resolution,[],[f27,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f27,plain,
    ( ~ r1_tarski(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f56,plain,
    ( ~ spl3_5
    | ~ spl3_3
    | ~ spl3_6
    | spl3_1 ),
    inference(avatar_split_clause,[],[f41,f25,f53,f35,f49])).

fof(f41,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK2),sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | spl3_1 ),
    inference(resolution,[],[f27,f21])).

% (8714)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_relat_1)).

fof(f47,plain,
    ( ~ spl3_4
    | spl3_1 ),
    inference(avatar_split_clause,[],[f40,f25,f44])).

fof(f40,plain,
    ( ~ m1_subset_1(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k1_zfmisc_1(k9_relat_1(sK2,sK1)))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f27,f22])).

fof(f38,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f16,f35])).

fof(f16,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_tarski(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

% (8727)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_funct_1)).

fof(f33,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f17,f30])).

fof(f30,plain,
    ( spl3_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f17,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f28,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f18,f25])).

fof(f18,plain,(
    ~ r1_tarski(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:58:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.43  % (8726)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.22/0.49  % (8729)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.22/0.49  % (8726)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f28,f33,f38,f47,f56,f57,f64,f74,f75,f76,f82])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    ~spl3_3 | spl3_7),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f80])).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    $false | (~spl3_3 | spl3_7)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f39,f63,f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.49    inference(nnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    ~m1_subset_1(k8_relat_1(sK0,sK2),k1_zfmisc_1(sK2)) | spl3_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f61])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    spl3_7 <=> m1_subset_1(k8_relat_1(sK0,sK2),k1_zfmisc_1(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X0] : (r1_tarski(k8_relat_1(X0,sK2),sK2)) ) | ~spl3_3),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f37,f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    v1_relat_1(sK2) | ~spl3_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    spl3_3 <=> v1_relat_1(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    ~spl3_3 | spl3_6),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f69])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    $false | (~spl3_3 | spl3_6)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f37,f55,f20])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ~r1_tarski(k8_relat_1(sK0,sK2),sK2) | spl3_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f53])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    spl3_6 <=> r1_tarski(k8_relat_1(sK0,sK2),sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    ~spl3_3 | spl3_6),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f67])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    $false | (~spl3_3 | spl3_6)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f39,f55])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    ~spl3_3 | spl3_6),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f71])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    $false | (~spl3_3 | spl3_6)),
% 0.22/0.49    inference(resolution,[],[f55,f39])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    ~spl3_7 | ~spl3_3 | spl3_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f58,f49,f35,f61])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    spl3_5 <=> v1_relat_1(k8_relat_1(sK0,sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    ~m1_subset_1(k8_relat_1(sK0,sK2),k1_zfmisc_1(sK2)) | (~spl3_3 | spl3_5)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f37,f51,f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ~v1_relat_1(k8_relat_1(sK0,sK2)) | spl3_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f49])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    ~spl3_4 | spl3_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f42,f25,f44])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    spl3_4 <=> m1_subset_1(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k1_zfmisc_1(k9_relat_1(sK2,sK1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    spl3_1 <=> r1_tarski(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ~m1_subset_1(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k1_zfmisc_1(k9_relat_1(sK2,sK1))) | spl3_1),
% 0.22/0.49    inference(resolution,[],[f27,f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ~r1_tarski(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1)) | spl3_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f25])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ~spl3_5 | ~spl3_3 | ~spl3_6 | spl3_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f41,f25,f53,f35,f49])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ~r1_tarski(k8_relat_1(sK0,sK2),sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(k8_relat_1(sK0,sK2)) | spl3_1),
% 0.22/0.49    inference(resolution,[],[f27,f21])).
% 0.22/0.49  % (8714)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : ((r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_relat_1)).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ~spl3_4 | spl3_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f40,f25,f44])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ~m1_subset_1(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k1_zfmisc_1(k9_relat_1(sK2,sK1))) | spl3_1),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f27,f22])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    spl3_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f16,f35])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    v1_relat_1(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ~r1_tarski(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f8,plain,(
% 0.22/0.49    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.49    inference(flattening,[],[f7])).
% 0.22/0.49  fof(f7,plain,(
% 0.22/0.49    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  % (8727)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.22/0.49  fof(f6,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1)))),
% 0.22/0.49    inference(negated_conjecture,[],[f5])).
% 0.22/0.49  fof(f5,conjecture,(
% 0.22/0.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_funct_1)).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    spl3_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f17,f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    spl3_2 <=> v1_funct_1(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    v1_funct_1(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ~spl3_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f18,f25])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ~r1_tarski(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1))),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (8726)------------------------------
% 0.22/0.49  % (8726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (8726)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (8726)Memory used [KB]: 5373
% 0.22/0.49  % (8726)Time elapsed: 0.066 s
% 0.22/0.49  % (8726)------------------------------
% 0.22/0.49  % (8726)------------------------------
% 0.22/0.49  % (8713)Success in time 0.127 s
%------------------------------------------------------------------------------
