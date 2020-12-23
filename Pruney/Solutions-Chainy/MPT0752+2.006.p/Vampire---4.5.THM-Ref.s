%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 (  53 expanded)
%              Number of leaves         :   13 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :  100 ( 110 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f57,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f46,f49,f52,f56])).

fof(f56,plain,(
    spl1_1 ),
    inference(avatar_contradiction_clause,[],[f55])).

fof(f55,plain,
    ( $false
    | spl1_1 ),
    inference(subsumption_resolution,[],[f54,f31])).

fof(f31,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl1_1
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f54,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f53,f22])).

fof(f22,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4))))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f27,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_relat_1)).

fof(f52,plain,(
    spl1_3 ),
    inference(avatar_contradiction_clause,[],[f51])).

fof(f51,plain,
    ( $false
    | spl1_3 ),
    inference(subsumption_resolution,[],[f50,f21])).

fof(f21,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f50,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl1_3 ),
    inference(resolution,[],[f24,f39])).

fof(f39,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | spl1_3 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl1_3
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f24,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f49,plain,(
    spl1_4 ),
    inference(avatar_contradiction_clause,[],[f48])).

fof(f48,plain,
    ( $false
    | spl1_4 ),
    inference(subsumption_resolution,[],[f47,f21])).

fof(f47,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl1_4 ),
    inference(resolution,[],[f23,f43])).

fof(f43,plain,
    ( ~ v5_ordinal1(k1_xboole_0)
    | spl1_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl1_4
  <=> v5_ordinal1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f23,plain,(
    ! [X0] :
      ( v5_ordinal1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v5_ordinal1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v5_ordinal1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_ordinal1)).

fof(f46,plain,(
    spl1_2 ),
    inference(avatar_contradiction_clause,[],[f45])).

fof(f45,plain,
    ( $false
    | spl1_2 ),
    inference(resolution,[],[f26,f35])).

fof(f35,plain,
    ( ~ v5_relat_1(k1_xboole_0,sK0)
    | spl1_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl1_2
  <=> v5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f26,plain,(
    ! [X1] : v5_relat_1(k1_xboole_0,X1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X1] : v5_relat_1(k1_xboole_0,X1) ),
    inference(rectify,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] : v5_relat_1(k1_xboole_0,X1) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t206_relat_1)).

fof(f44,plain,
    ( ~ spl1_1
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f20,f41,f37,f33,f29])).

fof(f20,plain,
    ( ~ v5_ordinal1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ v5_ordinal1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ~ v5_ordinal1(k1_xboole_0)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v5_relat_1(k1_xboole_0,X0)
        | ~ v1_relat_1(k1_xboole_0) )
   => ( ~ v5_ordinal1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v5_relat_1(k1_xboole_0,sK0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ~ v5_ordinal1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v5_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v5_ordinal1(k1_xboole_0)
        & v1_funct_1(k1_xboole_0)
        & v5_relat_1(k1_xboole_0,X0)
        & v1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( v5_ordinal1(k1_xboole_0)
      & v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:22:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (31849)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.21/0.49  % (31849)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f44,f46,f49,f52,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    spl1_1),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    $false | spl1_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f54,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ~v1_relat_1(k1_xboole_0) | spl1_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    spl1_1 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    v1_relat_1(k1_xboole_0)),
% 0.21/0.49    inference(resolution,[],[f53,f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4)))) | v1_relat_1(X0)) )),
% 0.21/0.49    inference(resolution,[],[f27,f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_relat_1)).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    spl1_3),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    $false | spl1_3),
% 0.21/0.49    inference(subsumption_resolution,[],[f50,f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ~v1_xboole_0(k1_xboole_0) | spl1_3),
% 0.21/0.49    inference(resolution,[],[f24,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ~v1_funct_1(k1_xboole_0) | spl1_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    spl1_3 <=> v1_funct_1(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    spl1_4),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    $false | spl1_4),
% 0.21/0.49    inference(subsumption_resolution,[],[f47,f21])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ~v1_xboole_0(k1_xboole_0) | spl1_4),
% 0.21/0.49    inference(resolution,[],[f23,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ~v5_ordinal1(k1_xboole_0) | spl1_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    spl1_4 <=> v5_ordinal1(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ( ! [X0] : (v5_ordinal1(X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (v5_ordinal1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(X0) => v5_ordinal1(X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_ordinal1)).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    spl1_2),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    $false | spl1_2),
% 0.21/0.49    inference(resolution,[],[f26,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ~v5_relat_1(k1_xboole_0,sK0) | spl1_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    spl1_2 <=> v5_relat_1(k1_xboole_0,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X1] : (v5_relat_1(k1_xboole_0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X1] : v5_relat_1(k1_xboole_0,X1)),
% 0.21/0.49    inference(rectify,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0,X1] : v5_relat_1(k1_xboole_0,X1)),
% 0.21/0.49    inference(pure_predicate_removal,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : (v5_relat_1(k1_xboole_0,X1) & v4_relat_1(k1_xboole_0,X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t206_relat_1)).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ~spl1_1 | ~spl1_2 | ~spl1_3 | ~spl1_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f20,f41,f37,f33,f29])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(k1_xboole_0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ? [X0] : (~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) => (~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(k1_xboole_0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ? [X0] : (~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 0.21/0.49    inference(negated_conjecture,[],[f9])).
% 0.21/0.49  fof(f9,conjecture,(
% 0.21/0.49    ! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (31849)------------------------------
% 0.21/0.49  % (31849)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (31849)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (31849)Memory used [KB]: 5373
% 0.21/0.49  % (31849)Time elapsed: 0.062 s
% 0.21/0.49  % (31849)------------------------------
% 0.21/0.49  % (31849)------------------------------
% 0.21/0.49  % (31848)Success in time 0.131 s
%------------------------------------------------------------------------------
