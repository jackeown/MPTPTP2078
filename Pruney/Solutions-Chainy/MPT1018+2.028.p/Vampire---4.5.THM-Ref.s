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
% Statistics : Number of formulae       :   44 ( 105 expanded)
%              Number of leaves         :    8 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  156 ( 680 expanded)
%              Number of equality atoms :   44 ( 192 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f109,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f98,f108])).

fof(f108,plain,(
    ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f107])).

fof(f107,plain,
    ( $false
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f104,f24])).

fof(f24,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f104,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f40,f52])).

fof(f52,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f40,plain,(
    ~ r1_tarski(sK0,sK3) ),
    inference(resolution,[],[f19,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f19,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( sK2 != sK3
    & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    & r2_hidden(sK3,sK0)
    & r2_hidden(sK2,sK0)
    & v2_funct_1(sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f12,f11])).

fof(f11,plain,
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

fof(f12,plain,
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

fof(f7,plain,(
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
    inference(flattening,[],[f6])).

fof(f6,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
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
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
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

fof(f98,plain,(
    ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f97])).

fof(f97,plain,
    ( $false
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f96,f21])).

fof(f21,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f13])).

fof(f96,plain,
    ( sK2 = sK3
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f77,f75])).

fof(f75,plain,
    ( sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl4_5 ),
    inference(resolution,[],[f55,f18])).

fof(f18,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f55,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl4_5
  <=> ! [X0] :
        ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f77,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f76,f20])).

fof(f20,plain,(
    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f76,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))
    | ~ spl4_5 ),
    inference(resolution,[],[f55,f19])).

fof(f61,plain,
    ( spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f60,f54,f50])).

fof(f60,plain,(
    ! [X0] :
      ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0
      | k1_xboole_0 = sK0
      | ~ r2_hidden(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f59,f14])).

fof(f14,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f59,plain,(
    ! [X0] :
      ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0
      | k1_xboole_0 = sK0
      | ~ r2_hidden(X0,sK0)
      | ~ v1_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f58,f15])).

fof(f15,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f58,plain,(
    ! [X0] :
      ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0
      | k1_xboole_0 = sK0
      | ~ r2_hidden(X0,sK0)
      | ~ v1_funct_2(sK1,sK0,sK0)
      | ~ v1_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f57,f17])).

fof(f17,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f57,plain,(
    ! [X0] :
      ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0
      | k1_xboole_0 = sK0
      | ~ r2_hidden(X0,sK0)
      | ~ v2_funct_1(sK1)
      | ~ v1_funct_2(sK1,sK0,sK0)
      | ~ v1_funct_1(sK1) ) ),
    inference(resolution,[],[f16,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

fof(f16,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:50:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (30681)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.47  % (30681)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f61,f98,f108])).
% 0.21/0.47  fof(f108,plain,(
% 0.21/0.47    ~spl4_4),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f107])).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    $false | ~spl4_4),
% 0.21/0.47    inference(subsumption_resolution,[],[f104,f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    ~r1_tarski(k1_xboole_0,sK3) | ~spl4_4),
% 0.21/0.47    inference(backward_demodulation,[],[f40,f52])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    k1_xboole_0 = sK0 | ~spl4_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    spl4_4 <=> k1_xboole_0 = sK0),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ~r1_tarski(sK0,sK3)),
% 0.21/0.47    inference(resolution,[],[f19,f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    r2_hidden(sK3,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    (sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0)) & v2_funct_1(sK1) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f12,f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) & v2_funct_1(sK1) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) => (sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.21/0.48    inference(flattening,[],[f6])).
% 0.21/0.48  fof(f6,plain,(
% 0.21/0.48    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & (k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0))) & v2_funct_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.21/0.48    inference(negated_conjecture,[],[f4])).
% 0.21/0.48  fof(f4,conjecture,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_2)).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    ~spl4_5),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f97])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    $false | ~spl4_5),
% 0.21/0.48    inference(subsumption_resolution,[],[f96,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    sK2 != sK3),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    sK2 = sK3 | ~spl4_5),
% 0.21/0.48    inference(forward_demodulation,[],[f77,f75])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~spl4_5),
% 0.21/0.48    inference(resolution,[],[f55,f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    r2_hidden(sK2,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) ) | ~spl4_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    spl4_5 <=> ! [X0] : (k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 | ~r2_hidden(X0,sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~spl4_5),
% 0.21/0.48    inference(forward_demodulation,[],[f76,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) | ~spl4_5),
% 0.21/0.48    inference(resolution,[],[f55,f19])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    spl4_4 | spl4_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f60,f54,f50])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X0] : (k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 | k1_xboole_0 = sK0 | ~r2_hidden(X0,sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f59,f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    v1_funct_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X0] : (k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 | k1_xboole_0 = sK0 | ~r2_hidden(X0,sK0) | ~v1_funct_1(sK1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f58,f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X0] : (k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 | k1_xboole_0 = sK0 | ~r2_hidden(X0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f57,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    v2_funct_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X0] : (k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 | k1_xboole_0 = sK0 | ~r2_hidden(X0,sK0) | ~v2_funct_1(sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)) )),
% 0.21/0.48    inference(resolution,[],[f16,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.48    inference(flattening,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (30681)------------------------------
% 0.21/0.48  % (30681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (30681)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (30681)Memory used [KB]: 6140
% 0.21/0.48  % (30681)Time elapsed: 0.009 s
% 0.21/0.48  % (30681)------------------------------
% 0.21/0.48  % (30681)------------------------------
% 0.21/0.48  % (30654)Success in time 0.117 s
%------------------------------------------------------------------------------
