%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:00 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 (  92 expanded)
%              Number of leaves         :   16 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :  188 ( 272 expanded)
%              Number of equality atoms :   35 (  58 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f84,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f44,f48,f65,f69,f76,f79])).

fof(f79,plain,
    ( ~ spl4_3
    | spl4_6 ),
    inference(avatar_split_clause,[],[f77,f74,f46])).

fof(f46,plain,
    ( spl4_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f74,plain,
    ( spl4_6
  <=> r1_tarski(k7_relat_1(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f77,plain,
    ( ~ v1_relat_1(sK0)
    | spl4_6 ),
    inference(resolution,[],[f75,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f75,plain,
    ( ~ r1_tarski(k7_relat_1(sK0,sK2),sK0)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f74])).

fof(f76,plain,
    ( ~ spl4_6
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f71,f60,f46,f74])).

fof(f60,plain,
    ( spl4_4
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ r1_tarski(k7_relat_1(sK0,sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f71,plain,
    ( ~ r1_tarski(k7_relat_1(sK0,sK2),sK0)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(resolution,[],[f61,f47])).

fof(f47,plain,
    ( v1_relat_1(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f61,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ r1_tarski(k7_relat_1(sK0,sK2),X0) )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f69,plain,
    ( ~ spl4_3
    | spl4_5 ),
    inference(avatar_split_clause,[],[f67,f63,f46])).

fof(f63,plain,
    ( spl4_5
  <=> k9_relat_1(sK0,sK1) = k2_relat_1(k7_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f67,plain,
    ( ~ v1_relat_1(sK0)
    | spl4_5 ),
    inference(trivial_inequality_removal,[],[f66])).

fof(f66,plain,
    ( k9_relat_1(sK0,sK1) != k9_relat_1(sK0,sK1)
    | ~ v1_relat_1(sK0)
    | spl4_5 ),
    inference(superposition,[],[f64,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f64,plain,
    ( k9_relat_1(sK0,sK1) != k2_relat_1(k7_relat_1(sK0,sK1))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f65,plain,
    ( ~ spl4_2
    | spl4_4
    | ~ spl4_5
    | spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f57,f46,f38,f63,f60,f42])).

fof(f42,plain,
    ( spl4_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f38,plain,
    ( spl4_1
  <=> k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k9_relat_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f57,plain,
    ( ! [X0] :
        ( k9_relat_1(sK0,sK1) != k2_relat_1(k7_relat_1(sK0,sK1))
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(sK1,sK2)
        | ~ r1_tarski(k7_relat_1(sK0,sK2),X0) )
    | spl4_1
    | ~ spl4_3 ),
    inference(superposition,[],[f39,f56])).

fof(f56,plain,
    ( ! [X2,X0,X1] :
        ( k9_relat_1(k7_relat_1(sK0,X0),X1) = k2_relat_1(k7_relat_1(sK0,X1))
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(k7_relat_1(sK0,X0),X2) )
    | ~ spl4_3 ),
    inference(resolution,[],[f55,f35])).

fof(f35,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f55,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k7_relat_1(sK0,X1),k1_zfmisc_1(X2))
        | k9_relat_1(k7_relat_1(sK0,X1),X0) = k2_relat_1(k7_relat_1(sK0,X0))
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_3 ),
    inference(resolution,[],[f54,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f54,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k7_relat_1(sK0,X0),k1_zfmisc_1(X2))
        | ~ r1_tarski(X1,X0)
        | k9_relat_1(k7_relat_1(sK0,X0),X1) = k2_relat_1(k7_relat_1(sK0,X1))
        | ~ v1_relat_1(X2) )
    | ~ spl4_3 ),
    inference(resolution,[],[f52,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f52,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(k7_relat_1(sK0,X0))
        | k9_relat_1(k7_relat_1(sK0,X0),X1) = k2_relat_1(k7_relat_1(sK0,X1))
        | ~ r1_tarski(X1,X0) )
    | ~ spl4_3 ),
    inference(superposition,[],[f28,f50])).

fof(f50,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(k7_relat_1(sK0,X1),X0) = k7_relat_1(sK0,X0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_3 ),
    inference(resolution,[],[f34,f47])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

fof(f39,plain,
    ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f48,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f23,f46])).

fof(f23,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)
    & r1_tarski(sK1,sK2)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f17,f16])).

% (8614)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f16,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1)
            & r1_tarski(X1,X2) )
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1)
          & r1_tarski(X1,X2) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2,X1] :
        ( k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1)
        & r1_tarski(X1,X2) )
   => ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)
      & r1_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1)
          & r1_tarski(X1,X2) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

fof(f44,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f24,f42])).

fof(f24,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f25,f38])).

fof(f25,plain,(
    k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:02:57 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.45  % (8610)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.45  % (8610)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f84,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(avatar_sat_refutation,[],[f40,f44,f48,f65,f69,f76,f79])).
% 0.20/0.45  fof(f79,plain,(
% 0.20/0.45    ~spl4_3 | spl4_6),
% 0.20/0.45    inference(avatar_split_clause,[],[f77,f74,f46])).
% 0.20/0.45  fof(f46,plain,(
% 0.20/0.45    spl4_3 <=> v1_relat_1(sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.45  fof(f74,plain,(
% 0.20/0.45    spl4_6 <=> r1_tarski(k7_relat_1(sK0,sK2),sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.45  fof(f77,plain,(
% 0.20/0.45    ~v1_relat_1(sK0) | spl4_6),
% 0.20/0.45    inference(resolution,[],[f75,f27])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f11])).
% 0.20/0.45  fof(f11,plain,(
% 0.20/0.45    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,axiom,(
% 0.20/0.45    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 0.20/0.45  fof(f75,plain,(
% 0.20/0.45    ~r1_tarski(k7_relat_1(sK0,sK2),sK0) | spl4_6),
% 0.20/0.45    inference(avatar_component_clause,[],[f74])).
% 0.20/0.45  fof(f76,plain,(
% 0.20/0.45    ~spl4_6 | ~spl4_3 | ~spl4_4),
% 0.20/0.45    inference(avatar_split_clause,[],[f71,f60,f46,f74])).
% 0.20/0.45  fof(f60,plain,(
% 0.20/0.45    spl4_4 <=> ! [X0] : (~v1_relat_1(X0) | ~r1_tarski(k7_relat_1(sK0,sK2),X0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.45  fof(f71,plain,(
% 0.20/0.45    ~r1_tarski(k7_relat_1(sK0,sK2),sK0) | (~spl4_3 | ~spl4_4)),
% 0.20/0.45    inference(resolution,[],[f61,f47])).
% 0.20/0.45  fof(f47,plain,(
% 0.20/0.45    v1_relat_1(sK0) | ~spl4_3),
% 0.20/0.45    inference(avatar_component_clause,[],[f46])).
% 0.20/0.45  fof(f61,plain,(
% 0.20/0.45    ( ! [X0] : (~v1_relat_1(X0) | ~r1_tarski(k7_relat_1(sK0,sK2),X0)) ) | ~spl4_4),
% 0.20/0.45    inference(avatar_component_clause,[],[f60])).
% 0.20/0.45  fof(f69,plain,(
% 0.20/0.45    ~spl4_3 | spl4_5),
% 0.20/0.45    inference(avatar_split_clause,[],[f67,f63,f46])).
% 0.20/0.45  fof(f63,plain,(
% 0.20/0.45    spl4_5 <=> k9_relat_1(sK0,sK1) = k2_relat_1(k7_relat_1(sK0,sK1))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.45  fof(f67,plain,(
% 0.20/0.45    ~v1_relat_1(sK0) | spl4_5),
% 0.20/0.45    inference(trivial_inequality_removal,[],[f66])).
% 0.20/0.45  fof(f66,plain,(
% 0.20/0.45    k9_relat_1(sK0,sK1) != k9_relat_1(sK0,sK1) | ~v1_relat_1(sK0) | spl4_5),
% 0.20/0.45    inference(superposition,[],[f64,f28])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f12])).
% 0.20/0.45  fof(f12,plain,(
% 0.20/0.45    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f5])).
% 0.20/0.45  fof(f5,axiom,(
% 0.20/0.45    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.45  fof(f64,plain,(
% 0.20/0.45    k9_relat_1(sK0,sK1) != k2_relat_1(k7_relat_1(sK0,sK1)) | spl4_5),
% 0.20/0.45    inference(avatar_component_clause,[],[f63])).
% 0.20/0.45  fof(f65,plain,(
% 0.20/0.45    ~spl4_2 | spl4_4 | ~spl4_5 | spl4_1 | ~spl4_3),
% 0.20/0.45    inference(avatar_split_clause,[],[f57,f46,f38,f63,f60,f42])).
% 0.20/0.45  fof(f42,plain,(
% 0.20/0.45    spl4_2 <=> r1_tarski(sK1,sK2)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.45  fof(f38,plain,(
% 0.20/0.45    spl4_1 <=> k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k9_relat_1(sK0,sK1)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.45  fof(f57,plain,(
% 0.20/0.45    ( ! [X0] : (k9_relat_1(sK0,sK1) != k2_relat_1(k7_relat_1(sK0,sK1)) | ~v1_relat_1(X0) | ~r1_tarski(sK1,sK2) | ~r1_tarski(k7_relat_1(sK0,sK2),X0)) ) | (spl4_1 | ~spl4_3)),
% 0.20/0.45    inference(superposition,[],[f39,f56])).
% 0.20/0.45  fof(f56,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k9_relat_1(k7_relat_1(sK0,X0),X1) = k2_relat_1(k7_relat_1(sK0,X1)) | ~v1_relat_1(X2) | ~r1_tarski(X1,X0) | ~r1_tarski(k7_relat_1(sK0,X0),X2)) ) | ~spl4_3),
% 0.20/0.45    inference(resolution,[],[f55,f35])).
% 0.20/0.45  fof(f35,plain,(
% 0.20/0.45    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.20/0.45    inference(equality_resolution,[],[f31])).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.45    inference(cnf_transformation,[],[f22])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.45    inference(rectify,[],[f19])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.45    inference(nnf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.20/0.45  fof(f55,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~r2_hidden(k7_relat_1(sK0,X1),k1_zfmisc_1(X2)) | k9_relat_1(k7_relat_1(sK0,X1),X0) = k2_relat_1(k7_relat_1(sK0,X0)) | ~v1_relat_1(X2) | ~r1_tarski(X0,X1)) ) | ~spl4_3),
% 0.20/0.45    inference(resolution,[],[f54,f29])).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f13])).
% 0.20/0.45  fof(f13,plain,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.45  fof(f54,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(k7_relat_1(sK0,X0),k1_zfmisc_1(X2)) | ~r1_tarski(X1,X0) | k9_relat_1(k7_relat_1(sK0,X0),X1) = k2_relat_1(k7_relat_1(sK0,X1)) | ~v1_relat_1(X2)) ) | ~spl4_3),
% 0.20/0.45    inference(resolution,[],[f52,f26])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f10])).
% 0.20/0.45  fof(f10,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.45  fof(f52,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~v1_relat_1(k7_relat_1(sK0,X0)) | k9_relat_1(k7_relat_1(sK0,X0),X1) = k2_relat_1(k7_relat_1(sK0,X1)) | ~r1_tarski(X1,X0)) ) | ~spl4_3),
% 0.20/0.45    inference(superposition,[],[f28,f50])).
% 0.20/0.45  fof(f50,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK0,X1),X0) = k7_relat_1(sK0,X0) | ~r1_tarski(X0,X1)) ) | ~spl4_3),
% 0.20/0.45    inference(resolution,[],[f34,f47])).
% 0.20/0.45  fof(f34,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f15])).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.20/0.45    inference(flattening,[],[f14])).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    ! [X0,X1,X2] : ((k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.45    inference(ennf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).
% 0.20/0.45  fof(f39,plain,(
% 0.20/0.45    k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1) | spl4_1),
% 0.20/0.45    inference(avatar_component_clause,[],[f38])).
% 0.20/0.45  fof(f48,plain,(
% 0.20/0.45    spl4_3),
% 0.20/0.45    inference(avatar_split_clause,[],[f23,f46])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    v1_relat_1(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f18])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    (k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1) & r1_tarski(sK1,sK2)) & v1_relat_1(sK0)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f17,f16])).
% 0.20/0.45  % (8614)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    ? [X0] : (? [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1) & r1_tarski(X1,X2)) & v1_relat_1(X0)) => (? [X2,X1] : (k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1) & r1_tarski(X1,X2)) & v1_relat_1(sK0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ? [X2,X1] : (k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1) & r1_tarski(X1,X2)) => (k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1) & r1_tarski(sK1,sK2))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f9,plain,(
% 0.20/0.45    ? [X0] : (? [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1) & r1_tarski(X1,X2)) & v1_relat_1(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f8])).
% 0.20/0.45  fof(f8,negated_conjecture,(
% 0.20/0.45    ~! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 0.20/0.45    inference(negated_conjecture,[],[f7])).
% 0.20/0.45  fof(f7,conjecture,(
% 0.20/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).
% 0.20/0.45  fof(f44,plain,(
% 0.20/0.45    spl4_2),
% 0.20/0.45    inference(avatar_split_clause,[],[f24,f42])).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    r1_tarski(sK1,sK2)),
% 0.20/0.45    inference(cnf_transformation,[],[f18])).
% 0.20/0.45  fof(f40,plain,(
% 0.20/0.45    ~spl4_1),
% 0.20/0.45    inference(avatar_split_clause,[],[f25,f38])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)),
% 0.20/0.45    inference(cnf_transformation,[],[f18])).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (8610)------------------------------
% 0.20/0.45  % (8610)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (8610)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (8610)Memory used [KB]: 10618
% 0.20/0.45  % (8610)Time elapsed: 0.007 s
% 0.20/0.45  % (8610)------------------------------
% 0.20/0.45  % (8610)------------------------------
% 0.20/0.46  % (8614)Refutation not found, incomplete strategy% (8614)------------------------------
% 0.20/0.46  % (8614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (8614)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (8614)Memory used [KB]: 6140
% 0.20/0.46  % (8614)Time elapsed: 0.058 s
% 0.20/0.46  % (8614)------------------------------
% 0.20/0.46  % (8614)------------------------------
% 0.20/0.46  % (8603)Success in time 0.115 s
%------------------------------------------------------------------------------
