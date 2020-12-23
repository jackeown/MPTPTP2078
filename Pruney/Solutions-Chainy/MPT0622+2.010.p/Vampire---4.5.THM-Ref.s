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
% DateTime   : Thu Dec  3 12:52:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 454 expanded)
%              Number of leaves         :   14 ( 108 expanded)
%              Depth                    :   18
%              Number of atoms          :  205 (1906 expanded)
%              Number of equality atoms :   61 ( 935 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f267,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f208,f235,f239,f266])).

fof(f266,plain,(
    ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f261])).

fof(f261,plain,
    ( $false
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f92,f177,f234])).

fof(f234,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK1))
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl7_4
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f177,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK4(sK1,sK2)),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f156,f141])).

% (1312)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f141,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | sK0 = X0 ) ),
    inference(superposition,[],[f139,f71])).

fof(f71,plain,(
    k2_relat_1(sK1) = k9_relat_1(sK2,k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f70,f63])).

fof(f63,plain,(
    k2_relat_1(sK1) = k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f57,f58])).

fof(f58,plain,(
    k2_relat_1(sK1) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f28,f56])).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f53,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f28,plain,(
    k1_tarski(sK0) = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k1_tarski(X0) = k2_relat_1(X2)
          & k1_tarski(X0) = k2_relat_1(X1)
          & k1_relat_1(X2) = k1_relat_1(X1)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k1_tarski(X0) = k2_relat_1(X2)
          & k1_tarski(X0) = k2_relat_1(X1)
          & k1_relat_1(X2) = k1_relat_1(X1)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( ( k1_tarski(X0) = k2_relat_1(X2)
                & k1_tarski(X0) = k2_relat_1(X1)
                & k1_relat_1(X2) = k1_relat_1(X1) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( ( k1_tarski(X0) = k2_relat_1(X2)
              & k1_tarski(X0) = k2_relat_1(X1)
              & k1_relat_1(X2) = k1_relat_1(X1) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_1)).

fof(f57,plain,(
    k2_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f29,f56])).

fof(f29,plain,(
    k1_tarski(sK0) = k2_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f70,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f65,f27])).

fof(f27,plain,(
    k1_relat_1(sK2) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f65,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f25,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f25,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f139,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k9_relat_1(sK2,X3))
      | sK0 = X2 ) ),
    inference(resolution,[],[f66,f131])).

fof(f131,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),sK2)
      | sK0 = X2 ) ),
    inference(resolution,[],[f100,f108])).

fof(f108,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f73,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f73,plain,(
    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f72,f27])).

fof(f72,plain,(
    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f64,f63])).

fof(f64,plain,(
    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) ),
    inference(unit_resulting_resolution,[],[f25,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f100,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X5,k2_relat_1(sK1)))
      | sK0 = X4 ) ),
    inference(superposition,[],[f60,f58])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))
      | X1 = X3 ) ),
    inference(definition_unfolding,[],[f37,f56])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1,sK2),X0),sK2)
      | ~ r2_hidden(X0,k9_relat_1(sK2,X1)) ) ),
    inference(resolution,[],[f25,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f156,plain,(
    sK0 != k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(backward_demodulation,[],[f93,f142])).

fof(f142,plain,(
    sK0 = k1_funct_1(sK1,sK4(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f102,f141])).

fof(f102,plain,(
    r2_hidden(k1_funct_1(sK1,sK4(sK1,sK2)),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f31,f32,f92,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

fof(f32,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f31,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f93,plain,(
    k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f25,f31,f32,f26,f30,f27,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

fof(f30,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f15])).

fof(f26,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f92,plain,(
    r2_hidden(sK4(sK1,sK2),k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f25,f31,f32,f26,f30,f27,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f239,plain,(
    spl7_3 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | spl7_3 ),
    inference(unit_resulting_resolution,[],[f26,f231])).

fof(f231,plain,
    ( ~ v1_funct_1(sK2)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl7_3
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f235,plain,
    ( ~ spl7_1
    | ~ spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f98,f233,f229,f198])).

fof(f198,plain,
    ( spl7_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f98,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK1))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(forward_demodulation,[],[f97,f27])).

fof(f97,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK1))
      | ~ v1_funct_1(sK2)
      | ~ r2_hidden(X0,k1_relat_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f33,f63])).

fof(f208,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f205])).

fof(f205,plain,
    ( $false
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f25,f200])).

fof(f200,plain,
    ( ~ v1_relat_1(sK2)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f198])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:10:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (1305)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (1313)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (1311)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (1305)Refutation not found, incomplete strategy% (1305)------------------------------
% 0.22/0.52  % (1305)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (1305)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (1305)Memory used [KB]: 1663
% 0.22/0.52  % (1305)Time elapsed: 0.103 s
% 0.22/0.52  % (1305)------------------------------
% 0.22/0.52  % (1305)------------------------------
% 0.22/0.52  % (1329)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (1308)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (1320)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (1307)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (1310)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (1324)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.53  % (1309)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (1323)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (1334)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (1309)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f267,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f208,f235,f239,f266])).
% 0.22/0.54  fof(f266,plain,(
% 0.22/0.54    ~spl7_4),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f261])).
% 0.22/0.54  fof(f261,plain,(
% 0.22/0.54    $false | ~spl7_4),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f92,f177,f234])).
% 0.22/0.54  fof(f234,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | ~spl7_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f233])).
% 0.22/0.54  fof(f233,plain,(
% 0.22/0.54    spl7_4 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK1)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.54  fof(f177,plain,(
% 0.22/0.54    ~r2_hidden(k1_funct_1(sK2,sK4(sK1,sK2)),k2_relat_1(sK1))),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f156,f141])).
% 0.22/0.54  % (1312)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  fof(f141,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | sK0 = X0) )),
% 0.22/0.54    inference(superposition,[],[f139,f71])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    k2_relat_1(sK1) = k9_relat_1(sK2,k1_relat_1(sK1))),
% 0.22/0.54    inference(forward_demodulation,[],[f70,f63])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    k2_relat_1(sK1) = k2_relat_1(sK2)),
% 0.22/0.54    inference(backward_demodulation,[],[f57,f58])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    k2_relat_1(sK1) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.22/0.54    inference(definition_unfolding,[],[f28,f56])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f39,f55])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f53,f54])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    k1_tarski(sK0) = k2_relat_1(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ? [X0,X1] : (? [X2] : (X1 != X2 & k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X2) = k1_relat_1(X1) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.54    inference(flattening,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ? [X0,X1] : (? [X2] : ((X1 != X2 & (k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X2) = k1_relat_1(X1))) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X2) = k1_relat_1(X1)) => X1 = X2)))),
% 0.22/0.54    inference(negated_conjecture,[],[f12])).
% 0.22/0.54  fof(f12,conjecture,(
% 0.22/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X2) = k1_relat_1(X1)) => X1 = X2)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_1)).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    k2_relat_1(sK2) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.22/0.54    inference(definition_unfolding,[],[f29,f56])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    k1_tarski(sK0) = k2_relat_1(sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK1))),
% 0.22/0.54    inference(forward_demodulation,[],[f65,f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    k1_relat_1(sK2) = k1_relat_1(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f25,f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    v1_relat_1(sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f139,plain,(
% 0.22/0.54    ( ! [X2,X3] : (~r2_hidden(X2,k9_relat_1(sK2,X3)) | sK0 = X2) )),
% 0.22/0.54    inference(resolution,[],[f66,f131])).
% 0.22/0.54  fof(f131,plain,(
% 0.22/0.54    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X3,X2),sK2) | sK0 = X2) )),
% 0.22/0.54    inference(resolution,[],[f100,f108])).
% 0.22/0.54  fof(f108,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) | ~r2_hidden(X0,sK2)) )),
% 0.22/0.54    inference(resolution,[],[f73,f46])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))),
% 0.22/0.54    inference(forward_demodulation,[],[f72,f27])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK1)))),
% 0.22/0.54    inference(forward_demodulation,[],[f64,f63])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f25,f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 0.22/0.54  fof(f100,plain,(
% 0.22/0.54    ( ! [X4,X5,X3] : (~r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X5,k2_relat_1(sK1))) | sK0 = X4) )),
% 0.22/0.54    inference(superposition,[],[f60,f58])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))) | X1 = X3) )),
% 0.22/0.54    inference(definition_unfolding,[],[f37,f56])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (X1 = X3 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK6(X0,X1,sK2),X0),sK2) | ~r2_hidden(X0,k9_relat_1(sK2,X1))) )),
% 0.22/0.54    inference(resolution,[],[f25,f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.22/0.54  fof(f156,plain,(
% 0.22/0.54    sK0 != k1_funct_1(sK2,sK4(sK1,sK2))),
% 0.22/0.54    inference(backward_demodulation,[],[f93,f142])).
% 0.22/0.54  fof(f142,plain,(
% 0.22/0.54    sK0 = k1_funct_1(sK1,sK4(sK1,sK2))),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f102,f141])).
% 0.22/0.54  fof(f102,plain,(
% 0.22/0.54    r2_hidden(k1_funct_1(sK1,sK4(sK1,sK2)),k2_relat_1(sK1))),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f31,f32,f92,f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(flattening,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    v1_funct_1(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    v1_relat_1(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f93,plain,(
% 0.22/0.54    k1_funct_1(sK1,sK4(sK1,sK2)) != k1_funct_1(sK2,sK4(sK1,sK2))),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f25,f31,f32,f26,f30,f27,f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X0) != k1_relat_1(X1) | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | X0 = X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(flattening,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    sK1 != sK2),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    v1_funct_1(sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f92,plain,(
% 0.22/0.54    r2_hidden(sK4(sK1,sK2),k1_relat_1(sK1))),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f25,f31,f32,f26,f30,f27,f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X0) | X0 = X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f239,plain,(
% 0.22/0.54    spl7_3),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f236])).
% 0.22/0.54  fof(f236,plain,(
% 0.22/0.54    $false | spl7_3),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f26,f231])).
% 0.22/0.54  fof(f231,plain,(
% 0.22/0.54    ~v1_funct_1(sK2) | spl7_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f229])).
% 0.22/0.54  fof(f229,plain,(
% 0.22/0.54    spl7_3 <=> v1_funct_1(sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.54  fof(f235,plain,(
% 0.22/0.54    ~spl7_1 | ~spl7_3 | spl7_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f98,f233,f229,f198])).
% 0.22/0.54  fof(f198,plain,(
% 0.22/0.54    spl7_1 <=> v1_relat_1(sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.54  fof(f98,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f97,f27])).
% 0.22/0.54  fof(f97,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK1)) | ~v1_funct_1(sK2) | ~r2_hidden(X0,k1_relat_1(sK2)) | ~v1_relat_1(sK2)) )),
% 0.22/0.54    inference(superposition,[],[f33,f63])).
% 0.22/0.54  fof(f208,plain,(
% 0.22/0.54    spl7_1),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f205])).
% 0.22/0.54  fof(f205,plain,(
% 0.22/0.54    $false | spl7_1),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f25,f200])).
% 0.22/0.54  fof(f200,plain,(
% 0.22/0.54    ~v1_relat_1(sK2) | spl7_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f198])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (1309)------------------------------
% 0.22/0.54  % (1309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (1309)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (1309)Memory used [KB]: 6396
% 0.22/0.54  % (1309)Time elapsed: 0.120 s
% 0.22/0.54  % (1309)------------------------------
% 0.22/0.54  % (1309)------------------------------
% 0.22/0.54  % (1322)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (1322)Refutation not found, incomplete strategy% (1322)------------------------------
% 0.22/0.54  % (1322)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (1322)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (1322)Memory used [KB]: 10618
% 0.22/0.54  % (1322)Time elapsed: 0.128 s
% 0.22/0.54  % (1322)------------------------------
% 0.22/0.54  % (1322)------------------------------
% 0.22/0.54  % (1333)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (1328)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (1331)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (1304)Success in time 0.181 s
%------------------------------------------------------------------------------
