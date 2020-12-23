%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:58 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   62 (  82 expanded)
%              Number of leaves         :   16 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :  181 ( 243 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f77,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f55,f58,f70,f73,f76])).

fof(f76,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f74])).

fof(f74,plain,
    ( $false
    | spl2_5 ),
    inference(resolution,[],[f69,f25])).

fof(f25,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ v5_funct_1(k1_xboole_0,sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ~ v5_funct_1(k1_xboole_0,X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v5_funct_1(k1_xboole_0,sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => v5_funct_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v5_funct_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

fof(f69,plain,
    ( ~ v1_funct_1(sK0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl2_5
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f73,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f71])).

fof(f71,plain,
    ( $false
    | spl2_4 ),
    inference(resolution,[],[f65,f24])).

fof(f24,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f65,plain,
    ( ~ v1_relat_1(sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl2_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f70,plain,
    ( ~ spl2_4
    | ~ spl2_5
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f61,f50,f67,f63])).

fof(f50,plain,
    ( spl2_3
  <=> ! [X0] :
        ( r2_hidden(sK1(X0,k1_xboole_0),k1_xboole_0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | v5_funct_1(k1_xboole_0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f61,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f60,f26])).

fof(f26,plain,(
    ~ v5_funct_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f60,plain,
    ( ! [X0] :
        ( v5_funct_1(k1_xboole_0,X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_3 ),
    inference(resolution,[],[f59,f30])).

fof(f30,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f59,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(k1_enumset1(sK1(X0,k1_xboole_0),sK1(X0,k1_xboole_0),X1),k1_xboole_0)
        | ~ v1_funct_1(X0)
        | v5_funct_1(k1_xboole_0,X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_3 ),
    inference(resolution,[],[f51,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k1_enumset1(X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f37,f36])).

fof(f36,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f51,plain,
    ( ! [X0] :
        ( r2_hidden(sK1(X0,k1_xboole_0),k1_xboole_0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | v5_funct_1(k1_xboole_0,X0) )
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f58,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f57])).

fof(f57,plain,
    ( $false
    | spl2_2 ),
    inference(resolution,[],[f56,f27])).

fof(f27,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f56,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl2_2 ),
    inference(resolution,[],[f48,f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f48,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl2_2
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f55,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f54])).

fof(f54,plain,
    ( $false
    | spl2_1 ),
    inference(resolution,[],[f53,f27])).

fof(f53,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl2_1 ),
    inference(resolution,[],[f44,f32])).

fof(f32,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f44,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl2_1
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f52,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | spl2_3 ),
    inference(avatar_split_clause,[],[f40,f50,f46,f42])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,X0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f34,f28])).

fof(f28,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k1_relat_1(X1))
      | v5_funct_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ( ~ r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1)))
                & r2_hidden(sK1(X0,X1),k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
          & r2_hidden(X2,k1_relat_1(X1)) )
     => ( ~ r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1)))
        & r2_hidden(sK1(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X2] :
                  ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  | ~ r2_hidden(X2,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,k1_relat_1(X1))
               => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:16:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.43  % (22030)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.44  % (22030)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f77,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f52,f55,f58,f70,f73,f76])).
% 0.22/0.44  fof(f76,plain,(
% 0.22/0.44    spl2_5),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f74])).
% 0.22/0.44  fof(f74,plain,(
% 0.22/0.44    $false | spl2_5),
% 0.22/0.44    inference(resolution,[],[f69,f25])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    v1_funct_1(sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f19])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ~v5_funct_1(k1_xboole_0,sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f18])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (~v5_funct_1(k1_xboole_0,sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.44    inference(flattening,[],[f11])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,negated_conjecture,(
% 0.22/0.44    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 0.22/0.44    inference(negated_conjecture,[],[f9])).
% 0.22/0.44  fof(f9,conjecture,(
% 0.22/0.44    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).
% 0.22/0.44  fof(f69,plain,(
% 0.22/0.44    ~v1_funct_1(sK0) | spl2_5),
% 0.22/0.44    inference(avatar_component_clause,[],[f67])).
% 0.22/0.44  fof(f67,plain,(
% 0.22/0.44    spl2_5 <=> v1_funct_1(sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.44  fof(f73,plain,(
% 0.22/0.44    spl2_4),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f71])).
% 0.22/0.44  fof(f71,plain,(
% 0.22/0.44    $false | spl2_4),
% 0.22/0.44    inference(resolution,[],[f65,f24])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    v1_relat_1(sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f19])).
% 0.22/0.44  fof(f65,plain,(
% 0.22/0.44    ~v1_relat_1(sK0) | spl2_4),
% 0.22/0.44    inference(avatar_component_clause,[],[f63])).
% 0.22/0.44  fof(f63,plain,(
% 0.22/0.44    spl2_4 <=> v1_relat_1(sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.44  fof(f70,plain,(
% 0.22/0.44    ~spl2_4 | ~spl2_5 | ~spl2_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f61,f50,f67,f63])).
% 0.22/0.44  fof(f50,plain,(
% 0.22/0.44    spl2_3 <=> ! [X0] : (r2_hidden(sK1(X0,k1_xboole_0),k1_xboole_0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | v5_funct_1(k1_xboole_0,X0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.44  fof(f61,plain,(
% 0.22/0.44    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl2_3),
% 0.22/0.44    inference(resolution,[],[f60,f26])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    ~v5_funct_1(k1_xboole_0,sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f19])).
% 0.22/0.44  fof(f60,plain,(
% 0.22/0.44    ( ! [X0] : (v5_funct_1(k1_xboole_0,X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl2_3),
% 0.22/0.44    inference(resolution,[],[f59,f30])).
% 0.22/0.44  fof(f30,plain,(
% 0.22/0.44    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.44  fof(f59,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r1_xboole_0(k1_enumset1(sK1(X0,k1_xboole_0),sK1(X0,k1_xboole_0),X1),k1_xboole_0) | ~v1_funct_1(X0) | v5_funct_1(k1_xboole_0,X0) | ~v1_relat_1(X0)) ) | ~spl2_3),
% 0.22/0.44    inference(resolution,[],[f51,f38])).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k1_enumset1(X0,X0,X1),X2)) )),
% 0.22/0.44    inference(definition_unfolding,[],[f37,f36])).
% 0.22/0.44  fof(f36,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.44  fof(f37,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f17])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.22/0.44    inference(ennf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 0.22/0.44  fof(f51,plain,(
% 0.22/0.44    ( ! [X0] : (r2_hidden(sK1(X0,k1_xboole_0),k1_xboole_0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | v5_funct_1(k1_xboole_0,X0)) ) | ~spl2_3),
% 0.22/0.44    inference(avatar_component_clause,[],[f50])).
% 0.22/0.44  fof(f58,plain,(
% 0.22/0.44    spl2_2),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f57])).
% 0.22/0.44  fof(f57,plain,(
% 0.22/0.44    $false | spl2_2),
% 0.22/0.44    inference(resolution,[],[f56,f27])).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    v1_xboole_0(k1_xboole_0)),
% 0.22/0.44    inference(cnf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    v1_xboole_0(k1_xboole_0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.44  fof(f56,plain,(
% 0.22/0.44    ~v1_xboole_0(k1_xboole_0) | spl2_2),
% 0.22/0.44    inference(resolution,[],[f48,f31])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,axiom,(
% 0.22/0.44    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).
% 0.22/0.45  fof(f48,plain,(
% 0.22/0.45    ~v1_funct_1(k1_xboole_0) | spl2_2),
% 0.22/0.45    inference(avatar_component_clause,[],[f46])).
% 0.22/0.45  fof(f46,plain,(
% 0.22/0.45    spl2_2 <=> v1_funct_1(k1_xboole_0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.45  fof(f55,plain,(
% 0.22/0.45    spl2_1),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f54])).
% 0.22/0.45  fof(f54,plain,(
% 0.22/0.45    $false | spl2_1),
% 0.22/0.45    inference(resolution,[],[f53,f27])).
% 0.22/0.45  fof(f53,plain,(
% 0.22/0.45    ~v1_xboole_0(k1_xboole_0) | spl2_1),
% 0.22/0.45    inference(resolution,[],[f44,f32])).
% 0.22/0.45  fof(f32,plain,(
% 0.22/0.45    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f14])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f5])).
% 0.22/0.45  fof(f5,axiom,(
% 0.22/0.45    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.22/0.45  fof(f44,plain,(
% 0.22/0.45    ~v1_relat_1(k1_xboole_0) | spl2_1),
% 0.22/0.45    inference(avatar_component_clause,[],[f42])).
% 0.22/0.45  fof(f42,plain,(
% 0.22/0.45    spl2_1 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.45  fof(f52,plain,(
% 0.22/0.45    ~spl2_1 | ~spl2_2 | spl2_3),
% 0.22/0.45    inference(avatar_split_clause,[],[f40,f50,f46,f42])).
% 0.22/0.45  fof(f40,plain,(
% 0.22/0.45    ( ! [X0] : (r2_hidden(sK1(X0,k1_xboole_0),k1_xboole_0) | v5_funct_1(k1_xboole_0,X0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.45    inference(superposition,[],[f34,f28])).
% 0.22/0.45  fof(f28,plain,(
% 0.22/0.45    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.45    inference(cnf_transformation,[],[f6])).
% 0.22/0.45  fof(f6,axiom,(
% 0.22/0.45    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.45  fof(f34,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k1_relat_1(X1)) | v5_funct_1(X1,X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f23])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | (~r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1))) & r2_hidden(sK1(X0,X1),k1_relat_1(X1)))) & (! [X3] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    ! [X1,X0] : (? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1))) => (~r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1))) & r2_hidden(sK1(X0,X1),k1_relat_1(X1))))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | ? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1)))) & (! [X3] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(rectify,[],[f20])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | ? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1)))) & (! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(nnf_transformation,[],[f16])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(flattening,[],[f15])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f8])).
% 0.22/0.45  fof(f8,axiom,(
% 0.22/0.45    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (22030)------------------------------
% 0.22/0.45  % (22030)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (22030)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (22030)Memory used [KB]: 6140
% 0.22/0.45  % (22030)Time elapsed: 0.033 s
% 0.22/0.45  % (22030)------------------------------
% 0.22/0.45  % (22030)------------------------------
% 0.22/0.45  % (22024)Success in time 0.09 s
%------------------------------------------------------------------------------
