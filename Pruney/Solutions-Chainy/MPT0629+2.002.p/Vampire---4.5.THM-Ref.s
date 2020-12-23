%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 (  93 expanded)
%              Number of leaves         :    9 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :  140 ( 369 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f51,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f45,f50])).

fof(f50,plain,(
    ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f49])).

fof(f49,plain,
    ( $false
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f48,f20])).

fof(f20,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    & r2_hidden(sK0,k2_relat_1(k5_relat_1(sK2,sK1)))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f17,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_hidden(X0,k2_relat_1(X1))
            & r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r2_hidden(sK0,k2_relat_1(sK1))
          & r2_hidden(sK0,k2_relat_1(k5_relat_1(X2,sK1)))
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( ~ r2_hidden(sK0,k2_relat_1(sK1))
        & r2_hidden(sK0,k2_relat_1(k5_relat_1(X2,sK1)))
        & v1_relat_1(X2) )
   => ( ~ r2_hidden(sK0,k2_relat_1(sK1))
      & r2_hidden(sK0,k2_relat_1(k5_relat_1(sK2,sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X0,k2_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X0,k2_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
             => r2_hidden(X0,k2_relat_1(X1)) ) ) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
             => r2_hidden(X0,k2_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))
           => r2_hidden(X0,k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_funct_1)).

fof(f48,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f47,f21])).

fof(f21,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f46,f23])).

fof(f23,plain,(
    ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f46,plain,
    ( r2_hidden(sK0,k2_relat_1(sK1))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f40,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v5_relat_1(k5_relat_1(X1,X0),k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f31,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | v5_relat_1(k5_relat_1(X1,X0),k2_relat_1(X0))
      | ~ v1_relat_1(k5_relat_1(X1,X0)) ) ),
    inference(resolution,[],[f24,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f40,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(k5_relat_1(sK2,sK1),X0)
        | r2_hidden(sK0,X0) )
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl3_2
  <=> ! [X0] :
        ( r2_hidden(sK0,X0)
        | ~ v5_relat_1(k5_relat_1(sK2,sK1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f45,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f44])).

fof(f44,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f43,f21])).

fof(f43,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f42,f20])).

fof(f42,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(resolution,[],[f37,f27])).

fof(f37,plain,
    ( ~ v1_relat_1(k5_relat_1(sK2,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl3_1
  <=> v1_relat_1(k5_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f41,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f33,f39,f35])).

fof(f33,plain,(
    ! [X0] :
      ( r2_hidden(sK0,X0)
      | ~ v5_relat_1(k5_relat_1(sK2,sK1),X0)
      | ~ v1_relat_1(k5_relat_1(sK2,sK1)) ) ),
    inference(resolution,[],[f28,f22])).

fof(f22,plain,(
    r2_hidden(sK0,k2_relat_1(k5_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_relat_1(X1))
      | r2_hidden(X2,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k2_relat_1(X1))
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:08:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (23124)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.20/0.46  % (23124)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f51,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f41,f45,f50])).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    ~spl3_2),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f49])).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    $false | ~spl3_2),
% 0.20/0.46    inference(subsumption_resolution,[],[f48,f20])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    v1_relat_1(sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    (~r2_hidden(sK0,k2_relat_1(sK1)) & r2_hidden(sK0,k2_relat_1(k5_relat_1(sK2,sK1))) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f17,f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ? [X0,X1] : (? [X2] : (~r2_hidden(X0,k2_relat_1(X1)) & r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1))) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r2_hidden(sK0,k2_relat_1(sK1)) & r2_hidden(sK0,k2_relat_1(k5_relat_1(X2,sK1))) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ? [X2] : (~r2_hidden(sK0,k2_relat_1(sK1)) & r2_hidden(sK0,k2_relat_1(k5_relat_1(X2,sK1))) & v1_relat_1(X2)) => (~r2_hidden(sK0,k2_relat_1(sK1)) & r2_hidden(sK0,k2_relat_1(k5_relat_1(sK2,sK1))) & v1_relat_1(sK2))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ? [X0,X1] : (? [X2] : (~r2_hidden(X0,k2_relat_1(X1)) & r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1))) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.20/0.46    inference(flattening,[],[f8])).
% 0.20/0.46  fof(f8,plain,(
% 0.20/0.46    ? [X0,X1] : (? [X2] : ((~r2_hidden(X0,k2_relat_1(X1)) & r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1)))) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,plain,(
% 0.20/0.46    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1))) => r2_hidden(X0,k2_relat_1(X1)))))),
% 0.20/0.46    inference(pure_predicate_removal,[],[f6])).
% 0.20/0.46  fof(f6,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1))) => r2_hidden(X0,k2_relat_1(X1)))))),
% 0.20/0.46    inference(negated_conjecture,[],[f5])).
% 0.20/0.46  fof(f5,conjecture,(
% 0.20/0.46    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k2_relat_1(k5_relat_1(X2,X1))) => r2_hidden(X0,k2_relat_1(X1)))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_funct_1)).
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    ~v1_relat_1(sK1) | ~spl3_2),
% 0.20/0.46    inference(subsumption_resolution,[],[f47,f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    v1_relat_1(sK2)),
% 0.20/0.46    inference(cnf_transformation,[],[f18])).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    ~v1_relat_1(sK2) | ~v1_relat_1(sK1) | ~spl3_2),
% 0.20/0.46    inference(subsumption_resolution,[],[f46,f23])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ~r2_hidden(sK0,k2_relat_1(sK1))),
% 0.20/0.46    inference(cnf_transformation,[],[f18])).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    r2_hidden(sK0,k2_relat_1(sK1)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK1) | ~spl3_2),
% 0.20/0.46    inference(resolution,[],[f40,f32])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ( ! [X0,X1] : (v5_relat_1(k5_relat_1(X1,X0),k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f31,f27])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.46    inference(flattening,[],[f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | v5_relat_1(k5_relat_1(X1,X0),k2_relat_1(X0)) | ~v1_relat_1(k5_relat_1(X1,X0))) )),
% 0.20/0.46    inference(resolution,[],[f24,f26])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(nnf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    ( ! [X0] : (~v5_relat_1(k5_relat_1(sK2,sK1),X0) | r2_hidden(sK0,X0)) ) | ~spl3_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f39])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    spl3_2 <=> ! [X0] : (r2_hidden(sK0,X0) | ~v5_relat_1(k5_relat_1(sK2,sK1),X0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    spl3_1),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f44])).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    $false | spl3_1),
% 0.20/0.46    inference(subsumption_resolution,[],[f43,f21])).
% 0.20/0.46  fof(f43,plain,(
% 0.20/0.46    ~v1_relat_1(sK2) | spl3_1),
% 0.20/0.46    inference(subsumption_resolution,[],[f42,f20])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    ~v1_relat_1(sK1) | ~v1_relat_1(sK2) | spl3_1),
% 0.20/0.46    inference(resolution,[],[f37,f27])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    ~v1_relat_1(k5_relat_1(sK2,sK1)) | spl3_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f35])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    spl3_1 <=> v1_relat_1(k5_relat_1(sK2,sK1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    ~spl3_1 | spl3_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f33,f39,f35])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    ( ! [X0] : (r2_hidden(sK0,X0) | ~v5_relat_1(k5_relat_1(sK2,sK1),X0) | ~v1_relat_1(k5_relat_1(sK2,sK1))) )),
% 0.20/0.46    inference(resolution,[],[f28,f22])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    r2_hidden(sK0,k2_relat_1(k5_relat_1(sK2,sK1)))),
% 0.20/0.46    inference(cnf_transformation,[],[f18])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_relat_1(X1)) | r2_hidden(X2,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(flattening,[],[f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1))) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.46    inference(ennf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k2_relat_1(X1)) => r2_hidden(X2,X0)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (23124)------------------------------
% 0.20/0.46  % (23124)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (23124)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (23124)Memory used [KB]: 5373
% 0.20/0.46  % (23124)Time elapsed: 0.047 s
% 0.20/0.46  % (23124)------------------------------
% 0.20/0.46  % (23124)------------------------------
% 0.20/0.46  % (23130)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.20/0.46  % (23115)Success in time 0.107 s
%------------------------------------------------------------------------------
