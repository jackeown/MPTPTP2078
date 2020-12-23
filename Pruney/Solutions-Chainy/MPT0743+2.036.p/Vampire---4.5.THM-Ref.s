%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   85 (1545 expanded)
%              Number of leaves         :   10 ( 411 expanded)
%              Depth                    :   39
%              Number of atoms          :  264 (7550 expanded)
%              Number of equality atoms :   25 ( 113 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f482,plain,(
    $false ),
    inference(resolution,[],[f478,f60])).

fof(f60,plain,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f478,plain,(
    ~ r2_hidden(sK0,k1_ordinal1(sK0)) ),
    inference(resolution,[],[f476,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f476,plain,(
    r1_tarski(k1_ordinal1(sK0),sK0) ),
    inference(resolution,[],[f475,f42])).

fof(f42,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
      | ~ r2_hidden(sK0,sK1) )
    & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
      | r2_hidden(sK0,sK1) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | r2_hidden(X0,X1) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(sK0),X1)
            | ~ r2_hidden(sK0,X1) )
          & ( r1_ordinal1(k1_ordinal1(sK0),X1)
            | r2_hidden(sK0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( ( ~ r1_ordinal1(k1_ordinal1(sK0),X1)
          | ~ r2_hidden(sK0,X1) )
        & ( r1_ordinal1(k1_ordinal1(sK0),X1)
          | r2_hidden(sK0,X1) )
        & v3_ordinal1(X1) )
   => ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
        | ~ r2_hidden(sK0,sK1) )
      & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
        | r2_hidden(sK0,sK1) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f475,plain,
    ( ~ v3_ordinal1(sK0)
    | r1_tarski(k1_ordinal1(sK0),sK0) ),
    inference(resolution,[],[f474,f76])).

fof(f76,plain,(
    ! [X2] :
      ( ~ r1_ordinal1(k1_ordinal1(sK0),X2)
      | ~ v3_ordinal1(X2)
      | r1_tarski(k1_ordinal1(sK0),X2) ) ),
    inference(resolution,[],[f63,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f63,plain,(
    v3_ordinal1(k1_ordinal1(sK0)) ),
    inference(resolution,[],[f42,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v3_ordinal1(k1_ordinal1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f474,plain,(
    r1_ordinal1(k1_ordinal1(sK0),sK0) ),
    inference(resolution,[],[f439,f429])).

fof(f429,plain,(
    ~ r2_hidden(sK0,sK0) ),
    inference(backward_demodulation,[],[f291,f372])).

fof(f372,plain,(
    sK0 = sK1 ),
    inference(duplicate_literal_removal,[],[f366])).

fof(f366,plain,
    ( sK0 = sK1
    | sK0 = sK1 ),
    inference(resolution,[],[f365,f290])).

fof(f290,plain,
    ( ~ r1_tarski(sK1,sK0)
    | sK0 = sK1 ),
    inference(resolution,[],[f288,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f288,plain,(
    r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f287,f43])).

fof(f43,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f287,plain,
    ( ~ v3_ordinal1(sK1)
    | r1_tarski(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f286])).

fof(f286,plain,
    ( ~ v3_ordinal1(sK1)
    | r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f284,f66])).

fof(f66,plain,(
    ! [X2] :
      ( ~ r1_ordinal1(sK0,X2)
      | ~ v3_ordinal1(X2)
      | r1_tarski(sK0,X2) ) ),
    inference(resolution,[],[f42,f46])).

fof(f284,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f283,f64])).

fof(f64,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK0)
      | ~ v3_ordinal1(X0)
      | r1_ordinal1(sK0,X0) ) ),
    inference(resolution,[],[f42,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f283,plain,
    ( ~ r2_hidden(sK1,sK0)
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f280,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f280,plain,
    ( ~ r2_hidden(sK1,k1_ordinal1(sK0))
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f275,f56])).

fof(f275,plain,
    ( r1_tarski(k1_ordinal1(sK0),sK1)
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f267,f43])).

fof(f267,plain,
    ( ~ v3_ordinal1(sK1)
    | r1_tarski(sK0,sK1)
    | r1_tarski(k1_ordinal1(sK0),sK1) ),
    inference(resolution,[],[f264,f76])).

fof(f264,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f245,f44])).

fof(f44,plain,
    ( r2_hidden(sK0,sK1)
    | r1_ordinal1(k1_ordinal1(sK0),sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f245,plain,
    ( ~ r2_hidden(sK0,sK1)
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f243,f56])).

fof(f243,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f242,f42])).

fof(f242,plain,
    ( ~ v3_ordinal1(sK0)
    | r1_tarski(sK1,sK0)
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f159,f43])).

fof(f159,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | r1_tarski(sK1,sK0)
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f152,f66])).

fof(f152,plain,
    ( r1_ordinal1(sK0,sK1)
    | r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f71,f124])).

fof(f124,plain,
    ( r1_ordinal1(sK1,sK0)
    | r1_ordinal1(sK0,sK1) ),
    inference(resolution,[],[f65,f43])).

fof(f65,plain,(
    ! [X1] :
      ( ~ v3_ordinal1(X1)
      | r1_ordinal1(sK0,X1)
      | r1_ordinal1(X1,sK0) ) ),
    inference(resolution,[],[f42,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | r1_ordinal1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f71,plain,(
    ! [X2] :
      ( ~ r1_ordinal1(sK1,X2)
      | ~ v3_ordinal1(X2)
      | r1_tarski(sK1,X2) ) ),
    inference(resolution,[],[f43,f46])).

fof(f365,plain,
    ( r1_tarski(sK1,sK0)
    | sK0 = sK1 ),
    inference(resolution,[],[f364,f42])).

fof(f364,plain,
    ( ~ v3_ordinal1(sK0)
    | sK0 = sK1
    | r1_tarski(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f363])).

fof(f363,plain,
    ( ~ v3_ordinal1(sK0)
    | sK0 = sK1
    | ~ v3_ordinal1(sK0)
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f361,f71])).

fof(f361,plain,
    ( r1_ordinal1(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | sK0 = sK1 ),
    inference(resolution,[],[f358,f69])).

fof(f69,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ v3_ordinal1(X0)
      | r1_ordinal1(sK1,X0) ) ),
    inference(resolution,[],[f43,f49])).

fof(f358,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f357,f45])).

fof(f45,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f357,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f355,f43])).

fof(f355,plain,
    ( ~ v3_ordinal1(sK1)
    | r1_ordinal1(k1_ordinal1(sK0),sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f174,f291])).

fof(f174,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK0)
      | r1_ordinal1(k1_ordinal1(sK0),X0)
      | ~ v3_ordinal1(X0)
      | sK0 = X0 ) ),
    inference(resolution,[],[f74,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_ordinal1(X1))
      | r2_hidden(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f74,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_ordinal1(sK0))
      | ~ v3_ordinal1(X0)
      | r1_ordinal1(k1_ordinal1(sK0),X0) ) ),
    inference(resolution,[],[f63,f49])).

fof(f291,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f288,f56])).

fof(f439,plain,
    ( r2_hidden(sK0,sK0)
    | r1_ordinal1(k1_ordinal1(sK0),sK0) ),
    inference(forward_demodulation,[],[f375,f372])).

fof(f375,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK0)
    | r2_hidden(sK0,sK1) ),
    inference(backward_demodulation,[],[f44,f372])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:57:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (32362)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.50  % (32371)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.50  % (32368)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.51  % (32375)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.51  % (32361)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (32364)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (32383)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (32370)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (32360)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (32361)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f482,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(resolution,[],[f478,f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X1] : (r2_hidden(X1,k1_ordinal1(X1))) )),
% 0.21/0.54    inference(equality_resolution,[],[f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.21/0.54    inference(flattening,[],[f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.21/0.54    inference(nnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,axiom,(
% 0.21/0.54    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).
% 0.21/0.54  fof(f478,plain,(
% 0.21/0.54    ~r2_hidden(sK0,k1_ordinal1(sK0))),
% 0.21/0.54    inference(resolution,[],[f476,f56])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,axiom,(
% 0.21/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.54  fof(f476,plain,(
% 0.21/0.54    r1_tarski(k1_ordinal1(sK0),sK0)),
% 0.21/0.54    inference(resolution,[],[f475,f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    v3_ordinal1(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f35,f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) => ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.54    inference(flattening,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,negated_conjecture,(
% 0.21/0.54    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.21/0.54    inference(negated_conjecture,[],[f19])).
% 0.21/0.54  fof(f19,conjecture,(
% 0.21/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).
% 0.21/0.54  fof(f475,plain,(
% 0.21/0.54    ~v3_ordinal1(sK0) | r1_tarski(k1_ordinal1(sK0),sK0)),
% 0.21/0.54    inference(resolution,[],[f474,f76])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    ( ! [X2] : (~r1_ordinal1(k1_ordinal1(sK0),X2) | ~v3_ordinal1(X2) | r1_tarski(k1_ordinal1(sK0),X2)) )),
% 0.21/0.54    inference(resolution,[],[f63,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.54    inference(flattening,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    v3_ordinal1(k1_ordinal1(sK0))),
% 0.21/0.54    inference(resolution,[],[f42,f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X0] : (~v3_ordinal1(X0) | v3_ordinal1(k1_ordinal1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,axiom,(
% 0.21/0.54    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).
% 0.21/0.54  fof(f474,plain,(
% 0.21/0.54    r1_ordinal1(k1_ordinal1(sK0),sK0)),
% 0.21/0.54    inference(resolution,[],[f439,f429])).
% 0.21/0.54  fof(f429,plain,(
% 0.21/0.54    ~r2_hidden(sK0,sK0)),
% 0.21/0.54    inference(backward_demodulation,[],[f291,f372])).
% 0.21/0.54  fof(f372,plain,(
% 0.21/0.54    sK0 = sK1),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f366])).
% 0.21/0.54  fof(f366,plain,(
% 0.21/0.54    sK0 = sK1 | sK0 = sK1),
% 0.21/0.54    inference(resolution,[],[f365,f290])).
% 0.21/0.54  fof(f290,plain,(
% 0.21/0.54    ~r1_tarski(sK1,sK0) | sK0 = sK1),
% 0.21/0.54    inference(resolution,[],[f288,f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(flattening,[],[f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.54  fof(f288,plain,(
% 0.21/0.54    r1_tarski(sK0,sK1)),
% 0.21/0.54    inference(resolution,[],[f287,f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    v3_ordinal1(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f36])).
% 0.21/0.54  fof(f287,plain,(
% 0.21/0.54    ~v3_ordinal1(sK1) | r1_tarski(sK0,sK1)),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f286])).
% 0.21/0.54  fof(f286,plain,(
% 0.21/0.54    ~v3_ordinal1(sK1) | r1_tarski(sK0,sK1) | ~v3_ordinal1(sK1) | r1_tarski(sK0,sK1)),
% 0.21/0.54    inference(resolution,[],[f284,f66])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    ( ! [X2] : (~r1_ordinal1(sK0,X2) | ~v3_ordinal1(X2) | r1_tarski(sK0,X2)) )),
% 0.21/0.54    inference(resolution,[],[f42,f46])).
% 0.21/0.54  fof(f284,plain,(
% 0.21/0.54    r1_ordinal1(sK0,sK1) | ~v3_ordinal1(sK1) | r1_tarski(sK0,sK1)),
% 0.21/0.54    inference(resolution,[],[f283,f64])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(X0,sK0) | ~v3_ordinal1(X0) | r1_ordinal1(sK0,X0)) )),
% 0.21/0.54    inference(resolution,[],[f42,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v3_ordinal1(X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | r2_hidden(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.54    inference(flattening,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,axiom,(
% 0.21/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.21/0.54  fof(f283,plain,(
% 0.21/0.54    ~r2_hidden(sK1,sK0) | r1_tarski(sK0,sK1)),
% 0.21/0.54    inference(resolution,[],[f280,f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f280,plain,(
% 0.21/0.54    ~r2_hidden(sK1,k1_ordinal1(sK0)) | r1_tarski(sK0,sK1)),
% 0.21/0.54    inference(resolution,[],[f275,f56])).
% 0.21/0.54  fof(f275,plain,(
% 0.21/0.54    r1_tarski(k1_ordinal1(sK0),sK1) | r1_tarski(sK0,sK1)),
% 0.21/0.54    inference(resolution,[],[f267,f43])).
% 0.21/0.54  fof(f267,plain,(
% 0.21/0.54    ~v3_ordinal1(sK1) | r1_tarski(sK0,sK1) | r1_tarski(k1_ordinal1(sK0),sK1)),
% 0.21/0.54    inference(resolution,[],[f264,f76])).
% 0.21/0.54  fof(f264,plain,(
% 0.21/0.54    r1_ordinal1(k1_ordinal1(sK0),sK1) | r1_tarski(sK0,sK1)),
% 0.21/0.54    inference(resolution,[],[f245,f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    r2_hidden(sK0,sK1) | r1_ordinal1(k1_ordinal1(sK0),sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f36])).
% 0.21/0.54  fof(f245,plain,(
% 0.21/0.54    ~r2_hidden(sK0,sK1) | r1_tarski(sK0,sK1)),
% 0.21/0.54    inference(resolution,[],[f243,f56])).
% 0.21/0.54  fof(f243,plain,(
% 0.21/0.54    r1_tarski(sK1,sK0) | r1_tarski(sK0,sK1)),
% 0.21/0.54    inference(resolution,[],[f242,f42])).
% 0.21/0.54  fof(f242,plain,(
% 0.21/0.54    ~v3_ordinal1(sK0) | r1_tarski(sK1,sK0) | r1_tarski(sK0,sK1)),
% 0.21/0.54    inference(resolution,[],[f159,f43])).
% 0.21/0.54  fof(f159,plain,(
% 0.21/0.54    ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | r1_tarski(sK1,sK0) | r1_tarski(sK0,sK1)),
% 0.21/0.54    inference(resolution,[],[f152,f66])).
% 0.21/0.54  fof(f152,plain,(
% 0.21/0.54    r1_ordinal1(sK0,sK1) | r1_tarski(sK1,sK0) | ~v3_ordinal1(sK0)),
% 0.21/0.54    inference(resolution,[],[f71,f124])).
% 0.21/0.54  fof(f124,plain,(
% 0.21/0.54    r1_ordinal1(sK1,sK0) | r1_ordinal1(sK0,sK1)),
% 0.21/0.54    inference(resolution,[],[f65,f43])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X1] : (~v3_ordinal1(X1) | r1_ordinal1(sK0,X1) | r1_ordinal1(X1,sK0)) )),
% 0.21/0.54    inference(resolution,[],[f42,f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v3_ordinal1(X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | r1_ordinal1(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.54    inference(flattening,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ( ! [X2] : (~r1_ordinal1(sK1,X2) | ~v3_ordinal1(X2) | r1_tarski(sK1,X2)) )),
% 0.21/0.54    inference(resolution,[],[f43,f46])).
% 0.21/0.54  fof(f365,plain,(
% 0.21/0.54    r1_tarski(sK1,sK0) | sK0 = sK1),
% 0.21/0.54    inference(resolution,[],[f364,f42])).
% 0.21/0.54  fof(f364,plain,(
% 0.21/0.54    ~v3_ordinal1(sK0) | sK0 = sK1 | r1_tarski(sK1,sK0)),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f363])).
% 0.21/0.54  fof(f363,plain,(
% 0.21/0.54    ~v3_ordinal1(sK0) | sK0 = sK1 | ~v3_ordinal1(sK0) | r1_tarski(sK1,sK0)),
% 0.21/0.54    inference(resolution,[],[f361,f71])).
% 0.21/0.54  fof(f361,plain,(
% 0.21/0.54    r1_ordinal1(sK1,sK0) | ~v3_ordinal1(sK0) | sK0 = sK1),
% 0.21/0.54    inference(resolution,[],[f358,f69])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(X0,sK1) | ~v3_ordinal1(X0) | r1_ordinal1(sK1,X0)) )),
% 0.21/0.54    inference(resolution,[],[f43,f49])).
% 0.21/0.54  fof(f358,plain,(
% 0.21/0.54    ~r2_hidden(sK0,sK1) | sK0 = sK1),
% 0.21/0.54    inference(resolution,[],[f357,f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f36])).
% 0.21/0.54  fof(f357,plain,(
% 0.21/0.54    r1_ordinal1(k1_ordinal1(sK0),sK1) | sK0 = sK1),
% 0.21/0.54    inference(resolution,[],[f355,f43])).
% 0.21/0.54  fof(f355,plain,(
% 0.21/0.54    ~v3_ordinal1(sK1) | r1_ordinal1(k1_ordinal1(sK0),sK1) | sK0 = sK1),
% 0.21/0.54    inference(resolution,[],[f174,f291])).
% 0.21/0.54  fof(f174,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(X0,sK0) | r1_ordinal1(k1_ordinal1(sK0),X0) | ~v3_ordinal1(X0) | sK0 = X0) )),
% 0.21/0.54    inference(resolution,[],[f74,f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k1_ordinal1(X1)) | r2_hidden(X0,X1) | X0 = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(sK0)) | ~v3_ordinal1(X0) | r1_ordinal1(k1_ordinal1(sK0),X0)) )),
% 0.21/0.54    inference(resolution,[],[f63,f49])).
% 0.21/0.54  fof(f291,plain,(
% 0.21/0.54    ~r2_hidden(sK1,sK0)),
% 0.21/0.54    inference(resolution,[],[f288,f56])).
% 0.21/0.54  fof(f439,plain,(
% 0.21/0.54    r2_hidden(sK0,sK0) | r1_ordinal1(k1_ordinal1(sK0),sK0)),
% 0.21/0.54    inference(forward_demodulation,[],[f375,f372])).
% 0.21/0.54  fof(f375,plain,(
% 0.21/0.54    r1_ordinal1(k1_ordinal1(sK0),sK0) | r2_hidden(sK0,sK1)),
% 0.21/0.54    inference(backward_demodulation,[],[f44,f372])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (32361)------------------------------
% 0.21/0.54  % (32361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (32361)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (32361)Memory used [KB]: 1918
% 0.21/0.54  % (32361)Time elapsed: 0.127 s
% 0.21/0.54  % (32361)------------------------------
% 0.21/0.54  % (32361)------------------------------
% 0.21/0.54  % (32359)Success in time 0.179 s
%------------------------------------------------------------------------------
