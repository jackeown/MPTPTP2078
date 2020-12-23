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
% DateTime   : Thu Dec  3 13:22:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 409 expanded)
%              Number of leaves         :    8 ( 145 expanded)
%              Depth                    :   15
%              Number of atoms          :  164 (1684 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f127,plain,(
    $false ),
    inference(global_subsumption,[],[f125,f120])).

fof(f120,plain,(
    r2_hidden(sK3(u1_orders_2(sK2),u1_orders_2(sK0)),u1_orders_2(sK0)) ),
    inference(unit_resulting_resolution,[],[f48,f115,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(u1_orders_2(sK1),X1)
      | r2_hidden(sK3(u1_orders_2(sK2),X0),X1)
      | r1_tarski(u1_orders_2(sK2),X0) ) ),
    inference(resolution,[],[f76,f28])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
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

fof(f76,plain,(
    ! [X3] :
      ( r2_hidden(sK3(u1_orders_2(sK2),X3),u1_orders_2(sK1))
      | r1_tarski(u1_orders_2(sK2),X3) ) ),
    inference(resolution,[],[f39,f53])).

fof(f53,plain,(
    r1_tarski(u1_orders_2(sK2),u1_orders_2(sK1)) ),
    inference(subsumption_resolution,[],[f51,f31])).

% (23665)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
fof(f31,plain,(
    l1_orders_2(sK1) ),
    inference(unit_resulting_resolution,[],[f20,f21,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_yellow_0(X1,X0)
      | l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_yellow_0)).

fof(f21,plain,(
    m1_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ m1_yellow_0(sK2,sK0)
    & m1_yellow_0(sK2,sK1)
    & m1_yellow_0(sK1,sK0)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f12,f11,f10])).

fof(f10,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ m1_yellow_0(X2,X0)
                & m1_yellow_0(X2,X1) )
            & m1_yellow_0(X1,X0) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_yellow_0(X2,sK0)
              & m1_yellow_0(X2,X1) )
          & m1_yellow_0(X1,sK0) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ m1_yellow_0(X2,sK0)
            & m1_yellow_0(X2,X1) )
        & m1_yellow_0(X1,sK0) )
   => ( ? [X2] :
          ( ~ m1_yellow_0(X2,sK0)
          & m1_yellow_0(X2,sK1) )
      & m1_yellow_0(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X2] :
        ( ~ m1_yellow_0(X2,sK0)
        & m1_yellow_0(X2,sK1) )
   => ( ~ m1_yellow_0(sK2,sK0)
      & m1_yellow_0(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_yellow_0(X2,X0)
              & m1_yellow_0(X2,X1) )
          & m1_yellow_0(X1,X0) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_yellow_0(X1,X0)
           => ! [X2] :
                ( m1_yellow_0(X2,X1)
               => m1_yellow_0(X2,X0) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ! [X2] :
              ( m1_yellow_0(X2,X1)
             => m1_yellow_0(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_yellow_6)).

fof(f20,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f51,plain,
    ( r1_tarski(u1_orders_2(sK2),u1_orders_2(sK1))
    | ~ l1_orders_2(sK1) ),
    inference(resolution,[],[f47,f22])).

fof(f22,plain,(
    m1_yellow_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_yellow_0(X1,X0)
      | r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f25,f27])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_yellow_0(X1,X0)
              | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
            & ( ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
                & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
              | ~ m1_yellow_0(X1,X0) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_yellow_0(X1,X0)
              | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
            & ( ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
                & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
              | ~ m1_yellow_0(X1,X0) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_yellow_0)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | r2_hidden(sK3(X0,X1),X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f28,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f115,plain,(
    ~ r1_tarski(u1_orders_2(sK2),u1_orders_2(sK0)) ),
    inference(unit_resulting_resolution,[],[f20,f35,f23,f113,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
      | m1_yellow_0(X1,X0)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f113,plain,(
    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f111])).

fof(f111,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK0))
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f109,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f109,plain,(
    ! [X0] :
      ( r2_hidden(sK3(u1_struct_0(sK2),X0),u1_struct_0(sK0))
      | r1_tarski(u1_struct_0(sK2),X0) ) ),
    inference(resolution,[],[f100,f41])).

fof(f41,plain,(
    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f20,f21,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_yellow_0(X1,X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f24,f27])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(u1_struct_0(sK1),X1)
      | r2_hidden(sK3(u1_struct_0(sK2),X0),X1)
      | r1_tarski(u1_struct_0(sK2),X0) ) ),
    inference(resolution,[],[f74,f28])).

fof(f74,plain,(
    ! [X1] :
      ( r2_hidden(sK3(u1_struct_0(sK2),X1),u1_struct_0(sK1))
      | r1_tarski(u1_struct_0(sK2),X1) ) ),
    inference(resolution,[],[f39,f46])).

fof(f46,plain,(
    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f44,f31])).

fof(f44,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1) ),
    inference(resolution,[],[f40,f22])).

fof(f23,plain,(
    ~ m1_yellow_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f35,plain,(
    l1_orders_2(sK2) ),
    inference(global_subsumption,[],[f34,f33])).

fof(f33,plain,
    ( l1_orders_2(sK2)
    | ~ l1_orders_2(sK1) ),
    inference(resolution,[],[f27,f22])).

fof(f34,plain,(
    l1_orders_2(sK1) ),
    inference(subsumption_resolution,[],[f32,f20])).

fof(f32,plain,
    ( l1_orders_2(sK1)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f27,f21])).

fof(f48,plain,(
    r1_tarski(u1_orders_2(sK1),u1_orders_2(sK0)) ),
    inference(unit_resulting_resolution,[],[f20,f21,f47])).

fof(f125,plain,(
    ~ r2_hidden(sK3(u1_orders_2(sK2),u1_orders_2(sK0)),u1_orders_2(sK0)) ),
    inference(unit_resulting_resolution,[],[f115,f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:04:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.44  % (23656)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.20/0.44  % (23656)Refutation not found, incomplete strategy% (23656)------------------------------
% 0.20/0.44  % (23656)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (23656)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.44  
% 0.20/0.44  % (23656)Memory used [KB]: 895
% 0.20/0.44  % (23656)Time elapsed: 0.058 s
% 0.20/0.44  % (23656)------------------------------
% 0.20/0.44  % (23656)------------------------------
% 0.20/0.44  % (23671)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.20/0.44  % (23664)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.20/0.44  % (23671)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f127,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(global_subsumption,[],[f125,f120])).
% 0.20/0.44  fof(f120,plain,(
% 0.20/0.44    r2_hidden(sK3(u1_orders_2(sK2),u1_orders_2(sK0)),u1_orders_2(sK0))),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f48,f115,f106])).
% 0.20/0.44  fof(f106,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r1_tarski(u1_orders_2(sK1),X1) | r2_hidden(sK3(u1_orders_2(sK2),X0),X1) | r1_tarski(u1_orders_2(sK2),X0)) )),
% 0.20/0.44    inference(resolution,[],[f76,f28])).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f19])).
% 0.20/0.44  fof(f19,plain,(
% 0.20/0.44    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).
% 0.20/0.44  fof(f18,plain,(
% 0.20/0.44    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f17,plain,(
% 0.20/0.44    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.44    inference(rectify,[],[f16])).
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.44    inference(nnf_transformation,[],[f9])).
% 0.20/0.44  fof(f9,plain,(
% 0.20/0.44    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.45  fof(f76,plain,(
% 0.20/0.45    ( ! [X3] : (r2_hidden(sK3(u1_orders_2(sK2),X3),u1_orders_2(sK1)) | r1_tarski(u1_orders_2(sK2),X3)) )),
% 0.20/0.45    inference(resolution,[],[f39,f53])).
% 0.20/0.45  fof(f53,plain,(
% 0.20/0.45    r1_tarski(u1_orders_2(sK2),u1_orders_2(sK1))),
% 0.20/0.45    inference(subsumption_resolution,[],[f51,f31])).
% 0.20/0.45  % (23665)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    l1_orders_2(sK1)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f20,f21,f27])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~m1_yellow_0(X1,X0) | l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f8])).
% 0.20/0.45  fof(f8,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~m1_yellow_0(X1,X0)) | ~l1_orders_2(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_yellow_0(X1,X0) => l1_orders_2(X1)))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_yellow_0)).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    m1_yellow_0(sK1,sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f13])).
% 0.20/0.45  fof(f13,plain,(
% 0.20/0.45    ((~m1_yellow_0(sK2,sK0) & m1_yellow_0(sK2,sK1)) & m1_yellow_0(sK1,sK0)) & l1_orders_2(sK0)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f12,f11,f10])).
% 0.20/0.45  fof(f10,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (? [X2] : (~m1_yellow_0(X2,X0) & m1_yellow_0(X2,X1)) & m1_yellow_0(X1,X0)) & l1_orders_2(X0)) => (? [X1] : (? [X2] : (~m1_yellow_0(X2,sK0) & m1_yellow_0(X2,X1)) & m1_yellow_0(X1,sK0)) & l1_orders_2(sK0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f11,plain,(
% 0.20/0.45    ? [X1] : (? [X2] : (~m1_yellow_0(X2,sK0) & m1_yellow_0(X2,X1)) & m1_yellow_0(X1,sK0)) => (? [X2] : (~m1_yellow_0(X2,sK0) & m1_yellow_0(X2,sK1)) & m1_yellow_0(sK1,sK0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f12,plain,(
% 0.20/0.45    ? [X2] : (~m1_yellow_0(X2,sK0) & m1_yellow_0(X2,sK1)) => (~m1_yellow_0(sK2,sK0) & m1_yellow_0(sK2,sK1))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f6,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (? [X2] : (~m1_yellow_0(X2,X0) & m1_yellow_0(X2,X1)) & m1_yellow_0(X1,X0)) & l1_orders_2(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f5])).
% 0.20/0.45  fof(f5,negated_conjecture,(
% 0.20/0.45    ~! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_yellow_0(X1,X0) => ! [X2] : (m1_yellow_0(X2,X1) => m1_yellow_0(X2,X0))))),
% 0.20/0.45    inference(negated_conjecture,[],[f4])).
% 0.20/0.45  fof(f4,conjecture,(
% 0.20/0.45    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_yellow_0(X1,X0) => ! [X2] : (m1_yellow_0(X2,X1) => m1_yellow_0(X2,X0))))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_yellow_6)).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    l1_orders_2(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f13])).
% 0.20/0.45  fof(f51,plain,(
% 0.20/0.45    r1_tarski(u1_orders_2(sK2),u1_orders_2(sK1)) | ~l1_orders_2(sK1)),
% 0.20/0.45    inference(resolution,[],[f47,f22])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    m1_yellow_0(sK2,sK1)),
% 0.20/0.45    inference(cnf_transformation,[],[f13])).
% 0.20/0.45  fof(f47,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~m1_yellow_0(X1,X0) | r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f25,f27])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f15])).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (((m1_yellow_0(X1,X0) | ~r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) & ((r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) | ~m1_yellow_0(X1,X0))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 0.20/0.45    inference(flattening,[],[f14])).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (((m1_yellow_0(X1,X0) | (~r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)))) & ((r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) | ~m1_yellow_0(X1,X0))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 0.20/0.45    inference(nnf_transformation,[],[f7])).
% 0.20/0.45  fof(f7,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : ((m1_yellow_0(X1,X0) <=> (r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => (m1_yellow_0(X1,X0) <=> (r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) & r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_yellow_0)).
% 0.20/0.45  fof(f39,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | r2_hidden(sK3(X0,X1),X2) | r1_tarski(X0,X1)) )),
% 0.20/0.45    inference(resolution,[],[f28,f29])).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f19])).
% 0.20/0.45  fof(f115,plain,(
% 0.20/0.45    ~r1_tarski(u1_orders_2(sK2),u1_orders_2(sK0))),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f20,f35,f23,f113,f26])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | m1_yellow_0(X1,X0) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f15])).
% 0.20/0.45  fof(f113,plain,(
% 0.20/0.45    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK0))),
% 0.20/0.45    inference(duplicate_literal_removal,[],[f111])).
% 0.20/0.45  fof(f111,plain,(
% 0.20/0.45    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK0)) | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK0))),
% 0.20/0.45    inference(resolution,[],[f109,f30])).
% 0.20/0.45  fof(f30,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f19])).
% 0.20/0.45  fof(f109,plain,(
% 0.20/0.45    ( ! [X0] : (r2_hidden(sK3(u1_struct_0(sK2),X0),u1_struct_0(sK0)) | r1_tarski(u1_struct_0(sK2),X0)) )),
% 0.20/0.45    inference(resolution,[],[f100,f41])).
% 0.20/0.45  fof(f41,plain,(
% 0.20/0.45    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f20,f21,f40])).
% 0.20/0.45  fof(f40,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~m1_yellow_0(X1,X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f24,f27])).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f15])).
% 0.20/0.45  fof(f100,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r1_tarski(u1_struct_0(sK1),X1) | r2_hidden(sK3(u1_struct_0(sK2),X0),X1) | r1_tarski(u1_struct_0(sK2),X0)) )),
% 0.20/0.45    inference(resolution,[],[f74,f28])).
% 0.20/0.45  fof(f74,plain,(
% 0.20/0.45    ( ! [X1] : (r2_hidden(sK3(u1_struct_0(sK2),X1),u1_struct_0(sK1)) | r1_tarski(u1_struct_0(sK2),X1)) )),
% 0.20/0.45    inference(resolution,[],[f39,f46])).
% 0.20/0.45  fof(f46,plain,(
% 0.20/0.45    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.20/0.45    inference(subsumption_resolution,[],[f44,f31])).
% 0.20/0.45  fof(f44,plain,(
% 0.20/0.45    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) | ~l1_orders_2(sK1)),
% 0.20/0.45    inference(resolution,[],[f40,f22])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    ~m1_yellow_0(sK2,sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f13])).
% 0.20/0.45  fof(f35,plain,(
% 0.20/0.45    l1_orders_2(sK2)),
% 0.20/0.45    inference(global_subsumption,[],[f34,f33])).
% 0.20/0.45  fof(f33,plain,(
% 0.20/0.45    l1_orders_2(sK2) | ~l1_orders_2(sK1)),
% 0.20/0.45    inference(resolution,[],[f27,f22])).
% 0.20/0.45  fof(f34,plain,(
% 0.20/0.45    l1_orders_2(sK1)),
% 0.20/0.45    inference(subsumption_resolution,[],[f32,f20])).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    l1_orders_2(sK1) | ~l1_orders_2(sK0)),
% 0.20/0.45    inference(resolution,[],[f27,f21])).
% 0.20/0.45  fof(f48,plain,(
% 0.20/0.45    r1_tarski(u1_orders_2(sK1),u1_orders_2(sK0))),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f20,f21,f47])).
% 0.20/0.45  fof(f125,plain,(
% 0.20/0.45    ~r2_hidden(sK3(u1_orders_2(sK2),u1_orders_2(sK0)),u1_orders_2(sK0))),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f115,f30])).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (23671)------------------------------
% 0.20/0.45  % (23671)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (23671)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (23671)Memory used [KB]: 5500
% 0.20/0.45  % (23671)Time elapsed: 0.007 s
% 0.20/0.45  % (23671)------------------------------
% 0.20/0.45  % (23671)------------------------------
% 0.20/0.45  % (23665)Refutation not found, incomplete strategy% (23665)------------------------------
% 0.20/0.45  % (23665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (23665)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.45  
% 0.20/0.45  % (23665)Memory used [KB]: 5373
% 0.20/0.45  % (23665)Time elapsed: 0.060 s
% 0.20/0.45  % (23665)------------------------------
% 0.20/0.45  % (23665)------------------------------
% 0.20/0.45  % (23650)Success in time 0.092 s
%------------------------------------------------------------------------------
