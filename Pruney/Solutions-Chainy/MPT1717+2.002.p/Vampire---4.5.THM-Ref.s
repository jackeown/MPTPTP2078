%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:01 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 164 expanded)
%              Number of leaves         :    5 (  29 expanded)
%              Depth                    :   21
%              Number of atoms          :  254 ( 813 expanded)
%              Number of equality atoms :   26 ( 106 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f66,plain,(
    $false ),
    inference(subsumption_resolution,[],[f65,f19])).

% (31406)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f19,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X0,X1,X1)
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X0,X1,X1)
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X1,X1) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tmap_1)).

fof(f65,plain,(
    v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f64,f17])).

fof(f17,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f64,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f63,f20])).

fof(f20,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f63,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f62,f21])).

fof(f21,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f62,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(sK1,X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f61,f46])).

fof(f46,plain,(
    m1_pre_topc(sK1,sK1) ),
    inference(subsumption_resolution,[],[f45,f34])).

fof(f34,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f32,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f45,plain,
    ( m1_pre_topc(sK1,sK1)
    | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK1)) ),
    inference(resolution,[],[f44,f17])).

fof(f44,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_pre_topc(X0,sK1)
      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f43,f17])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,sK0)
      | ~ m1_pre_topc(X0,sK0)
      | m1_pre_topc(X0,X1)
      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f42,f20])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ m1_pre_topc(X1,sK0)
      | m1_pre_topc(X0,X1)
      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ) ),
    inference(resolution,[],[f29,f21])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f61,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK1,X0)
      | ~ m1_pre_topc(sK1,sK1)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f60,f16])).

fof(f16,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X0)
      | ~ m1_pre_topc(sK1,sK1)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X0)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,X0)
      | ~ m1_pre_topc(sK1,sK1)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f56,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tsep_1(X2,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ~ r1_tsep_1(X2,X1)
                & ~ r1_tsep_1(X1,X2) )
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ~ r1_tsep_1(X2,X1)
                & ~ r1_tsep_1(X1,X2) )
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( m1_pre_topc(X1,X2)
               => ( ~ r1_tsep_1(X2,X1)
                  & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tmap_1)).

fof(f56,plain,(
    r1_tsep_1(sK1,sK1) ),
    inference(subsumption_resolution,[],[f55,f18])).

fof(f18,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k2_tsep_1(sK0,sK1,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f55,plain,
    ( r1_tsep_1(sK1,sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f54,f46])).

fof(f54,plain,
    ( r1_tsep_1(sK1,sK1)
    | ~ m1_pre_topc(sK1,sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f53,f16])).

fof(f53,plain,
    ( v2_struct_0(sK1)
    | r1_tsep_1(sK1,sK1)
    | ~ m1_pre_topc(sK1,sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,sK1,sK1) ),
    inference(resolution,[],[f52,f17])).

fof(f52,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | r1_tsep_1(X0,sK1)
      | ~ m1_pre_topc(sK1,X0)
      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,X0,sK1) ) ),
    inference(subsumption_resolution,[],[f51,f16])).

fof(f51,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK1)
      | v2_struct_0(X0)
      | r1_tsep_1(X0,sK1)
      | ~ m1_pre_topc(sK1,X0)
      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,X0,sK1) ) ),
    inference(resolution,[],[f50,f17])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | r1_tsep_1(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f49,f19])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,sK0)
      | r1_tsep_1(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f48,f20])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,sK0)
      | r1_tsep_1(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(sK0,X0,X1) ) ),
    inference(resolution,[],[f23,f21])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X1)
      | k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X2,X1)
                  | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                & ( k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  | ~ m1_pre_topc(X2,X1) )
                & ( m1_pre_topc(X1,X2)
                  | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                & ( k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ m1_pre_topc(X1,X2) ) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X2,X1)
                  | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                & ( k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  | ~ m1_pre_topc(X2,X1) )
                & ( m1_pre_topc(X1,X2)
                  | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                & ( k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ m1_pre_topc(X1,X2) ) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ( ( k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                   => m1_pre_topc(X2,X1) )
                  & ( m1_pre_topc(X2,X1)
                   => k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                  & ( k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                   => m1_pre_topc(X1,X2) )
                  & ( m1_pre_topc(X1,X2)
                   => k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tsep_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:38:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (31403)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (31425)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (31409)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (31409)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f65,f19])).
% 0.22/0.52  % (31406)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ~v2_struct_0(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X0,X1,X1) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f7])).
% 0.22/0.52  fof(f7,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X0,X1,X1) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,negated_conjecture,(
% 0.22/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X1,X1)))),
% 0.22/0.52    inference(negated_conjecture,[],[f5])).
% 0.22/0.52  fof(f5,conjecture,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X1,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tmap_1)).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    v2_struct_0(sK0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f64,f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    m1_pre_topc(sK1,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f63,f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    v2_pre_topc(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ~v2_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0)),
% 0.22/0.52    inference(resolution,[],[f62,f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    l1_pre_topc(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(sK1,X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f61,f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    m1_pre_topc(sK1,sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f45,f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.22/0.52    inference(resolution,[],[f32,f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    m1_pre_topc(sK1,sK1) | ~r1_tarski(u1_struct_0(sK1),u1_struct_0(sK1))),
% 0.22/0.52    inference(resolution,[],[f44,f17])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_pre_topc(X0,sK1) | ~r1_tarski(u1_struct_0(X0),u1_struct_0(sK1))) )),
% 0.22/0.52    inference(resolution,[],[f43,f17])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,sK0) | m1_pre_topc(X0,X1) | ~r1_tarski(u1_struct_0(X0),u1_struct_0(X1))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f42,f20])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v2_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X1,sK0) | m1_pre_topc(X0,X1) | ~r1_tarski(u1_struct_0(X0),u1_struct_0(X1))) )),
% 0.22/0.52    inference(resolution,[],[f29,f21])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.52    inference(flattening,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f60,f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ~v2_struct_0(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X0) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f57])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,X0) | ~m1_pre_topc(sK1,sK1) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(resolution,[],[f56,f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r1_tsep_1(X2,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X2) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : ((~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (((~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2)) | ~m1_pre_topc(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tmap_1)).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    r1_tsep_1(sK1,sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f55,f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != k2_tsep_1(sK0,sK1,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    r1_tsep_1(sK1,sK1) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,sK1,sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f54,f46])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    r1_tsep_1(sK1,sK1) | ~m1_pre_topc(sK1,sK1) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,sK1,sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f53,f16])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    v2_struct_0(sK1) | r1_tsep_1(sK1,sK1) | ~m1_pre_topc(sK1,sK1) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,sK1,sK1)),
% 0.22/0.52    inference(resolution,[],[f52,f17])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | r1_tsep_1(X0,sK1) | ~m1_pre_topc(sK1,X0) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,X0,sK1)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f51,f16])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_struct_0(sK1) | v2_struct_0(X0) | r1_tsep_1(X0,sK1) | ~m1_pre_topc(sK1,X0) | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,X0,sK1)) )),
% 0.22/0.52    inference(resolution,[],[f50,f17])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | v2_struct_0(X0) | r1_tsep_1(X0,X1) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(sK0,X0,X1)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f49,f19])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v2_struct_0(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | r1_tsep_1(X0,X1) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(sK0,X0,X1)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f48,f20])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | r1_tsep_1(X0,X1) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(sK0,X0,X1)) )),
% 0.22/0.52    inference(resolution,[],[f23,f21])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X1) | k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X2,X1) | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | ~m1_pre_topc(X2,X1)) & (m1_pre_topc(X1,X2) | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) & (k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X2))) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f9])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X2,X1) | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | ~m1_pre_topc(X2,X1)) & (m1_pre_topc(X1,X2) | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) & (k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X2))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ((k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => m1_pre_topc(X2,X1)) & (m1_pre_topc(X2,X1) => k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) => m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) => k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tsep_1)).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (31409)------------------------------
% 0.22/0.52  % (31409)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (31409)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (31409)Memory used [KB]: 6268
% 0.22/0.52  % (31409)Time elapsed: 0.111 s
% 0.22/0.52  % (31409)------------------------------
% 0.22/0.52  % (31409)------------------------------
% 0.22/0.52  % (31402)Success in time 0.161 s
%------------------------------------------------------------------------------
