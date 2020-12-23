%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1591+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :  191 (1148 expanded)
%              Number of leaves         :   26 ( 541 expanded)
%              Depth                    :   57
%              Number of atoms          : 1166 (14053 expanded)
%              Number of equality atoms :  126 (3698 expanded)
%              Maximal formula depth    :   17 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f238,plain,(
    $false ),
    inference(subsumption_resolution,[],[f237,f69])).

fof(f69,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,
    ( k12_lattice3(sK1,sK2,sK3) != k12_lattice3(sK0,sK4,sK5)
    & sK3 = sK5
    & sK2 = sK4
    & m1_subset_1(sK5,u1_struct_0(sK0))
    & m1_subset_1(sK4,u1_struct_0(sK0))
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & m1_yellow_0(sK1,sK0)
    & v5_yellow_0(sK1,sK0)
    & v4_yellow_0(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_orders_2(sK0)
    & v2_lattice3(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f19,f53,f52,f51,f50,f49,f48])).

% (15897)Refutation not found, incomplete strategy% (15897)------------------------------
% (15897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15897)Termination reason: Refutation not found, incomplete strategy

% (15897)Memory used [KB]: 10618
% (15897)Time elapsed: 0.124 s
% (15897)------------------------------
% (15897)------------------------------
fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( k12_lattice3(X1,X2,X3) != k12_lattice3(X0,X4,X5)
                            & X3 = X5
                            & X2 = X4
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                & m1_subset_1(X2,u1_struct_0(X1)) )
            & m1_yellow_0(X1,X0)
            & v5_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k12_lattice3(X1,X2,X3) != k12_lattice3(sK0,X4,X5)
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(sK0)) )
                      & m1_subset_1(X4,u1_struct_0(sK0)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_yellow_0(X1,sK0)
          & v5_yellow_0(X1,sK0)
          & v4_yellow_0(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK0)
      & v2_lattice3(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

% (15896)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% (15902)Refutation not found, incomplete strategy% (15902)------------------------------
% (15902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15902)Termination reason: Refutation not found, incomplete strategy

% (15902)Memory used [KB]: 10874
% (15902)Time elapsed: 0.118 s
% (15902)------------------------------
% (15902)------------------------------
% (15912)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% (15910)Refutation not found, incomplete strategy% (15910)------------------------------
% (15910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15910)Termination reason: Refutation not found, incomplete strategy

% (15910)Memory used [KB]: 1791
% (15910)Time elapsed: 0.113 s
% (15910)------------------------------
% (15910)------------------------------
% (15901)Refutation not found, incomplete strategy% (15901)------------------------------
% (15901)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15901)Termination reason: Refutation not found, incomplete strategy

% (15901)Memory used [KB]: 6396
% (15901)Time elapsed: 0.117 s
% (15901)------------------------------
% (15901)------------------------------
% (15904)Refutation not found, incomplete strategy% (15904)------------------------------
% (15904)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15904)Termination reason: Refutation not found, incomplete strategy

% (15904)Memory used [KB]: 10874
% (15904)Time elapsed: 0.140 s
% (15904)------------------------------
% (15904)------------------------------
% (15903)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% (15916)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
fof(f49,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( k12_lattice3(X1,X2,X3) != k12_lattice3(sK0,X4,X5)
                        & X3 = X5
                        & X2 = X4
                        & m1_subset_1(X5,u1_struct_0(sK0)) )
                    & m1_subset_1(X4,u1_struct_0(sK0)) )
                & m1_subset_1(X3,u1_struct_0(X1)) )
            & m1_subset_1(X2,u1_struct_0(X1)) )
        & m1_yellow_0(X1,sK0)
        & v5_yellow_0(X1,sK0)
        & v4_yellow_0(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k12_lattice3(sK0,X4,X5) != k12_lattice3(sK1,X2,X3)
                      & X3 = X5
                      & X2 = X4
                      & m1_subset_1(X5,u1_struct_0(sK0)) )
                  & m1_subset_1(X4,u1_struct_0(sK0)) )
              & m1_subset_1(X3,u1_struct_0(sK1)) )
          & m1_subset_1(X2,u1_struct_0(sK1)) )
      & m1_yellow_0(sK1,sK0)
      & v5_yellow_0(sK1,sK0)
      & v4_yellow_0(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k12_lattice3(sK0,X4,X5) != k12_lattice3(sK1,X2,X3)
                    & X3 = X5
                    & X2 = X4
                    & m1_subset_1(X5,u1_struct_0(sK0)) )
                & m1_subset_1(X4,u1_struct_0(sK0)) )
            & m1_subset_1(X3,u1_struct_0(sK1)) )
        & m1_subset_1(X2,u1_struct_0(sK1)) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k12_lattice3(sK0,X4,X5) != k12_lattice3(sK1,sK2,X3)
                  & X3 = X5
                  & sK2 = X4
                  & m1_subset_1(X5,u1_struct_0(sK0)) )
              & m1_subset_1(X4,u1_struct_0(sK0)) )
          & m1_subset_1(X3,u1_struct_0(sK1)) )
      & m1_subset_1(sK2,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( k12_lattice3(sK0,X4,X5) != k12_lattice3(sK1,sK2,X3)
                & X3 = X5
                & sK2 = X4
                & m1_subset_1(X5,u1_struct_0(sK0)) )
            & m1_subset_1(X4,u1_struct_0(sK0)) )
        & m1_subset_1(X3,u1_struct_0(sK1)) )
   => ( ? [X4] :
          ( ? [X5] :
              ( k12_lattice3(sK0,X4,X5) != k12_lattice3(sK1,sK2,sK3)
              & sK3 = X5
              & sK2 = X4
              & m1_subset_1(X5,u1_struct_0(sK0)) )
          & m1_subset_1(X4,u1_struct_0(sK0)) )
      & m1_subset_1(sK3,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( k12_lattice3(sK0,X4,X5) != k12_lattice3(sK1,sK2,sK3)
            & sK3 = X5
            & sK2 = X4
            & m1_subset_1(X5,u1_struct_0(sK0)) )
        & m1_subset_1(X4,u1_struct_0(sK0)) )
   => ( ? [X5] :
          ( k12_lattice3(sK1,sK2,sK3) != k12_lattice3(sK0,sK4,X5)
          & sK3 = X5
          & sK2 = sK4
          & m1_subset_1(X5,u1_struct_0(sK0)) )
      & m1_subset_1(sK4,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X5] :
        ( k12_lattice3(sK1,sK2,sK3) != k12_lattice3(sK0,sK4,X5)
        & sK3 = X5
        & sK2 = sK4
        & m1_subset_1(X5,u1_struct_0(sK0)) )
   => ( k12_lattice3(sK1,sK2,sK3) != k12_lattice3(sK0,sK4,sK5)
      & sK3 = sK5
      & sK2 = sK4
      & m1_subset_1(sK5,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k12_lattice3(X1,X2,X3) != k12_lattice3(X0,X4,X5)
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_yellow_0(X1,X0)
          & v5_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k12_lattice3(X1,X2,X3) != k12_lattice3(X0,X4,X5)
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_yellow_0(X1,X0)
          & v5_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( m1_yellow_0(X1,X0)
              & v5_yellow_0(X1,X0)
              & v4_yellow_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X0))
                           => ( ( X3 = X5
                                & X2 = X4 )
                             => k12_lattice3(X1,X2,X3) = k12_lattice3(X0,X4,X5) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v5_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X0))
                         => ( ( X3 = X5
                              & X2 = X4 )
                           => k12_lattice3(X1,X2,X3) = k12_lattice3(X0,X4,X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_yellow_0)).

fof(f237,plain,(
    ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f236,f73])).

fof(f73,plain,(
    m1_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f236,plain,(
    ! [X0] :
      ( ~ m1_yellow_0(sK1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f235,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_yellow_0)).

fof(f235,plain,(
    ~ l1_orders_2(sK1) ),
    inference(subsumption_resolution,[],[f234,f81])).

fof(f81,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f234,plain,
    ( ~ l1_orders_2(sK1)
    | ~ l1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f233,f70])).

fof(f70,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f233,plain,
    ( ~ l1_orders_2(sK1)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f232,f84])).

fof(f84,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f232,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_orders_2(sK1) ),
    inference(subsumption_resolution,[],[f231,f74])).

fof(f74,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f54])).

fof(f231,plain,
    ( ~ l1_orders_2(sK1)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(resolution,[],[f230,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f230,plain,
    ( ~ r2_hidden(sK2,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1) ),
    inference(resolution,[],[f229,f81])).

fof(f229,plain,
    ( ~ l1_struct_0(sK1)
    | ~ r2_hidden(sK2,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f228,f70])).

fof(f228,plain,
    ( ~ r2_hidden(sK2,u1_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f227,f84])).

fof(f227,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ r2_hidden(sK2,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f226,f75])).

fof(f75,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f54])).

fof(f226,plain,
    ( ~ r2_hidden(sK2,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(resolution,[],[f225,f109])).

fof(f225,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK1))
    | ~ r2_hidden(sK2,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f224,f75])).

fof(f224,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ r2_hidden(sK2,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f223,f74])).

fof(f223,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ r2_hidden(sK2,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f222,f115])).

fof(f115,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f76,f78])).

fof(f78,plain,(
    sK2 = sK4 ),
    inference(cnf_transformation,[],[f54])).

fof(f76,plain,(
    m1_subset_1(sK4,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f54])).

fof(f222,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_hidden(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ r2_hidden(sK2,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f221,f114])).

fof(f114,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f77,f79])).

fof(f79,plain,(
    sK3 = sK5 ),
    inference(cnf_transformation,[],[f54])).

fof(f77,plain,(
    m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f54])).

fof(f221,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_hidden(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ r2_hidden(sK2,u1_struct_0(sK1)) ),
    inference(trivial_inequality_removal,[],[f220])).

fof(f220,plain,
    ( k12_lattice3(sK0,sK2,sK3) != k12_lattice3(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_hidden(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ r2_hidden(sK2,u1_struct_0(sK1)) ),
    inference(superposition,[],[f113,f217])).

fof(f217,plain,(
    ! [X0,X1] :
      ( k12_lattice3(sK0,X0,X1) = k12_lattice3(sK1,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ r2_hidden(X0,u1_struct_0(sK1)) ) ),
    inference(duplicate_literal_removal,[],[f216])).

fof(f216,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | k12_lattice3(sK0,X0,X1) = k12_lattice3(sK1,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f214,f193])).

fof(f193,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k12_lattice3(sK0,X0,X1),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | k12_lattice3(sK0,X0,X1) = k12_lattice3(sK1,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f192,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( r2_yellow_0(sK0,k2_tarski(X1,X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f118,f67])).

fof(f67,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_yellow_0(sK0,k2_tarski(X1,X0))
      | ~ v5_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f117,f69])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_yellow_0(sK0,k2_tarski(X1,X0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0) ) ),
    inference(resolution,[],[f101,f68])).

fof(f68,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f101,plain,(
    ! [X4,X0,X3] :
      ( ~ v2_lattice3(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r2_yellow_0(X0,k2_tarski(X3,X4))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ( ( v2_lattice3(X0)
          | ( ~ r2_yellow_0(X0,k2_tarski(sK8(X0),sK9(X0)))
            & m1_subset_1(sK9(X0),u1_struct_0(X0))
            & m1_subset_1(sK8(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( r2_yellow_0(X0,k2_tarski(X3,X4))
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v2_lattice3(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f61,f63,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ~ r2_yellow_0(X0,k2_tarski(sK8(X0),X2))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK8(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ~ r2_yellow_0(X0,k2_tarski(sK8(X0),X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r2_yellow_0(X0,k2_tarski(sK8(X0),sK9(X0)))
        & m1_subset_1(sK9(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ( ( v2_lattice3(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( r2_yellow_0(X0,k2_tarski(X3,X4))
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v2_lattice3(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ( ( v2_lattice3(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( r2_yellow_0(X0,k2_tarski(X1,X2))
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v2_lattice3(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( r2_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( r2_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ( v2_lattice3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => r2_yellow_0(X0,k2_tarski(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_yellow_0)).

fof(f192,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k12_lattice3(sK0,X0,X1),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ r2_yellow_0(sK0,k2_tarski(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | k12_lattice3(sK0,X0,X1) = k12_lattice3(sK1,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f190,f150])).

fof(f150,plain,(
    ! [X0,X1] :
      ( k12_lattice3(sK0,X0,X1) = k2_yellow_0(sK0,k2_tarski(X0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f149])).

fof(f149,plain,(
    ! [X0,X1] :
      ( k12_lattice3(sK0,X0,X1) = k2_yellow_0(sK0,k2_tarski(X0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f147,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X0) = k7_domain_1(u1_struct_0(sK0),X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f129,f68])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k2_tarski(X1,X0) = k7_domain_1(u1_struct_0(sK0),X1,X0)
      | ~ v2_lattice3(sK0) ) ),
    inference(resolution,[],[f127,f69])).

fof(f127,plain,(
    ! [X4,X2,X3] :
      ( ~ l1_orders_2(X2)
      | ~ m1_subset_1(X4,u1_struct_0(X2))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | k2_tarski(X3,X4) = k7_domain_1(u1_struct_0(X2),X3,X4)
      | ~ v2_lattice3(X2) ) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,(
    ! [X4,X2,X3] :
      ( k2_tarski(X3,X4) = k7_domain_1(u1_struct_0(X2),X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X2))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_orders_2(X2)
      | ~ v2_lattice3(X2)
      | ~ l1_orders_2(X2) ) ),
    inference(resolution,[],[f124,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X1)
      | k7_domain_1(u1_struct_0(X1),X0,X2) = k2_tarski(X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f116,f81])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k7_domain_1(u1_struct_0(X1),X2,X0) = k2_tarski(X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f111,f84])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_domain_1)).

fof(f147,plain,(
    ! [X0,X1] :
      ( k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X1,X0)) = k12_lattice3(sK0,X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f146,f66])).

fof(f66,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v4_orders_2(sK0)
      | k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X1,X0)) = k12_lattice3(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f145,f67])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X1,X0)) = k12_lattice3(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f144,f68])).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v2_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X1,X0)) = k12_lattice3(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f142,f69])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X1,X0)) = k12_lattice3(sK0,X1,X0) ) ),
    inference(resolution,[],[f94,f65])).

fof(f65,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) = k12_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) = k12_lattice3(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) = k12_lattice3(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) = k12_lattice3(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_yellow_0)).

fof(f190,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k2_yellow_0(sK0,k2_tarski(X0,X1)),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ r2_yellow_0(sK0,k2_tarski(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | k2_yellow_0(sK0,k2_tarski(X0,X1)) = k12_lattice3(sK1,X0,X1) ) ),
    inference(subsumption_resolution,[],[f189,f69])).

fof(f189,plain,(
    ! [X0,X1] :
      ( k2_yellow_0(sK0,k2_tarski(X0,X1)) = k12_lattice3(sK1,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ r2_yellow_0(sK0,k2_tarski(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ r2_hidden(k2_yellow_0(sK0,k2_tarski(X0,X1)),u1_struct_0(sK1))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f188,f73])).

fof(f188,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_yellow_0(sK1,X2)
      | k2_yellow_0(sK0,k2_tarski(X0,X1)) = k12_lattice3(sK1,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ r2_yellow_0(sK0,k2_tarski(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ r2_hidden(k2_yellow_0(sK0,k2_tarski(X0,X1)),u1_struct_0(sK1))
      | ~ l1_orders_2(X2) ) ),
    inference(resolution,[],[f187,f83])).

fof(f187,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(sK1)
      | ~ r2_hidden(k2_yellow_0(sK0,k2_tarski(X1,X0)),u1_struct_0(sK1))
      | k2_yellow_0(sK0,k2_tarski(X1,X0)) = k12_lattice3(sK1,X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ r2_yellow_0(sK0,k2_tarski(X1,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f186,f81])).

fof(f186,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ r2_hidden(k2_yellow_0(sK0,k2_tarski(X0,X1)),u1_struct_0(sK1))
      | k2_yellow_0(sK0,k2_tarski(X0,X1)) = k12_lattice3(sK1,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ r2_yellow_0(sK0,k2_tarski(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f185,f70])).

fof(f185,plain,(
    ! [X0,X1] :
      ( ~ r2_yellow_0(sK0,k2_tarski(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ r2_hidden(k2_yellow_0(sK0,k2_tarski(X0,X1)),u1_struct_0(sK1))
      | k2_yellow_0(sK0,k2_tarski(X0,X1)) = k12_lattice3(sK1,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ l1_struct_0(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f184,f84])).

fof(f184,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(u1_struct_0(sK1))
      | ~ r2_yellow_0(sK0,k2_tarski(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ r2_hidden(k2_yellow_0(sK0,k2_tarski(X0,X1)),u1_struct_0(sK1))
      | k2_yellow_0(sK0,k2_tarski(X0,X1)) = k12_lattice3(sK1,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(duplicate_literal_removal,[],[f183])).

fof(f183,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ r2_yellow_0(sK0,k2_tarski(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ r2_hidden(k2_yellow_0(sK0,k2_tarski(X0,X1)),u1_struct_0(sK1))
      | k2_yellow_0(sK0,k2_tarski(X0,X1)) = k12_lattice3(sK1,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f182,f139])).

fof(f139,plain,(
    ! [X2,X1] :
      ( m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(duplicate_literal_removal,[],[f138])).

fof(f138,plain,(
    ! [X2,X1] :
      ( m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X2,u1_struct_0(sK1)) ) ),
    inference(superposition,[],[f110,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k7_domain_1(u1_struct_0(sK1),X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f135,f69])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | k2_tarski(X0,X1) = k7_domain_1(u1_struct_0(sK1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f128,f73])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_yellow_0(sK1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | k2_tarski(X1,X0) = k7_domain_1(u1_struct_0(sK1),X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ l1_orders_2(X2) ) ),
    inference(resolution,[],[f125,f83])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | k2_tarski(X0,X1) = k7_domain_1(u1_struct_0(sK1),X0,X1) ) ),
    inference(resolution,[],[f124,f70])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_domain_1)).

fof(f182,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_tarski(X1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ r2_yellow_0(sK0,k2_tarski(X1,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ r2_hidden(k2_yellow_0(sK0,k2_tarski(X1,X0)),u1_struct_0(sK1))
      | k2_yellow_0(sK0,k2_tarski(X1,X0)) = k12_lattice3(sK1,X1,X0) ) ),
    inference(subsumption_resolution,[],[f181,f69])).

fof(f181,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ r2_yellow_0(sK0,k2_tarski(X1,X0))
      | ~ m1_subset_1(k2_tarski(X1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r2_hidden(k2_yellow_0(sK0,k2_tarski(X1,X0)),u1_struct_0(sK1))
      | k2_yellow_0(sK0,k2_tarski(X1,X0)) = k12_lattice3(sK1,X1,X0)
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f180,f68])).

fof(f180,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ r2_yellow_0(sK0,k2_tarski(X1,X0))
      | ~ m1_subset_1(k2_tarski(X1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r2_hidden(k2_yellow_0(sK0,k2_tarski(X1,X0)),u1_struct_0(sK1))
      | k2_yellow_0(sK0,k2_tarski(X1,X0)) = k12_lattice3(sK1,X1,X0)
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f178,f82])).

fof(f178,plain,(
    ! [X2,X3] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ r2_yellow_0(sK0,k2_tarski(X2,X3))
      | ~ m1_subset_1(k2_tarski(X2,X3),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r2_hidden(k2_yellow_0(sK0,k2_tarski(X2,X3)),u1_struct_0(sK1))
      | k12_lattice3(sK1,X2,X3) = k2_yellow_0(sK0,k2_tarski(X2,X3)) ) ),
    inference(superposition,[],[f177,f158])).

fof(f158,plain,(
    ! [X0] :
      ( k2_yellow_0(sK0,X0) = k2_yellow_0(sK1,X0)
      | ~ r2_yellow_0(sK0,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r2_hidden(k2_yellow_0(sK0,X0),u1_struct_0(sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f157,f66])).

fof(f157,plain,(
    ! [X0] :
      ( ~ r2_hidden(k2_yellow_0(sK0,X0),u1_struct_0(sK1))
      | ~ r2_yellow_0(sK0,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | k2_yellow_0(sK0,X0) = k2_yellow_0(sK1,X0)
      | ~ v4_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f156,f69])).

fof(f156,plain,(
    ! [X0] :
      ( ~ r2_hidden(k2_yellow_0(sK0,X0),u1_struct_0(sK1))
      | ~ r2_yellow_0(sK0,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | k2_yellow_0(sK0,X0) = k2_yellow_0(sK1,X0)
      | ~ l1_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f155,f70])).

fof(f155,plain,(
    ! [X0] :
      ( ~ r2_hidden(k2_yellow_0(sK0,X0),u1_struct_0(sK1))
      | ~ r2_yellow_0(sK0,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | k2_yellow_0(sK0,X0) = k2_yellow_0(sK1,X0)
      | v2_struct_0(sK1)
      | ~ l1_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f154,f73])).

fof(f154,plain,(
    ! [X0] :
      ( ~ r2_hidden(k2_yellow_0(sK0,X0),u1_struct_0(sK1))
      | ~ r2_yellow_0(sK0,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_yellow_0(sK1,sK0)
      | k2_yellow_0(sK0,X0) = k2_yellow_0(sK1,X0)
      | v2_struct_0(sK1)
      | ~ l1_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f86,f71])).

fof(f71,plain,(
    v4_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_yellow_0(X1,X0)
      | ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
      | ~ r2_yellow_0(X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_yellow_0(X1,X0)
      | k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
                & r2_yellow_0(X1,X2) )
              | ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
              | ~ r2_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
                & r2_yellow_0(X1,X2) )
              | ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
              | ~ r2_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
                  & r2_yellow_0(X0,X2) )
               => ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
                  & r2_yellow_0(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_yellow_0)).

fof(f177,plain,(
    ! [X0,X1] :
      ( k12_lattice3(sK1,X0,X1) = k2_yellow_0(sK1,k2_tarski(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(duplicate_literal_removal,[],[f174])).

fof(f174,plain,(
    ! [X0,X1] :
      ( k12_lattice3(sK1,X0,X1) = k2_yellow_0(sK1,k2_tarski(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ) ),
    inference(superposition,[],[f173,f136])).

fof(f173,plain,(
    ! [X0,X1] :
      ( k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),X0,X1)) = k12_lattice3(sK1,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f172,f66])).

fof(f172,plain,(
    ! [X0,X1] :
      ( k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),X0,X1)) = k12_lattice3(sK1,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ v4_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f171,f67])).

fof(f171,plain,(
    ! [X0,X1] :
      ( k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),X0,X1)) = k12_lattice3(sK1,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f170,f68])).

fof(f170,plain,(
    ! [X0,X1] :
      ( k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),X0,X1)) = k12_lattice3(sK1,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ v2_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f169,f69])).

fof(f169,plain,(
    ! [X0,X1] :
      ( k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),X0,X1)) = k12_lattice3(sK1,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f168,f73])).

fof(f168,plain,(
    ! [X0,X1] :
      ( k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),X0,X1)) = k12_lattice3(sK1,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_yellow_0(sK1,sK0)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f167,f72])).

fof(f72,plain,(
    v5_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f167,plain,(
    ! [X0,X1] :
      ( k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),X0,X1)) = k12_lattice3(sK1,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ v5_yellow_0(sK1,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_yellow_0(sK1,sK0)
      | ~ l1_orders_2(sK0)
      | ~ v2_lattice3(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0) ) ),
    inference(resolution,[],[f166,f71])).

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_yellow_0(sK1,X2)
      | k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),X0,X1)) = k12_lattice3(sK1,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ v5_yellow_0(sK1,X2)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_yellow_0(sK1,X2)
      | ~ l1_orders_2(X2)
      | ~ v2_lattice3(X2)
      | ~ v5_orders_2(X2)
      | ~ v4_orders_2(X2) ) ),
    inference(subsumption_resolution,[],[f165,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( v5_orders_2(X1)
      | ~ v4_yellow_0(X1,X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_yellow_0(X1,X0)
            & v5_orders_2(X1) )
          | ~ v4_yellow_0(X1,X0)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_yellow_0(X1,X0)
            & v5_orders_2(X1) )
          | ~ v4_yellow_0(X1,X0)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ( v4_yellow_0(X1,X0)
           => ( v4_yellow_0(X1,X0)
              & v5_orders_2(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc8_yellow_0)).

fof(f165,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ v5_orders_2(sK1)
      | k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),X0,X1)) = k12_lattice3(sK1,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ v5_yellow_0(sK1,X2)
      | ~ v4_yellow_0(sK1,X2)
      | ~ m1_yellow_0(sK1,X2)
      | ~ l1_orders_2(X2)
      | ~ v2_lattice3(X2)
      | ~ v5_orders_2(X2)
      | ~ v4_orders_2(X2) ) ),
    inference(subsumption_resolution,[],[f164,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( v4_orders_2(X1)
      | ~ v4_yellow_0(X1,X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_yellow_0(X1,X0)
            & v4_orders_2(X1) )
          | ~ v4_yellow_0(X1,X0)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_yellow_0(X1,X0)
            & v4_orders_2(X1) )
          | ~ v4_yellow_0(X1,X0)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ( v4_yellow_0(X1,X0)
           => ( v4_yellow_0(X1,X0)
              & v4_orders_2(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc7_yellow_0)).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ v5_orders_2(sK1)
      | ~ v4_orders_2(sK1)
      | k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),X0,X1)) = k12_lattice3(sK1,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ v5_yellow_0(sK1,X2)
      | ~ v4_yellow_0(sK1,X2)
      | ~ m1_yellow_0(sK1,X2)
      | ~ l1_orders_2(X2)
      | ~ v2_lattice3(X2)
      | ~ v5_orders_2(X2)
      | ~ v4_orders_2(X2) ) ),
    inference(subsumption_resolution,[],[f163,f70])).

fof(f163,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ v5_orders_2(sK1)
      | ~ v4_orders_2(sK1)
      | k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),X0,X1)) = k12_lattice3(sK1,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ v5_yellow_0(sK1,X2)
      | ~ v4_yellow_0(sK1,X2)
      | v2_struct_0(sK1)
      | ~ m1_yellow_0(sK1,X2)
      | ~ l1_orders_2(X2)
      | ~ v2_lattice3(X2)
      | ~ v5_orders_2(X2)
      | ~ v4_orders_2(X2) ) ),
    inference(resolution,[],[f162,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( v2_lattice3(X1)
      | ~ v5_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & v2_lattice3(X1)
            & ~ v2_struct_0(X1) )
          | ~ v5_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & v2_lattice3(X1)
            & ~ v2_struct_0(X1) )
          | ~ v5_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ( ( v5_yellow_0(X1,X0)
              & v4_yellow_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( v5_yellow_0(X1,X0)
              & v4_yellow_0(X1,X0)
              & v2_lattice3(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc11_yellow_0)).

fof(f162,plain,(
    ! [X0,X1] :
      ( ~ v2_lattice3(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ v5_orders_2(sK1)
      | ~ v4_orders_2(sK1)
      | k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),X0,X1)) = k12_lattice3(sK1,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f161,f65])).

fof(f161,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ v2_lattice3(sK1)
      | ~ v5_orders_2(sK1)
      | ~ v4_orders_2(sK1)
      | k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),X0,X1)) = k12_lattice3(sK1,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f160,f69])).

fof(f160,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ v2_lattice3(sK1)
      | ~ v5_orders_2(sK1)
      | ~ v4_orders_2(sK1)
      | k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),X0,X1)) = k12_lattice3(sK1,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ l1_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f159,f73])).

fof(f159,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ v2_lattice3(sK1)
      | ~ v5_orders_2(sK1)
      | ~ v4_orders_2(sK1)
      | k2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),X0,X1)) = k12_lattice3(sK1,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_yellow_0(sK1,sK0)
      | ~ l1_orders_2(sK0)
      | ~ v3_orders_2(sK0) ) ),
    inference(resolution,[],[f148,f71])).

fof(f148,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ v4_yellow_0(X3,X5)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ v2_lattice3(X3)
      | ~ v5_orders_2(X3)
      | ~ v4_orders_2(X3)
      | k2_yellow_0(X3,k7_domain_1(u1_struct_0(X3),X4,X2)) = k12_lattice3(X3,X4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X3))
      | ~ m1_yellow_0(X3,X5)
      | ~ l1_orders_2(X5)
      | ~ v3_orders_2(X5) ) ),
    inference(subsumption_resolution,[],[f143,f83])).

fof(f143,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v2_lattice3(X3)
      | ~ v5_orders_2(X3)
      | ~ v4_orders_2(X3)
      | k2_yellow_0(X3,k7_domain_1(u1_struct_0(X3),X4,X2)) = k12_lattice3(X3,X4,X2)
      | ~ v4_yellow_0(X3,X5)
      | ~ m1_yellow_0(X3,X5)
      | ~ l1_orders_2(X5)
      | ~ v3_orders_2(X5) ) ),
    inference(resolution,[],[f94,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v3_orders_2(X1)
      | ~ v4_yellow_0(X1,X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_yellow_0(X1,X0)
            & v3_orders_2(X1) )
          | ~ v4_yellow_0(X1,X0)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_yellow_0(X1,X0)
            & v3_orders_2(X1) )
          | ~ v4_yellow_0(X1,X0)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ( v4_yellow_0(X1,X0)
           => ( v4_yellow_0(X1,X0)
              & v3_orders_2(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_yellow_0)).

fof(f214,plain,(
    ! [X0,X1] :
      ( r2_hidden(k12_lattice3(sK0,X0,X1),u1_struct_0(sK1))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X1,u1_struct_0(sK1)) ) ),
    inference(duplicate_literal_removal,[],[f213])).

fof(f213,plain,(
    ! [X0,X1] :
      ( r2_hidden(k12_lattice3(sK0,X0,X1),u1_struct_0(sK1))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f211,f150])).

fof(f211,plain,(
    ! [X0,X1] :
      ( r2_hidden(k2_yellow_0(sK0,k2_tarski(X0,X1)),u1_struct_0(sK1))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X1,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f210,f119])).

fof(f210,plain,(
    ! [X0,X1] :
      ( r2_hidden(k2_yellow_0(sK0,k2_tarski(X0,X1)),u1_struct_0(sK1))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X1,u1_struct_0(sK1))
      | ~ r2_yellow_0(sK0,k2_tarski(X0,X1)) ) ),
    inference(duplicate_literal_removal,[],[f207])).

fof(f207,plain,(
    ! [X0,X1] :
      ( r2_hidden(k2_yellow_0(sK0,k2_tarski(X0,X1)),u1_struct_0(sK1))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X1,u1_struct_0(sK1))
      | ~ r2_yellow_0(sK0,k2_tarski(X0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f206,f131])).

fof(f206,plain,(
    ! [X0,X1] :
      ( r2_hidden(k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X1,X0)),u1_struct_0(sK1))
      | ~ r2_hidden(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | ~ r2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X1,X0)) ) ),
    inference(subsumption_resolution,[],[f205,f69])).

fof(f205,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(sK1))
      | ~ r2_hidden(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X1,X0)),u1_struct_0(sK1))
      | ~ r2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X1,X0))
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f204,f68])).

fof(f204,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(sK1))
      | ~ r2_hidden(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X1,X0)),u1_struct_0(sK1))
      | ~ r2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X1,X0))
      | ~ v2_lattice3(sK0)
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f203,f82])).

fof(f203,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ r2_hidden(X1,u1_struct_0(sK1))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X0,X1)),u1_struct_0(sK1))
      | ~ r2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X0,X1)) ) ),
    inference(subsumption_resolution,[],[f202,f69])).

fof(f202,plain,(
    ! [X0,X1] :
      ( ~ r2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X0,X1))
      | ~ r2_hidden(X1,u1_struct_0(sK1))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X0,X1)),u1_struct_0(sK1))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f201,f72])).

fof(f201,plain,(
    ! [X0,X1] :
      ( ~ r2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X0,X1))
      | ~ r2_hidden(X1,u1_struct_0(sK1))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v5_yellow_0(sK1,sK0)
      | r2_hidden(k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X0,X1)),u1_struct_0(sK1))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f87,f73])).

fof(f87,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ m1_yellow_0(X1,X0)
      | ~ r2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X4,X5))
      | ~ r2_hidden(X5,u1_struct_0(X1))
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v5_yellow_0(X1,X0)
      | r2_hidden(k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X4,X5)),u1_struct_0(X1))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_yellow_0(X1,X0)
              | ( ~ r2_hidden(k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),sK6(X0,X1),sK7(X0,X1))),u1_struct_0(X1))
                & r2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),sK6(X0,X1),sK7(X0,X1)))
                & r2_hidden(sK7(X0,X1),u1_struct_0(X1))
                & r2_hidden(sK6(X0,X1),u1_struct_0(X1))
                & m1_subset_1(sK7(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X4,X5)),u1_struct_0(X1))
                      | ~ r2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X4,X5))
                      | ~ r2_hidden(X5,u1_struct_0(X1))
                      | ~ r2_hidden(X4,u1_struct_0(X1))
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v5_yellow_0(X1,X0) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f56,f58,f57])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3)),u1_struct_0(X1))
              & r2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3))
              & r2_hidden(X3,u1_struct_0(X1))
              & r2_hidden(X2,u1_struct_0(X1))
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),sK6(X0,X1),X3)),u1_struct_0(X1))
            & r2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),sK6(X0,X1),X3))
            & r2_hidden(X3,u1_struct_0(X1))
            & r2_hidden(sK6(X0,X1),u1_struct_0(X1))
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),sK6(X0,X1),X3)),u1_struct_0(X1))
          & r2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),sK6(X0,X1),X3))
          & r2_hidden(X3,u1_struct_0(X1))
          & r2_hidden(sK6(X0,X1),u1_struct_0(X1))
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),sK6(X0,X1),sK7(X0,X1))),u1_struct_0(X1))
        & r2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),sK6(X0,X1),sK7(X0,X1)))
        & r2_hidden(sK7(X0,X1),u1_struct_0(X1))
        & r2_hidden(sK6(X0,X1),u1_struct_0(X1))
        & m1_subset_1(sK7(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_yellow_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3)),u1_struct_0(X1))
                      & r2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3))
                      & r2_hidden(X3,u1_struct_0(X1))
                      & r2_hidden(X2,u1_struct_0(X1))
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X4,X5)),u1_struct_0(X1))
                      | ~ r2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X4,X5))
                      | ~ r2_hidden(X5,u1_struct_0(X1))
                      | ~ r2_hidden(X4,u1_struct_0(X1))
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v5_yellow_0(X1,X0) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_yellow_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3)),u1_struct_0(X1))
                      & r2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3))
                      & r2_hidden(X3,u1_struct_0(X1))
                      & r2_hidden(X2,u1_struct_0(X1))
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3)),u1_struct_0(X1))
                      | ~ r2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3))
                      | ~ r2_hidden(X3,u1_struct_0(X1))
                      | ~ r2_hidden(X2,u1_struct_0(X1))
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v5_yellow_0(X1,X0) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_yellow_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3)),u1_struct_0(X1))
                    | ~ r2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3))
                    | ~ r2_hidden(X3,u1_struct_0(X1))
                    | ~ r2_hidden(X2,u1_struct_0(X1))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_yellow_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3)),u1_struct_0(X1))
                    | ~ r2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3))
                    | ~ r2_hidden(X3,u1_struct_0(X1))
                    | ~ r2_hidden(X2,u1_struct_0(X1))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ( v5_yellow_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3))
                        & r2_hidden(X3,u1_struct_0(X1))
                        & r2_hidden(X2,u1_struct_0(X1)) )
                     => r2_hidden(k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X2,X3)),u1_struct_0(X1)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_yellow_0)).

fof(f113,plain,(
    k12_lattice3(sK1,sK2,sK3) != k12_lattice3(sK0,sK2,sK3) ),
    inference(backward_demodulation,[],[f112,f78])).

fof(f112,plain,(
    k12_lattice3(sK1,sK2,sK3) != k12_lattice3(sK0,sK4,sK3) ),
    inference(backward_demodulation,[],[f80,f79])).

fof(f80,plain,(
    k12_lattice3(sK1,sK2,sK3) != k12_lattice3(sK0,sK4,sK5) ),
    inference(cnf_transformation,[],[f54])).

%------------------------------------------------------------------------------
