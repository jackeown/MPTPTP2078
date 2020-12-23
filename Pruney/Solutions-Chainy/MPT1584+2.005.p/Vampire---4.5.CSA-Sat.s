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
% DateTime   : Thu Dec  3 13:16:24 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   23 (  23 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    0
%              Number of atoms          :   84 (  84 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   11 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u96,negated_conjecture,(
    sK3 = sK4 )).

tff(u95,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r2_hidden(sK5(X0,X1,X2),X3)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_lattice3(X0,X3,X2)
      | r1_lattice3(X0,X1,X2) ) )).

tff(u94,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r2_hidden(sK6(X0,X1,X2),X3)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_lattice3(X0,X3,X2)
      | r2_lattice3(X0,X1,X2) ) )).

tff(u93,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK5(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,X2) ) )).

tff(u92,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK6(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,X2) ) )).

tff(u91,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_subset_1(sK5(X1,X2,X0),u1_struct_0(X1))
      | ~ r2_hidden(sK5(X1,X2,X0),X3)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ r1_lattice3(X1,X3,X0)
      | r1_lattice3(X1,X2,X0) ) )).

tff(u90,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ m1_subset_1(sK6(X5,X6,X4),u1_struct_0(X5))
      | ~ r2_hidden(sK6(X5,X6,X4),X7)
      | ~ m1_subset_1(X4,u1_struct_0(X5))
      | ~ l1_orders_2(X5)
      | ~ r2_lattice3(X5,X7,X4)
      | r2_lattice3(X5,X6,X4) ) )).

tff(u89,negated_conjecture,(
    m1_subset_1(sK3,u1_struct_0(sK0)) )).

tff(u88,negated_conjecture,(
    m1_subset_1(sK3,u1_struct_0(sK1)) )).

tff(u87,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,X2) ) )).

tff(u86,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,X2) ) )).

tff(u85,negated_conjecture,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) )).

tff(u84,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) )).

tff(u83,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u82,negated_conjecture,
    ( ~ ~ r1_lattice3(sK0,sK2,sK3)
    | ~ r1_lattice3(sK0,sK2,sK3) )).

tff(u81,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r1_lattice3(X4,X7,sK6(X4,X5,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ r2_hidden(X6,X7)
      | ~ l1_orders_2(X4)
      | ~ m1_subset_1(sK6(X4,X5,X6),u1_struct_0(X4))
      | r2_lattice3(X4,X5,X6) ) )).

tff(u80,negated_conjecture,
    ( ~ r1_lattice3(sK1,sK2,sK4)
    | r1_lattice3(sK1,sK2,sK3) )).

tff(u79,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,X2) ) )).

tff(u78,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,X2) ) )).

tff(u77,axiom,(
    ! [X1,X3,X0,X2] :
      ( r1_orders_2(X0,X3,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X3,X1)
      | ~ l1_orders_2(X0)
      | ~ r2_lattice3(X0,X1,X2) ) )).

tff(u76,axiom,(
    ! [X1,X3,X0,X2] :
      ( r1_orders_2(X0,X2,X3)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X3,X1)
      | ~ l1_orders_2(X0)
      | ~ r1_lattice3(X0,X1,X2) ) )).

tff(u75,negated_conjecture,
    ( ~ ~ r2_lattice3(sK0,sK2,sK3)
    | ~ r2_lattice3(sK0,sK2,sK3) )).

% (23430)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
tff(u74,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r2_lattice3(X0,X3,sK5(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,X3)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:02:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (23426)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.49  % (23425)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.49  % (23424)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.49  % (23435)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.49  % (23416)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.49  % (23418)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.49  % (23434)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.49  % (23420)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.49  % (23415)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.50  % (23423)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.50  % (23419)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.50  % (23417)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.50  % (23438)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.50  % (23427)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.50  % (23437)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.50  % (23433)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.50  % (23427)# SZS output start Saturation.
% 0.20/0.50  tff(u96,negated_conjecture,
% 0.20/0.50      (sK3 = sK4)).
% 0.20/0.50  
% 0.20/0.50  tff(u95,axiom,
% 0.20/0.50      (![X1, X3, X0, X2] : ((~r2_hidden(sK5(X0,X1,X2),X3) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r1_lattice3(X0,X3,X2) | r1_lattice3(X0,X1,X2))))).
% 0.20/0.50  
% 0.20/0.50  tff(u94,axiom,
% 0.20/0.50      (![X1, X3, X0, X2] : ((~r2_hidden(sK6(X0,X1,X2),X3) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r2_lattice3(X0,X3,X2) | r2_lattice3(X0,X1,X2))))).
% 0.20/0.50  
% 0.20/0.50  tff(u93,axiom,
% 0.20/0.50      (![X1, X0, X2] : ((r2_hidden(sK5(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,X2))))).
% 0.20/0.50  
% 0.20/0.50  tff(u92,axiom,
% 0.20/0.50      (![X1, X0, X2] : ((r2_hidden(sK6(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2))))).
% 0.20/0.50  
% 0.20/0.50  tff(u91,axiom,
% 0.20/0.50      (![X1, X3, X0, X2] : ((~m1_subset_1(sK5(X1,X2,X0),u1_struct_0(X1)) | ~r2_hidden(sK5(X1,X2,X0),X3) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~r1_lattice3(X1,X3,X0) | r1_lattice3(X1,X2,X0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u90,axiom,
% 0.20/0.50      (![X5, X7, X4, X6] : ((~m1_subset_1(sK6(X5,X6,X4),u1_struct_0(X5)) | ~r2_hidden(sK6(X5,X6,X4),X7) | ~m1_subset_1(X4,u1_struct_0(X5)) | ~l1_orders_2(X5) | ~r2_lattice3(X5,X7,X4) | r2_lattice3(X5,X6,X4))))).
% 0.20/0.50  
% 0.20/0.50  tff(u89,negated_conjecture,
% 0.20/0.50      m1_subset_1(sK3,u1_struct_0(sK0))).
% 0.20/0.50  
% 0.20/0.50  tff(u88,negated_conjecture,
% 0.20/0.50      m1_subset_1(sK3,u1_struct_0(sK1))).
% 0.20/0.50  
% 0.20/0.50  tff(u87,axiom,
% 0.20/0.50      (![X1, X0, X2] : ((m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,X2))))).
% 0.20/0.50  
% 0.20/0.50  tff(u86,axiom,
% 0.20/0.50      (![X1, X0, X2] : ((m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2))))).
% 0.20/0.50  
% 0.20/0.50  tff(u85,negated_conjecture,
% 0.20/0.50      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))).
% 0.20/0.50  
% 0.20/0.50  tff(u84,axiom,
% 0.20/0.50      (![X1, X0, X2] : ((m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))))).
% 0.20/0.50  
% 0.20/0.50  tff(u83,negated_conjecture,
% 0.20/0.50      l1_orders_2(sK0)).
% 0.20/0.50  
% 0.20/0.50  tff(u82,negated_conjecture,
% 0.20/0.50      ((~~r1_lattice3(sK0,sK2,sK3)) | ~r1_lattice3(sK0,sK2,sK3))).
% 0.20/0.50  
% 0.20/0.50  tff(u81,axiom,
% 0.20/0.50      (![X5, X7, X4, X6] : ((~r1_lattice3(X4,X7,sK6(X4,X5,X6)) | ~m1_subset_1(X6,u1_struct_0(X4)) | ~r2_hidden(X6,X7) | ~l1_orders_2(X4) | ~m1_subset_1(sK6(X4,X5,X6),u1_struct_0(X4)) | r2_lattice3(X4,X5,X6))))).
% 0.20/0.50  
% 0.20/0.50  tff(u80,negated_conjecture,
% 0.20/0.50      ((~r1_lattice3(sK1,sK2,sK4)) | r1_lattice3(sK1,sK2,sK3))).
% 0.20/0.50  
% 0.20/0.50  tff(u79,axiom,
% 0.20/0.50      (![X1, X0, X2] : ((~r1_orders_2(X0,X2,sK5(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,X2))))).
% 0.20/0.50  
% 0.20/0.50  tff(u78,axiom,
% 0.20/0.50      (![X1, X0, X2] : ((~r1_orders_2(X0,sK6(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2))))).
% 0.20/0.50  
% 0.20/0.50  tff(u77,axiom,
% 0.20/0.50      (![X1, X3, X0, X2] : ((r1_orders_2(X0,X3,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X3,X1) | ~l1_orders_2(X0) | ~r2_lattice3(X0,X1,X2))))).
% 0.20/0.50  
% 0.20/0.50  tff(u76,axiom,
% 0.20/0.50      (![X1, X3, X0, X2] : ((r1_orders_2(X0,X2,X3) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X3,X1) | ~l1_orders_2(X0) | ~r1_lattice3(X0,X1,X2))))).
% 0.20/0.50  
% 0.20/0.50  tff(u75,negated_conjecture,
% 0.20/0.50      ((~~r2_lattice3(sK0,sK2,sK3)) | ~r2_lattice3(sK0,sK2,sK3))).
% 0.20/0.50  
% 0.20/0.50  % (23430)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.50  tff(u74,axiom,
% 0.20/0.50      (![X1, X3, X0, X2] : ((~r2_lattice3(X0,X3,sK5(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,X3) | ~l1_orders_2(X0) | ~m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | r1_lattice3(X0,X1,X2))))).
% 0.20/0.50  
% 0.20/0.50  % (23427)# SZS output end Saturation.
% 0.20/0.50  % (23427)------------------------------
% 0.20/0.50  % (23427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (23427)Termination reason: Satisfiable
% 0.20/0.50  
% 0.20/0.50  % (23427)Memory used [KB]: 10618
% 0.20/0.50  % (23427)Time elapsed: 0.083 s
% 0.20/0.50  % (23427)------------------------------
% 0.20/0.50  % (23427)------------------------------
% 0.20/0.50  % (23429)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.50  % (23414)Success in time 0.143 s
%------------------------------------------------------------------------------
