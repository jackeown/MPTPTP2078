%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:57 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   33 (  33 expanded)
%              Number of leaves         :   33 (  33 expanded)
%              Depth                    :    0
%              Number of atoms          :   86 (  86 expanded)
%              Number of equality atoms :   52 (  52 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u309,axiom,(
    ! [X3,X2] :
      ( sK3(X2,X3) != sK3(sK3(X2,X3),X3)
      | k1_tarski(X2) = X3
      | sK3(X2,X3) = X2
      | k1_tarski(sK3(X2,X3)) = X3 ) )).

tff(u308,axiom,(
    ! [X1,X0,X2] :
      ( sK3(X2,k1_tarski(X1)) != X0
      | sK3(X0,k1_tarski(X1)) = sK3(X2,k1_tarski(X1))
      | sK3(X2,k1_tarski(X1)) = X2
      | k1_tarski(X0) = k1_tarski(X1)
      | k1_tarski(X1) = k1_tarski(X2) ) )).

tff(u307,axiom,(
    ! [X1,X0,X2] :
      ( sK3(X2,k1_tarski(X1)) != X0
      | sK3(X2,k1_tarski(X1)) = X2
      | sK3(X0,k1_tarski(X1)) = X0
      | k1_tarski(X1) = k1_tarski(X2)
      | k1_tarski(X0) = k1_tarski(X1) ) )).

tff(u306,negated_conjecture,
    ( ~ ( k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_tarski(sK1)) != k1_tarski(k1_tarski(sK1)) )
    | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_tarski(sK1)) != k1_tarski(k1_tarski(sK1)) )).

tff(u305,axiom,(
    ! [X1,X0] :
      ( X0 != X1
      | sK3(X0,k1_tarski(X1)) = X0
      | k1_tarski(X0) = k1_tarski(X1) ) )).

tff(u304,axiom,(
    ! [X1,X0] :
      ( X0 != X1
      | sK3(X0,k1_tarski(X1)) = X1
      | k1_tarski(X0) = k1_tarski(X1) ) )).

tff(u303,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) != k1_tarski(sK1)
    | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) )).

tff(u302,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK2) != k1_tarski(sK2)
    | k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2) )).

tff(u301,axiom,(
    ! [X1,X0] :
      ( sK3(X0,k1_tarski(X1)) = X0
      | sK3(X0,k1_tarski(X1)) = X1
      | k1_tarski(X0) = k1_tarski(X1) ) )).

tff(u300,axiom,(
    ! [X3,X5,X4] :
      ( sK3(X3,k1_tarski(X4)) = sK3(X5,k1_tarski(X4))
      | sK3(X5,k1_tarski(X4)) = X5
      | sK3(X3,k1_tarski(X4)) = X3
      | k1_tarski(X5) = k1_tarski(X4)
      | k1_tarski(X3) = k1_tarski(X4) ) )).

tff(u299,axiom,(
    ! [X3,X2] :
      ( sK3(sK3(X2,k1_tarski(X3)),k1_tarski(X3)) = X3
      | sK3(X2,k1_tarski(X3)) = X2
      | k1_tarski(X3) = k1_tarski(sK3(X2,k1_tarski(X3)))
      | k1_tarski(X3) = k1_tarski(X2) ) )).

tff(u298,axiom,(
    ! [X1,X0] :
      ( k1_tarski(X1) = k1_tarski(sK3(X0,k1_tarski(X1)))
      | sK3(X0,k1_tarski(X1)) = X0
      | k1_tarski(X0) = k1_tarski(X1) ) )).

tff(u297,negated_conjecture,
    ( ~ ~ r2_hidden(sK2,k5_waybel_0(sK0,sK1))
    | ~ r2_hidden(sK2,k5_waybel_0(sK0,sK1)) )).

tff(u296,axiom,(
    ! [X9,X11,X10] :
      ( ~ r2_hidden(X11,k1_tarski(X10))
      | sK3(X9,k1_tarski(X10)) = X11
      | sK3(X9,k1_tarski(X10)) = X9
      | k1_tarski(X9) = k1_tarski(X10) ) )).

tff(u295,axiom,(
    ! [X3,X0] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) )).

tff(u294,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(X0,X1)
      | sK3(X0,X1) != X0
      | k1_tarski(X0) = X1 ) )).

tff(u293,axiom,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) )).

tff(u292,axiom,(
    ! [X1,X0] :
      ( r2_hidden(sK3(X0,X1),X1)
      | sK3(X0,X1) = X0
      | k1_tarski(X0) = X1 ) )).

tff(u291,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u290,negated_conjecture,(
    l1_struct_0(sK0) )).

tff(u289,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u288,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0)) )).

tff(u287,negated_conjecture,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u286,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) )).

tff(u285,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) )).

tff(u284,negated_conjecture,
    ( ~ ~ m1_subset_1(k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_tarski(sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_tarski(sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )).

tff(u283,negated_conjecture,(
    m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u282,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u281,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) != k1_tarski(sK1)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u280,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK2) != k1_tarski(sK2)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u279,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) )).

tff(u278,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u277,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK2,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:24:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.45  % (8407)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.46  % (8407)Refutation not found, incomplete strategy% (8407)------------------------------
% 0.20/0.46  % (8407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (8407)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (8407)Memory used [KB]: 10618
% 0.20/0.46  % (8407)Time elapsed: 0.051 s
% 0.20/0.46  % (8407)------------------------------
% 0.20/0.46  % (8407)------------------------------
% 0.20/0.46  % (8423)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.48  % (8419)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.49  % (8424)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.49  % (8406)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.49  % (8405)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.49  % (8411)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.49  % (8411)# SZS output start Saturation.
% 0.20/0.49  tff(u309,axiom,
% 0.20/0.49      (![X3, X2] : (((sK3(X2,X3) != sK3(sK3(X2,X3),X3)) | (k1_tarski(X2) = X3) | (sK3(X2,X3) = X2) | (k1_tarski(sK3(X2,X3)) = X3))))).
% 0.20/0.49  
% 0.20/0.49  tff(u308,axiom,
% 0.20/0.49      (![X1, X0, X2] : (((sK3(X2,k1_tarski(X1)) != X0) | (sK3(X0,k1_tarski(X1)) = sK3(X2,k1_tarski(X1))) | (sK3(X2,k1_tarski(X1)) = X2) | (k1_tarski(X0) = k1_tarski(X1)) | (k1_tarski(X1) = k1_tarski(X2)))))).
% 0.20/0.49  
% 0.20/0.49  tff(u307,axiom,
% 0.20/0.49      (![X1, X0, X2] : (((sK3(X2,k1_tarski(X1)) != X0) | (sK3(X2,k1_tarski(X1)) = X2) | (sK3(X0,k1_tarski(X1)) = X0) | (k1_tarski(X1) = k1_tarski(X2)) | (k1_tarski(X0) = k1_tarski(X1)))))).
% 0.20/0.49  
% 0.20/0.49  tff(u306,negated_conjecture,
% 0.20/0.49      ((~(k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_tarski(sK1)) != k1_tarski(k1_tarski(sK1)))) | (k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_tarski(sK1)) != k1_tarski(k1_tarski(sK1))))).
% 0.20/0.49  
% 0.20/0.49  tff(u305,axiom,
% 0.20/0.49      (![X1, X0] : (((X0 != X1) | (sK3(X0,k1_tarski(X1)) = X0) | (k1_tarski(X0) = k1_tarski(X1)))))).
% 0.20/0.49  
% 0.20/0.49  tff(u304,axiom,
% 0.20/0.49      (![X1, X0] : (((X0 != X1) | (sK3(X0,k1_tarski(X1)) = X1) | (k1_tarski(X0) = k1_tarski(X1)))))).
% 0.20/0.49  
% 0.20/0.49  tff(u303,negated_conjecture,
% 0.20/0.49      ((~(k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1))) | (k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)))).
% 0.20/0.49  
% 0.20/0.49  tff(u302,negated_conjecture,
% 0.20/0.49      ((~(k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2))) | (k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2)))).
% 0.20/0.49  
% 0.20/0.49  tff(u301,axiom,
% 0.20/0.49      (![X1, X0] : (((sK3(X0,k1_tarski(X1)) = X0) | (sK3(X0,k1_tarski(X1)) = X1) | (k1_tarski(X0) = k1_tarski(X1)))))).
% 0.20/0.49  
% 0.20/0.49  tff(u300,axiom,
% 0.20/0.49      (![X3, X5, X4] : (((sK3(X3,k1_tarski(X4)) = sK3(X5,k1_tarski(X4))) | (sK3(X5,k1_tarski(X4)) = X5) | (sK3(X3,k1_tarski(X4)) = X3) | (k1_tarski(X5) = k1_tarski(X4)) | (k1_tarski(X3) = k1_tarski(X4)))))).
% 0.20/0.49  
% 0.20/0.49  tff(u299,axiom,
% 0.20/0.49      (![X3, X2] : (((sK3(sK3(X2,k1_tarski(X3)),k1_tarski(X3)) = X3) | (sK3(X2,k1_tarski(X3)) = X2) | (k1_tarski(X3) = k1_tarski(sK3(X2,k1_tarski(X3)))) | (k1_tarski(X3) = k1_tarski(X2)))))).
% 0.20/0.49  
% 0.20/0.49  tff(u298,axiom,
% 0.20/0.49      (![X1, X0] : (((k1_tarski(X1) = k1_tarski(sK3(X0,k1_tarski(X1)))) | (sK3(X0,k1_tarski(X1)) = X0) | (k1_tarski(X0) = k1_tarski(X1)))))).
% 0.20/0.49  
% 0.20/0.49  tff(u297,negated_conjecture,
% 0.20/0.49      ((~~r2_hidden(sK2,k5_waybel_0(sK0,sK1))) | ~r2_hidden(sK2,k5_waybel_0(sK0,sK1)))).
% 0.20/0.49  
% 0.20/0.49  tff(u296,axiom,
% 0.20/0.49      (![X9, X11, X10] : ((~r2_hidden(X11,k1_tarski(X10)) | (sK3(X9,k1_tarski(X10)) = X11) | (sK3(X9,k1_tarski(X10)) = X9) | (k1_tarski(X9) = k1_tarski(X10)))))).
% 0.20/0.49  
% 0.20/0.49  tff(u295,axiom,
% 0.20/0.49      (![X3, X0] : ((~r2_hidden(X3,k1_tarski(X0)) | (X0 = X3))))).
% 0.20/0.49  
% 0.20/0.49  tff(u294,axiom,
% 0.20/0.49      (![X1, X0] : ((~r2_hidden(X0,X1) | (sK3(X0,X1) != X0) | (k1_tarski(X0) = X1))))).
% 0.20/0.49  
% 0.20/0.49  tff(u293,axiom,
% 0.20/0.49      (![X3] : (r2_hidden(X3,k1_tarski(X3))))).
% 0.20/0.49  
% 0.20/0.49  tff(u292,axiom,
% 0.20/0.49      (![X1, X0] : ((r2_hidden(sK3(X0,X1),X1) | (sK3(X0,X1) = X0) | (k1_tarski(X0) = X1))))).
% 0.20/0.49  
% 0.20/0.49  tff(u291,negated_conjecture,
% 0.20/0.49      ~v2_struct_0(sK0)).
% 0.20/0.49  
% 0.20/0.49  tff(u290,negated_conjecture,
% 0.20/0.49      l1_struct_0(sK0)).
% 0.20/0.49  
% 0.20/0.49  tff(u289,axiom,
% 0.20/0.49      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.20/0.49  
% 0.20/0.49  tff(u288,negated_conjecture,
% 0.20/0.49      ((~~v1_xboole_0(u1_struct_0(sK0))) | ~v1_xboole_0(u1_struct_0(sK0)))).
% 0.20/0.49  
% 0.20/0.49  tff(u287,negated_conjecture,
% 0.20/0.49      ((~v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.20/0.49  
% 0.20/0.49  tff(u286,axiom,
% 0.20/0.49      (![X1, X0] : ((~m1_subset_1(X1,X0) | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | v1_xboole_0(X0))))).
% 0.20/0.49  
% 0.20/0.49  tff(u285,axiom,
% 0.20/0.49      (![X1, X0] : ((~m1_subset_1(X1,X0) | (k6_domain_1(X0,X1) = k1_tarski(X1)) | v1_xboole_0(X0))))).
% 0.20/0.49  
% 0.20/0.49  tff(u284,negated_conjecture,
% 0.20/0.49      ((~~m1_subset_1(k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_tarski(sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) | ~m1_subset_1(k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_tarski(sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))).
% 0.20/0.49  
% 0.20/0.49  tff(u283,negated_conjecture,
% 0.20/0.49      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.20/0.49  
% 0.20/0.49  tff(u282,negated_conjecture,
% 0.20/0.49      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.20/0.49  
% 0.20/0.49  tff(u281,negated_conjecture,
% 0.20/0.49      ((~(k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1))) | (~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.20/0.49  
% 0.20/0.49  tff(u280,negated_conjecture,
% 0.20/0.49      ((~(k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2))) | (~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.20/0.49  
% 0.20/0.49  tff(u279,axiom,
% 0.20/0.49      (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))).
% 0.20/0.49  
% 0.20/0.49  tff(u278,negated_conjecture,
% 0.20/0.49      l1_orders_2(sK0)).
% 0.20/0.49  
% 0.20/0.49  tff(u277,negated_conjecture,
% 0.20/0.49      ((~r1_orders_2(sK0,sK2,sK1)) | r1_orders_2(sK0,sK2,sK1))).
% 0.20/0.49  
% 0.20/0.49  % (8411)# SZS output end Saturation.
% 0.20/0.49  % (8411)------------------------------
% 0.20/0.49  % (8411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (8411)Termination reason: Satisfiable
% 0.20/0.49  
% 0.20/0.49  % (8411)Memory used [KB]: 10618
% 0.20/0.49  % (8411)Time elapsed: 0.100 s
% 0.20/0.49  % (8411)------------------------------
% 0.20/0.49  % (8411)------------------------------
% 0.20/0.49  % (8398)Success in time 0.146 s
%------------------------------------------------------------------------------
