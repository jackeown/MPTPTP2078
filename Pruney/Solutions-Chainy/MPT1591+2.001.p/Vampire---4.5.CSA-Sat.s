%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:25 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 (  55 expanded)
%              Number of leaves         :   55 (  55 expanded)
%              Depth                    :    0
%              Number of atoms          :  133 ( 133 expanded)
%              Number of equality atoms :   31 (  31 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u302,negated_conjecture,(
    k12_lattice3(sK1,sK2,sK3) != k12_lattice3(sK0,sK2,sK3) )).

tff(u301,axiom,(
    ! [X1,X0] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) )).

tff(u300,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | k2_tarski(sK3,sK3) = k7_domain_1(u1_struct_0(sK0),sK3,sK3) )).

tff(u299,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | k2_tarski(sK2,sK3) = k7_domain_1(u1_struct_0(sK0),sK2,sK3) )).

tff(u298,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | k7_domain_1(u1_struct_0(sK0),sK3,sK2) = k2_tarski(sK3,sK2) )).

tff(u297,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | k7_domain_1(u1_struct_0(sK0),sK2,sK2) = k2_tarski(sK2,sK2) )).

tff(u296,negated_conjecture,(
    sK2 = sK4 )).

tff(u295,negated_conjecture,(
    sK3 = sK5 )).

tff(u294,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0)) )).

tff(u293,axiom,(
    ! [X1,X0,X2] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) ) )).

tff(u292,axiom,(
    ! [X1,X0] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) )).

tff(u291,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) )).

tff(u290,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ! [X1] :
        ( ~ m1_subset_1(u1_struct_0(sK0),X1)
        | ~ v1_xboole_0(X1) ) )).

tff(u289,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ! [X3,X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k7_domain_1(u1_struct_0(sK0),X3,X2) = k2_tarski(X3,X2) ) )).

tff(u288,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_tarski(X0,sK3) = k7_domain_1(u1_struct_0(sK0),X0,sK3) ) )).

tff(u287,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k7_domain_1(u1_struct_0(sK0),X1,sK2) = k2_tarski(X1,sK2) ) )).

tff(u286,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_tarski(sK3,X0) = k7_domain_1(u1_struct_0(sK0),sK3,X0) ) )).

tff(u285,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k7_domain_1(u1_struct_0(sK0),sK2,X1) = k2_tarski(sK2,X1) ) )).

tff(u284,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_tarski(X0,X0) = k7_domain_1(u1_struct_0(sK0),X0,X0) ) )).

tff(u283,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK1)) )).

tff(u282,negated_conjecture,(
    m1_subset_1(sK3,u1_struct_0(sK1)) )).

tff(u281,negated_conjecture,(
    m1_subset_1(sK3,u1_struct_0(sK0)) )).

tff(u280,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u279,axiom,(
    ! [X1,X0] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) )).

tff(u278,axiom,(
    ! [X1,X0] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) )).

tff(u277,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) )).

tff(u276,negated_conjecture,
    ( ~ m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u275,negated_conjecture,
    ( ~ m1_subset_1(k2_tarski(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tarski(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u274,negated_conjecture,
    ( ~ m1_subset_1(k2_tarski(sK3,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tarski(sK3,sK2),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u273,negated_conjecture,
    ( ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u272,negated_conjecture,
    ( ~ ! [X3,X2] :
          ( ~ m1_subset_1(X2,u1_struct_0(sK0))
          | ~ r2_hidden(X3,u1_struct_0(sK0))
          | k2_tarski(X2,X3) = k7_domain_1(u1_struct_0(sK0),X2,X3) )
    | ! [X3,X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X3,u1_struct_0(sK0))
        | k2_tarski(X2,X3) = k7_domain_1(u1_struct_0(sK0),X2,X3) ) )).

tff(u271,negated_conjecture,
    ( ~ ! [X3,X2] :
          ( ~ m1_subset_1(X2,u1_struct_0(sK0))
          | ~ r2_hidden(X3,u1_struct_0(sK0))
          | k7_domain_1(u1_struct_0(sK0),X3,X2) = k2_tarski(X3,X2) )
    | ! [X3,X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X3,u1_struct_0(sK0))
        | k7_domain_1(u1_struct_0(sK0),X3,X2) = k2_tarski(X3,X2) ) )).

tff(u270,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ r2_hidden(X0,u1_struct_0(sK0))
          | k2_tarski(X0,sK3) = k7_domain_1(u1_struct_0(sK0),X0,sK3) )
    | ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK0))
        | k2_tarski(X0,sK3) = k7_domain_1(u1_struct_0(sK0),X0,sK3) ) )).

tff(u269,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ r2_hidden(X0,u1_struct_0(sK0))
          | k2_tarski(X0,sK2) = k7_domain_1(u1_struct_0(sK0),X0,sK2) )
    | ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK0))
        | k2_tarski(X0,sK2) = k7_domain_1(u1_struct_0(sK0),X0,sK2) ) )).

tff(u268,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ r2_hidden(X0,u1_struct_0(sK0))
          | k2_tarski(sK3,X0) = k7_domain_1(u1_struct_0(sK0),sK3,X0) )
    | ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK0))
        | k2_tarski(sK3,X0) = k7_domain_1(u1_struct_0(sK0),sK3,X0) ) )).

tff(u267,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ r2_hidden(X0,u1_struct_0(sK0))
          | k2_tarski(sK2,X0) = k7_domain_1(u1_struct_0(sK0),sK2,X0) )
    | ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK0))
        | k2_tarski(sK2,X0) = k7_domain_1(u1_struct_0(sK0),sK2,X0) ) )).

tff(u266,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ r2_hidden(X0,u1_struct_0(sK0))
          | k2_tarski(X0,X0) = k7_domain_1(u1_struct_0(sK0),X0,X0) )
    | ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK0))
        | k2_tarski(X0,X0) = k7_domain_1(u1_struct_0(sK0),X0,X0) ) )).

tff(u265,negated_conjecture,
    ( ~ ! [X3,X2] :
          ( ~ r2_hidden(X2,u1_struct_0(sK0))
          | ~ r2_hidden(X3,u1_struct_0(sK0))
          | k7_domain_1(u1_struct_0(sK0),X3,X2) = k2_tarski(X3,X2) )
    | ! [X3,X2] :
        ( ~ r2_hidden(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X3,u1_struct_0(sK0))
        | k7_domain_1(u1_struct_0(sK0),X3,X2) = k2_tarski(X3,X2) ) )).

tff(u264,axiom,(
    ! [X1,X0] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) )).

tff(u263,negated_conjecture,(
    ~ v2_struct_0(sK1) )).

tff(u262,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v2_struct_0(sK0) )).

tff(u261,axiom,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) )).

tff(u260,negated_conjecture,
    ( ~ ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK1) )).

tff(u259,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) )).

tff(u258,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | l1_struct_0(sK0) )).

tff(u257,negated_conjecture,
    ( ~ ~ l1_struct_0(sK1)
    | ~ l1_orders_2(sK1) )).

tff(u256,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u255,axiom,(
    ! [X0] :
      ( ~ v2_lattice3(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) )).

tff(u254,negated_conjecture,(
    v2_lattice3(sK0) )).

tff(u253,negated_conjecture,(
    v3_orders_2(sK0) )).

tff(u252,negated_conjecture,(
    v4_orders_2(sK0) )).

tff(u251,negated_conjecture,(
    v5_orders_2(sK0) )).

tff(u250,negated_conjecture,(
    v4_yellow_0(sK1,sK0) )).

tff(u249,negated_conjecture,(
    v5_yellow_0(sK1,sK0) )).

tff(u248,negated_conjecture,(
    m1_yellow_0(sK1,sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:27:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (1148)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (1144)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (1147)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (1152)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (1145)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (1145)Refutation not found, incomplete strategy% (1145)------------------------------
% 0.21/0.48  % (1145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (1155)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (1144)Refutation not found, incomplete strategy% (1144)------------------------------
% 0.21/0.48  % (1144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (1144)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (1144)Memory used [KB]: 1663
% 0.21/0.48  % (1144)Time elapsed: 0.061 s
% 0.21/0.48  % (1144)------------------------------
% 0.21/0.48  % (1144)------------------------------
% 0.21/0.48  % (1153)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (1145)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (1145)Memory used [KB]: 6140
% 0.21/0.48  % (1145)Time elapsed: 0.061 s
% 0.21/0.48  % (1145)------------------------------
% 0.21/0.48  % (1145)------------------------------
% 0.21/0.48  % (1143)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (1152)Refutation not found, incomplete strategy% (1152)------------------------------
% 0.21/0.48  % (1152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (1152)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (1152)Memory used [KB]: 10874
% 0.21/0.48  % (1152)Time elapsed: 0.067 s
% 0.21/0.48  % (1152)------------------------------
% 0.21/0.48  % (1152)------------------------------
% 0.21/0.49  % (1151)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (1142)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (1157)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (1140)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.50  % (1157)# SZS output start Saturation.
% 0.21/0.50  tff(u302,negated_conjecture,
% 0.21/0.50      (k12_lattice3(sK1,sK2,sK3) != k12_lattice3(sK0,sK2,sK3))).
% 0.21/0.50  
% 0.21/0.50  tff(u301,axiom,
% 0.21/0.50      (![X1, X0] : ((k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1))))).
% 0.21/0.50  
% 0.21/0.50  tff(u300,negated_conjecture,
% 0.21/0.50      ((~~v1_xboole_0(u1_struct_0(sK0))) | (k2_tarski(sK3,sK3) = k7_domain_1(u1_struct_0(sK0),sK3,sK3)))).
% 0.21/0.50  
% 0.21/0.50  tff(u299,negated_conjecture,
% 0.21/0.50      ((~~v1_xboole_0(u1_struct_0(sK0))) | (k2_tarski(sK2,sK3) = k7_domain_1(u1_struct_0(sK0),sK2,sK3)))).
% 0.21/0.50  
% 0.21/0.50  tff(u298,negated_conjecture,
% 0.21/0.50      ((~~v1_xboole_0(u1_struct_0(sK0))) | (k7_domain_1(u1_struct_0(sK0),sK3,sK2) = k2_tarski(sK3,sK2)))).
% 0.21/0.50  
% 0.21/0.50  tff(u297,negated_conjecture,
% 0.21/0.50      ((~~v1_xboole_0(u1_struct_0(sK0))) | (k7_domain_1(u1_struct_0(sK0),sK2,sK2) = k2_tarski(sK2,sK2)))).
% 0.21/0.50  
% 0.21/0.50  tff(u296,negated_conjecture,
% 0.21/0.50      (sK2 = sK4)).
% 0.21/0.50  
% 0.21/0.50  tff(u295,negated_conjecture,
% 0.21/0.50      (sK3 = sK5)).
% 0.21/0.50  
% 0.21/0.50  tff(u294,negated_conjecture,
% 0.21/0.50      ((~~v1_xboole_0(u1_struct_0(sK0))) | ~v1_xboole_0(u1_struct_0(sK0)))).
% 0.21/0.50  
% 0.21/0.50  tff(u293,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((v1_xboole_0(X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | (k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)))))).
% 0.21/0.50  
% 0.21/0.50  tff(u292,axiom,
% 0.21/0.50      (![X1, X0] : ((v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u291,negated_conjecture,
% 0.21/0.50      ((~v1_xboole_0(u1_struct_0(sK1))) | v1_xboole_0(u1_struct_0(sK1)))).
% 0.21/0.50  
% 0.21/0.50  tff(u290,negated_conjecture,
% 0.21/0.50      ((~~v1_xboole_0(u1_struct_0(sK0))) | (![X1] : ((~m1_subset_1(u1_struct_0(sK0),X1) | ~v1_xboole_0(X1)))))).
% 0.21/0.50  
% 0.21/0.50  tff(u289,negated_conjecture,
% 0.21/0.50      ((~~v1_xboole_0(u1_struct_0(sK0))) | (![X3, X2] : ((~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | (k7_domain_1(u1_struct_0(sK0),X3,X2) = k2_tarski(X3,X2))))))).
% 0.21/0.50  
% 0.21/0.50  tff(u288,negated_conjecture,
% 0.21/0.50      ((~~v1_xboole_0(u1_struct_0(sK0))) | (![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k2_tarski(X0,sK3) = k7_domain_1(u1_struct_0(sK0),X0,sK3))))))).
% 0.21/0.50  
% 0.21/0.50  tff(u287,negated_conjecture,
% 0.21/0.50      ((~~v1_xboole_0(u1_struct_0(sK0))) | (![X1] : ((~m1_subset_1(X1,u1_struct_0(sK0)) | (k7_domain_1(u1_struct_0(sK0),X1,sK2) = k2_tarski(X1,sK2))))))).
% 0.21/0.50  
% 0.21/0.50  tff(u286,negated_conjecture,
% 0.21/0.50      ((~~v1_xboole_0(u1_struct_0(sK0))) | (![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k2_tarski(sK3,X0) = k7_domain_1(u1_struct_0(sK0),sK3,X0))))))).
% 0.21/0.50  
% 0.21/0.50  tff(u285,negated_conjecture,
% 0.21/0.50      ((~~v1_xboole_0(u1_struct_0(sK0))) | (![X1] : ((~m1_subset_1(X1,u1_struct_0(sK0)) | (k7_domain_1(u1_struct_0(sK0),sK2,X1) = k2_tarski(sK2,X1))))))).
% 0.21/0.50  
% 0.21/0.50  tff(u284,negated_conjecture,
% 0.21/0.50      ((~~v1_xboole_0(u1_struct_0(sK0))) | (![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k2_tarski(X0,X0) = k7_domain_1(u1_struct_0(sK0),X0,X0))))))).
% 0.21/0.50  
% 0.21/0.50  tff(u283,negated_conjecture,
% 0.21/0.50      m1_subset_1(sK2,u1_struct_0(sK1))).
% 0.21/0.50  
% 0.21/0.50  tff(u282,negated_conjecture,
% 0.21/0.50      m1_subset_1(sK3,u1_struct_0(sK1))).
% 0.21/0.50  
% 0.21/0.50  tff(u281,negated_conjecture,
% 0.21/0.50      m1_subset_1(sK3,u1_struct_0(sK0))).
% 0.21/0.50  
% 0.21/0.50  tff(u280,negated_conjecture,
% 0.21/0.50      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.21/0.50  
% 0.21/0.50  tff(u279,axiom,
% 0.21/0.50      (![X1, X0] : ((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u278,axiom,
% 0.21/0.50      (![X1, X0] : ((m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u277,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u276,negated_conjecture,
% 0.21/0.50      ((~m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u275,negated_conjecture,
% 0.21/0.50      ((~m1_subset_1(k2_tarski(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(k2_tarski(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u274,negated_conjecture,
% 0.21/0.50      ((~m1_subset_1(k2_tarski(sK3,sK2),k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(k2_tarski(sK3,sK2),k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u273,negated_conjecture,
% 0.21/0.50      ((~m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u272,negated_conjecture,
% 0.21/0.50      ((~(![X3, X2] : ((~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X3,u1_struct_0(sK0)) | (k2_tarski(X2,X3) = k7_domain_1(u1_struct_0(sK0),X2,X3)))))) | (![X3, X2] : ((~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X3,u1_struct_0(sK0)) | (k2_tarski(X2,X3) = k7_domain_1(u1_struct_0(sK0),X2,X3))))))).
% 0.21/0.50  
% 0.21/0.50  tff(u271,negated_conjecture,
% 0.21/0.50      ((~(![X3, X2] : ((~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X3,u1_struct_0(sK0)) | (k7_domain_1(u1_struct_0(sK0),X3,X2) = k2_tarski(X3,X2)))))) | (![X3, X2] : ((~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X3,u1_struct_0(sK0)) | (k7_domain_1(u1_struct_0(sK0),X3,X2) = k2_tarski(X3,X2))))))).
% 0.21/0.50  
% 0.21/0.50  tff(u270,negated_conjecture,
% 0.21/0.50      ((~(![X0] : ((~r2_hidden(X0,u1_struct_0(sK0)) | (k2_tarski(X0,sK3) = k7_domain_1(u1_struct_0(sK0),X0,sK3)))))) | (![X0] : ((~r2_hidden(X0,u1_struct_0(sK0)) | (k2_tarski(X0,sK3) = k7_domain_1(u1_struct_0(sK0),X0,sK3))))))).
% 0.21/0.50  
% 0.21/0.50  tff(u269,negated_conjecture,
% 0.21/0.50      ((~(![X0] : ((~r2_hidden(X0,u1_struct_0(sK0)) | (k2_tarski(X0,sK2) = k7_domain_1(u1_struct_0(sK0),X0,sK2)))))) | (![X0] : ((~r2_hidden(X0,u1_struct_0(sK0)) | (k2_tarski(X0,sK2) = k7_domain_1(u1_struct_0(sK0),X0,sK2))))))).
% 0.21/0.50  
% 0.21/0.50  tff(u268,negated_conjecture,
% 0.21/0.50      ((~(![X0] : ((~r2_hidden(X0,u1_struct_0(sK0)) | (k2_tarski(sK3,X0) = k7_domain_1(u1_struct_0(sK0),sK3,X0)))))) | (![X0] : ((~r2_hidden(X0,u1_struct_0(sK0)) | (k2_tarski(sK3,X0) = k7_domain_1(u1_struct_0(sK0),sK3,X0))))))).
% 0.21/0.50  
% 0.21/0.50  tff(u267,negated_conjecture,
% 0.21/0.50      ((~(![X0] : ((~r2_hidden(X0,u1_struct_0(sK0)) | (k2_tarski(sK2,X0) = k7_domain_1(u1_struct_0(sK0),sK2,X0)))))) | (![X0] : ((~r2_hidden(X0,u1_struct_0(sK0)) | (k2_tarski(sK2,X0) = k7_domain_1(u1_struct_0(sK0),sK2,X0))))))).
% 0.21/0.50  
% 0.21/0.50  tff(u266,negated_conjecture,
% 0.21/0.50      ((~(![X0] : ((~r2_hidden(X0,u1_struct_0(sK0)) | (k2_tarski(X0,X0) = k7_domain_1(u1_struct_0(sK0),X0,X0)))))) | (![X0] : ((~r2_hidden(X0,u1_struct_0(sK0)) | (k2_tarski(X0,X0) = k7_domain_1(u1_struct_0(sK0),X0,X0))))))).
% 0.21/0.50  
% 0.21/0.50  tff(u265,negated_conjecture,
% 0.21/0.50      ((~(![X3, X2] : ((~r2_hidden(X2,u1_struct_0(sK0)) | ~r2_hidden(X3,u1_struct_0(sK0)) | (k7_domain_1(u1_struct_0(sK0),X3,X2) = k2_tarski(X3,X2)))))) | (![X3, X2] : ((~r2_hidden(X2,u1_struct_0(sK0)) | ~r2_hidden(X3,u1_struct_0(sK0)) | (k7_domain_1(u1_struct_0(sK0),X3,X2) = k2_tarski(X3,X2))))))).
% 0.21/0.50  
% 0.21/0.50  tff(u264,axiom,
% 0.21/0.50      (![X1, X0] : ((r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u263,negated_conjecture,
% 0.21/0.50      ~v2_struct_0(sK1)).
% 0.21/0.50  
% 0.21/0.50  tff(u262,negated_conjecture,
% 0.21/0.50      ((~~v2_struct_0(sK0)) | ~v2_struct_0(sK0))).
% 0.21/0.50  
% 0.21/0.50  tff(u261,axiom,
% 0.21/0.50      (![X0] : ((v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0)))))).
% 0.21/0.50  
% 0.21/0.50  tff(u260,negated_conjecture,
% 0.21/0.50      ((~~l1_struct_0(sK1)) | ~l1_struct_0(sK1))).
% 0.21/0.50  
% 0.21/0.50  tff(u259,axiom,
% 0.21/0.50      (![X0] : ((l1_struct_0(X0) | ~l1_orders_2(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u258,negated_conjecture,
% 0.21/0.50      ((~l1_struct_0(sK0)) | l1_struct_0(sK0))).
% 0.21/0.50  
% 0.21/0.50  tff(u257,negated_conjecture,
% 0.21/0.50      ((~~l1_struct_0(sK1)) | ~l1_orders_2(sK1))).
% 0.21/0.50  
% 0.21/0.50  tff(u256,negated_conjecture,
% 0.21/0.50      l1_orders_2(sK0)).
% 0.21/0.50  
% 0.21/0.50  tff(u255,axiom,
% 0.21/0.50      (![X0] : ((~v2_lattice3(X0) | ~v2_struct_0(X0) | ~l1_orders_2(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u254,negated_conjecture,
% 0.21/0.50      v2_lattice3(sK0)).
% 0.21/0.50  
% 0.21/0.50  tff(u253,negated_conjecture,
% 0.21/0.50      v3_orders_2(sK0)).
% 0.21/0.50  
% 0.21/0.50  tff(u252,negated_conjecture,
% 0.21/0.50      v4_orders_2(sK0)).
% 0.21/0.50  
% 0.21/0.50  tff(u251,negated_conjecture,
% 0.21/0.50      v5_orders_2(sK0)).
% 0.21/0.50  
% 0.21/0.50  tff(u250,negated_conjecture,
% 0.21/0.50      v4_yellow_0(sK1,sK0)).
% 0.21/0.50  
% 0.21/0.50  tff(u249,negated_conjecture,
% 0.21/0.50      v5_yellow_0(sK1,sK0)).
% 0.21/0.50  
% 0.21/0.50  tff(u248,negated_conjecture,
% 0.21/0.50      m1_yellow_0(sK1,sK0)).
% 0.21/0.50  
% 0.21/0.50  % (1157)# SZS output end Saturation.
% 0.21/0.50  % (1157)------------------------------
% 0.21/0.50  % (1157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (1157)Termination reason: Satisfiable
% 0.21/0.50  
% 0.21/0.50  % (1157)Memory used [KB]: 6268
% 0.21/0.50  % (1157)Time elapsed: 0.086 s
% 0.21/0.50  % (1157)------------------------------
% 0.21/0.50  % (1157)------------------------------
% 0.21/0.50  % (1139)Success in time 0.136 s
%------------------------------------------------------------------------------
