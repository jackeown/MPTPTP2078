%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:24 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :    9 (   9 expanded)
%              Number of leaves         :    9 (   9 expanded)
%              Depth                    :    0
%              Number of atoms          :   26 (  26 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u77,negated_conjecture,
    ( ~ ( k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) != k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) )
    | k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) != k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) )).

tff(u76,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_xboole_0(u1_struct_0(sK1)) )).

tff(u75,axiom,
    ( ~ ! [X1,X0] :
          ( ~ r2_hidden(X1,X0)
          | ~ v1_xboole_0(X0) )
    | ! [X1,X0] :
        ( ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) )).

tff(u74,negated_conjecture,
    ( ~ r2_hidden(k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)),u1_struct_0(sK1))
    | r2_hidden(k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)),u1_struct_0(sK1)) )).

tff(u73,negated_conjecture,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | m1_subset_1(sK3,u1_struct_0(sK1)) )).

tff(u72,negated_conjecture,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | m1_subset_1(sK2,u1_struct_0(sK1)) )).

tff(u71,axiom,
    ( ~ ! [X1,X0,X2] :
          ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
          | ~ m1_subset_1(X2,X0)
          | ~ m1_subset_1(X1,X0)
          | v1_xboole_0(X0) )
    | ! [X1,X0,X2] :
        ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,X0)
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) ) )).

tff(u70,negated_conjecture,
    ( ~ ~ r1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | ~ r1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) )).

tff(u69,negated_conjecture,
    ( ~ r1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | r1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:30:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.40  % (25001)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.40  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.40  % (25001)# SZS output start Saturation.
% 0.21/0.40  tff(u77,negated_conjecture,
% 0.21/0.40      ((~(k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) != k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)))) | (k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) != k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))))).
% 0.21/0.40  
% 0.21/0.40  tff(u76,negated_conjecture,
% 0.21/0.40      ((~~v1_xboole_0(u1_struct_0(sK1))) | ~v1_xboole_0(u1_struct_0(sK1)))).
% 0.21/0.40  
% 0.21/0.40  tff(u75,axiom,
% 0.21/0.40      ((~(![X1, X0] : ((~r2_hidden(X1,X0) | ~v1_xboole_0(X0))))) | (![X1, X0] : ((~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))))).
% 0.21/0.40  
% 0.21/0.40  tff(u74,negated_conjecture,
% 0.21/0.40      ((~r2_hidden(k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)),u1_struct_0(sK1))) | r2_hidden(k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)),u1_struct_0(sK1)))).
% 0.21/0.40  
% 0.21/0.40  tff(u73,negated_conjecture,
% 0.21/0.40      ((~m1_subset_1(sK3,u1_struct_0(sK1))) | m1_subset_1(sK3,u1_struct_0(sK1)))).
% 0.21/0.40  
% 0.21/0.40  tff(u72,negated_conjecture,
% 0.21/0.40      ((~m1_subset_1(sK2,u1_struct_0(sK1))) | m1_subset_1(sK2,u1_struct_0(sK1)))).
% 0.21/0.40  
% 0.21/0.40  tff(u71,axiom,
% 0.21/0.40      ((~(![X1, X0, X2] : ((m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))))) | (![X1, X0, X2] : ((m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)))))).
% 0.21/0.40  
% 0.21/0.40  tff(u70,negated_conjecture,
% 0.21/0.40      ((~~r1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))) | ~r1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)))).
% 0.21/0.40  
% 0.21/0.40  tff(u69,negated_conjecture,
% 0.21/0.40      ((~r1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3))) | r1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)))).
% 0.21/0.40  
% 0.21/0.40  % (25001)# SZS output end Saturation.
% 0.21/0.40  % (25001)------------------------------
% 0.21/0.40  % (25001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.40  % (25001)Termination reason: Satisfiable
% 0.21/0.40  
% 0.21/0.40  % (25001)Memory used [KB]: 6012
% 0.21/0.40  % (25001)Time elapsed: 0.003 s
% 0.21/0.40  % (25001)------------------------------
% 0.21/0.40  % (25001)------------------------------
% 0.21/0.40  % (24987)Success in time 0.048 s
%------------------------------------------------------------------------------
