%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:17 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   17 (  17 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    0
%              Number of atoms          :   53 (  53 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u62,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u61,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u60,negated_conjecture,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r2_hidden(X4,sK2)
      | k1_yellow_0(sK0,sK3(X4)) = X4 ) )).

tff(u59,negated_conjecture,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r2_hidden(X4,sK2)
      | v1_finset_1(sK3(X4)) ) )).

tff(u58,negated_conjecture,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(sK1))
      | ~ v1_finset_1(X6)
      | k1_xboole_0 = X6
      | r1_yellow_0(sK0,X6) ) )).

tff(u57,negated_conjecture,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u56,negated_conjecture,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u55,negated_conjecture,(
    ! [X4] :
      ( m1_subset_1(sK3(X4),k1_zfmisc_1(sK1))
      | ~ r2_hidden(X4,sK2)
      | ~ m1_subset_1(X4,u1_struct_0(sK0)) ) )).

tff(u54,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ r1_yellow_0(X0,X1)
      | r1_yellow_0(X0,X2) ) )).

tff(u53,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_lattice3(X0,X2,sK4(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,sK4(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ r1_yellow_0(X0,X1)
      | r1_yellow_0(X0,X2) ) )).

tff(u52,axiom,(
    ! [X1,X0,X2] :
      ( r2_lattice3(X0,X2,sK4(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | r2_lattice3(X0,X1,sK4(X0,X1,X2))
      | ~ r1_yellow_0(X0,X1)
      | r1_yellow_0(X0,X2) ) )).

tff(u51,negated_conjecture,
    ( ~ ~ r1_yellow_0(sK0,sK1)
    | ~ r1_yellow_0(sK0,sK1) )).

tff(u50,negated_conjecture,
    ( ~ r1_yellow_0(sK0,sK2)
    | r1_yellow_0(sK0,sK2) )).

tff(u49,negated_conjecture,(
    ! [X4] :
      ( r1_yellow_0(sK0,sK3(X4))
      | ~ r2_hidden(X4,sK2)
      | ~ m1_subset_1(X4,u1_struct_0(sK0)) ) )).

tff(u48,negated_conjecture,(
    ! [X3,X2] :
      ( v1_finset_1(sK3(sK4(sK0,X2,X3)))
      | r1_yellow_0(sK0,X3)
      | ~ r2_hidden(sK4(sK0,X2,X3),sK2)
      | ~ r1_yellow_0(sK0,X2) ) )).

tff(u47,negated_conjecture,(
    ! [X1,X0] :
      ( ~ r2_hidden(sK4(sK0,X0,X1),sK2)
      | r1_yellow_0(sK0,X1)
      | ~ r1_yellow_0(sK0,X0)
      | sK4(sK0,X0,X1) = k1_yellow_0(sK0,sK3(sK4(sK0,X0,X1))) ) )).

tff(u46,negated_conjecture,(
    ! [X3] :
      ( r2_hidden(k1_yellow_0(sK0,X3),sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
      | k1_xboole_0 = X3
      | ~ v1_finset_1(X3) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:30:37 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.44  % (9353)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.46  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.47  % (9353)# SZS output start Saturation.
% 0.20/0.47  tff(u62,negated_conjecture,
% 0.20/0.47      ~v2_struct_0(sK0)).
% 0.20/0.47  
% 0.20/0.47  tff(u61,negated_conjecture,
% 0.20/0.47      l1_orders_2(sK0)).
% 0.20/0.47  
% 0.20/0.47  tff(u60,negated_conjecture,
% 0.20/0.47      (![X4] : ((~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_hidden(X4,sK2) | (k1_yellow_0(sK0,sK3(X4)) = X4))))).
% 0.20/0.47  
% 0.20/0.47  tff(u59,negated_conjecture,
% 0.20/0.47      (![X4] : ((~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_hidden(X4,sK2) | v1_finset_1(sK3(X4)))))).
% 0.20/0.47  
% 0.20/0.47  tff(u58,negated_conjecture,
% 0.20/0.47      (![X6] : ((~m1_subset_1(X6,k1_zfmisc_1(sK1)) | ~v1_finset_1(X6) | (k1_xboole_0 = X6) | r1_yellow_0(sK0,X6))))).
% 0.20/0.47  
% 0.20/0.47  tff(u57,negated_conjecture,
% 0.20/0.47      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.47  
% 0.20/0.47  tff(u56,negated_conjecture,
% 0.20/0.47      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.47  
% 0.20/0.47  tff(u55,negated_conjecture,
% 0.20/0.47      (![X4] : ((m1_subset_1(sK3(X4),k1_zfmisc_1(sK1)) | ~r2_hidden(X4,sK2) | ~m1_subset_1(X4,u1_struct_0(sK0)))))).
% 0.20/0.47  
% 0.20/0.47  tff(u54,axiom,
% 0.20/0.47      (![X1, X0, X2] : ((m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0) | ~r1_yellow_0(X0,X1) | r1_yellow_0(X0,X2))))).
% 0.20/0.47  
% 0.20/0.47  tff(u53,axiom,
% 0.20/0.47      (![X1, X0, X2] : ((~r2_lattice3(X0,X2,sK4(X0,X1,X2)) | ~r2_lattice3(X0,X1,sK4(X0,X1,X2)) | ~l1_orders_2(X0) | v2_struct_0(X0) | ~r1_yellow_0(X0,X1) | r1_yellow_0(X0,X2))))).
% 0.20/0.47  
% 0.20/0.47  tff(u52,axiom,
% 0.20/0.47      (![X1, X0, X2] : ((r2_lattice3(X0,X2,sK4(X0,X1,X2)) | ~l1_orders_2(X0) | v2_struct_0(X0) | r2_lattice3(X0,X1,sK4(X0,X1,X2)) | ~r1_yellow_0(X0,X1) | r1_yellow_0(X0,X2))))).
% 0.20/0.47  
% 0.20/0.47  tff(u51,negated_conjecture,
% 0.20/0.47      ((~~r1_yellow_0(sK0,sK1)) | ~r1_yellow_0(sK0,sK1))).
% 0.20/0.47  
% 0.20/0.47  tff(u50,negated_conjecture,
% 0.20/0.47      ((~r1_yellow_0(sK0,sK2)) | r1_yellow_0(sK0,sK2))).
% 0.20/0.47  
% 0.20/0.47  tff(u49,negated_conjecture,
% 0.20/0.47      (![X4] : ((r1_yellow_0(sK0,sK3(X4)) | ~r2_hidden(X4,sK2) | ~m1_subset_1(X4,u1_struct_0(sK0)))))).
% 0.20/0.47  
% 0.20/0.47  tff(u48,negated_conjecture,
% 0.20/0.47      (![X3, X2] : ((v1_finset_1(sK3(sK4(sK0,X2,X3))) | r1_yellow_0(sK0,X3) | ~r2_hidden(sK4(sK0,X2,X3),sK2) | ~r1_yellow_0(sK0,X2))))).
% 0.20/0.47  
% 0.20/0.47  tff(u47,negated_conjecture,
% 0.20/0.47      (![X1, X0] : ((~r2_hidden(sK4(sK0,X0,X1),sK2) | r1_yellow_0(sK0,X1) | ~r1_yellow_0(sK0,X0) | (sK4(sK0,X0,X1) = k1_yellow_0(sK0,sK3(sK4(sK0,X0,X1)))))))).
% 0.20/0.47  
% 0.20/0.47  tff(u46,negated_conjecture,
% 0.20/0.47      (![X3] : ((r2_hidden(k1_yellow_0(sK0,X3),sK2) | ~m1_subset_1(X3,k1_zfmisc_1(sK1)) | (k1_xboole_0 = X3) | ~v1_finset_1(X3))))).
% 0.20/0.47  
% 0.20/0.47  % (9353)# SZS output end Saturation.
% 0.20/0.47  % (9353)------------------------------
% 0.20/0.47  % (9353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (9353)Termination reason: Satisfiable
% 0.20/0.47  
% 0.20/0.47  % (9353)Memory used [KB]: 10618
% 0.20/0.47  % (9353)Time elapsed: 0.064 s
% 0.20/0.47  % (9353)------------------------------
% 0.20/0.47  % (9353)------------------------------
% 0.20/0.47  % (9340)Success in time 0.113 s
%------------------------------------------------------------------------------
