%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:33 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   26 (  26 expanded)
%              Number of leaves         :   26 (  26 expanded)
%              Depth                    :    0
%              Number of atoms          :   29 (  29 expanded)
%              Number of equality atoms :   20 (  20 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u129,negated_conjecture,(
    sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

tff(u128,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 )).

tff(u127,axiom,(
    ! [X0] : k3_subset_1(X0,k3_subset_1(X0,X0)) = X0 )).

tff(u126,axiom,(
    ! [X0] : k6_subset_1(X0,k3_subset_1(X0,X0)) = X0 )).

tff(u125,negated_conjecture,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) )).

tff(u124,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k3_subset_1(X1,k3_subset_1(X1,k6_subset_1(X1,X2))) )).

tff(u123,axiom,(
    ! [X0] : k3_subset_1(X0,X0) = k6_subset_1(X0,X0) )).

tff(u122,axiom,(
    ! [X1,X2] : k3_subset_1(X1,k6_subset_1(X1,X2)) = k6_subset_1(X1,k6_subset_1(X1,X2)) )).

tff(u121,negated_conjecture,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k6_subset_1(u1_struct_0(sK0),sK1) )).

tff(u120,axiom,(
    ! [X3,X2] : k6_subset_1(X2,X3) = k6_subset_1(X2,k3_subset_1(X2,k6_subset_1(X2,X3))) )).

tff(u119,negated_conjecture,(
    ! [X11] : k7_subset_1(u1_struct_0(sK0),sK1,X11) = k6_subset_1(sK1,X11) )).

tff(u118,axiom,(
    ! [X9,X8,X10] : k7_subset_1(X8,k6_subset_1(X8,X9),X10) = k6_subset_1(k6_subset_1(X8,X9),X10) )).

tff(u117,axiom,(
    ! [X3,X2] : k7_subset_1(X2,k3_subset_1(X2,X2),X3) = k6_subset_1(k3_subset_1(X2,X2),X3) )).

tff(u116,negated_conjecture,(
    ! [X7] : k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X7) = k6_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),X7) )).

tff(u115,axiom,(
    ! [X5,X4,X6] : k7_subset_1(X4,k3_subset_1(X4,k6_subset_1(X4,X5)),X6) = k6_subset_1(k3_subset_1(X4,k6_subset_1(X4,X5)),X6) )).

tff(u114,negated_conjecture,(
    sK1 = k6_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) )).

tff(u113,axiom,(
    ! [X1,X0] : k6_subset_1(X0,X1) = k7_subset_1(X0,X0,X1) )).

tff(u112,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2) ) )).

tff(u111,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k6_subset_1(X0,X1) ) )).

tff(u110,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) )).

tff(u109,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

tff(u108,axiom,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,X0),k1_zfmisc_1(X0)) )).

tff(u107,axiom,(
    ! [X3,X2] : m1_subset_1(k3_subset_1(X2,k6_subset_1(X2,X3)),k1_zfmisc_1(X2)) )).

tff(u106,negated_conjecture,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u105,axiom,(
    ! [X1,X0] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) )).

tff(u104,negated_conjecture,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:26:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (10392)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.49  % (10392)# SZS output start Saturation.
% 0.21/0.49  tff(u129,negated_conjecture,
% 0.21/0.49      (sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 0.21/0.49  
% 0.21/0.49  tff(u128,axiom,
% 0.21/0.49      (![X0] : ((k2_subset_1(X0) = X0)))).
% 0.21/0.49  
% 0.21/0.49  tff(u127,axiom,
% 0.21/0.49      (![X0] : ((k3_subset_1(X0,k3_subset_1(X0,X0)) = X0)))).
% 0.21/0.49  
% 0.21/0.49  tff(u126,axiom,
% 0.21/0.49      (![X0] : ((k6_subset_1(X0,k3_subset_1(X0,X0)) = X0)))).
% 0.21/0.49  
% 0.21/0.49  tff(u125,negated_conjecture,
% 0.21/0.49      (sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))).
% 0.21/0.49  
% 0.21/0.49  tff(u124,axiom,
% 0.21/0.49      (![X1, X2] : ((k6_subset_1(X1,X2) = k3_subset_1(X1,k3_subset_1(X1,k6_subset_1(X1,X2))))))).
% 0.21/0.49  
% 0.21/0.49  tff(u123,axiom,
% 0.21/0.49      (![X0] : ((k3_subset_1(X0,X0) = k6_subset_1(X0,X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u122,axiom,
% 0.21/0.49      (![X1, X2] : ((k3_subset_1(X1,k6_subset_1(X1,X2)) = k6_subset_1(X1,k6_subset_1(X1,X2)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u121,negated_conjecture,
% 0.21/0.49      (k3_subset_1(u1_struct_0(sK0),sK1) = k6_subset_1(u1_struct_0(sK0),sK1))).
% 0.21/0.49  
% 0.21/0.49  tff(u120,axiom,
% 0.21/0.49      (![X3, X2] : ((k6_subset_1(X2,X3) = k6_subset_1(X2,k3_subset_1(X2,k6_subset_1(X2,X3))))))).
% 0.21/0.49  
% 0.21/0.49  tff(u119,negated_conjecture,
% 0.21/0.49      (![X11] : ((k7_subset_1(u1_struct_0(sK0),sK1,X11) = k6_subset_1(sK1,X11))))).
% 0.21/0.49  
% 0.21/0.49  tff(u118,axiom,
% 0.21/0.49      (![X9, X8, X10] : ((k7_subset_1(X8,k6_subset_1(X8,X9),X10) = k6_subset_1(k6_subset_1(X8,X9),X10))))).
% 0.21/0.49  
% 0.21/0.49  tff(u117,axiom,
% 0.21/0.49      (![X3, X2] : ((k7_subset_1(X2,k3_subset_1(X2,X2),X3) = k6_subset_1(k3_subset_1(X2,X2),X3))))).
% 0.21/0.49  
% 0.21/0.49  tff(u116,negated_conjecture,
% 0.21/0.49      (![X7] : ((k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X7) = k6_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),X7))))).
% 0.21/0.49  
% 0.21/0.49  tff(u115,axiom,
% 0.21/0.49      (![X5, X4, X6] : ((k7_subset_1(X4,k3_subset_1(X4,k6_subset_1(X4,X5)),X6) = k6_subset_1(k3_subset_1(X4,k6_subset_1(X4,X5)),X6))))).
% 0.21/0.49  
% 0.21/0.49  tff(u114,negated_conjecture,
% 0.21/0.49      (sK1 = k6_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))).
% 0.21/0.49  
% 0.21/0.49  tff(u113,axiom,
% 0.21/0.49      (![X1, X0] : ((k6_subset_1(X0,X1) = k7_subset_1(X0,X0,X1))))).
% 0.21/0.49  
% 0.21/0.49  tff(u112,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u111,axiom,
% 0.21/0.49      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k3_subset_1(X0,X1) = k6_subset_1(X0,X1)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u110,axiom,
% 0.21/0.49      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1))))).
% 0.21/0.49  
% 0.21/0.49  tff(u109,axiom,
% 0.21/0.49      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u108,axiom,
% 0.21/0.49      (![X0] : (m1_subset_1(k3_subset_1(X0,X0),k1_zfmisc_1(X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u107,axiom,
% 0.21/0.49      (![X3, X2] : (m1_subset_1(k3_subset_1(X2,k6_subset_1(X2,X3)),k1_zfmisc_1(X2))))).
% 0.21/0.49  
% 0.21/0.49  tff(u106,negated_conjecture,
% 0.21/0.49      m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.49  
% 0.21/0.49  tff(u105,axiom,
% 0.21/0.49      (![X1, X0] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u104,negated_conjecture,
% 0.21/0.49      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.49  
% 0.21/0.49  % (10392)# SZS output end Saturation.
% 0.21/0.49  % (10392)------------------------------
% 0.21/0.49  % (10392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (10392)Termination reason: Satisfiable
% 0.21/0.49  
% 0.21/0.49  % (10392)Memory used [KB]: 10618
% 0.21/0.49  % (10392)Time elapsed: 0.054 s
% 0.21/0.49  % (10392)------------------------------
% 0.21/0.49  % (10392)------------------------------
% 0.21/0.50  % (10382)Success in time 0.132 s
%------------------------------------------------------------------------------
