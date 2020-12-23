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
% DateTime   : Thu Dec  3 13:13:17 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   14 (  14 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    0
%              Number of atoms          :   21 (  21 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u60,axiom,(
    ! [X0] :
      ( k5_setfam_1(X0,k1_xboole_0) != X0
      | k1_xboole_0 = X0 ) )).

tff(u59,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) )).

tff(u58,negated_conjecture,(
    k1_xboole_0 = k5_setfam_1(u1_struct_0(sK0),k1_xboole_0) )).

tff(u57,axiom,(
    ! [X0] : k1_xboole_0 = k5_setfam_1(X0,k1_xboole_0) )).

tff(u56,negated_conjecture,(
    k1_xboole_0 = u1_struct_0(sK0) )).

tff(u55,negated_conjecture,(
    k1_xboole_0 = sK1 )).

tff(u54,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k5_setfam_1(X0,X1) = X0
      | ~ m1_setfam_1(X1,X0) ) )).

tff(u53,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k5_setfam_1(X0,X1) = k3_tarski(X1) ) )).

tff(u52,negated_conjecture,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )).

tff(u51,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

tff(u50,axiom,(
    ! [X0] :
      ( ~ m1_setfam_1(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) )).

tff(u49,negated_conjecture,(
    m1_setfam_1(k1_xboole_0,u1_struct_0(sK0)) )).

tff(u48,negated_conjecture,(
    m1_setfam_1(k1_xboole_0,k1_xboole_0) )).

tff(u47,axiom,(
    ! [X1,X0] :
      ( m1_setfam_1(X1,X0)
      | k5_setfam_1(X0,X1) != X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:47:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.42  % (31827)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.42  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.42  % (31827)# SZS output start Saturation.
% 0.21/0.42  tff(u60,axiom,
% 0.21/0.42      (![X0] : (((k5_setfam_1(X0,k1_xboole_0) != X0) | (k1_xboole_0 = X0))))).
% 0.21/0.42  
% 0.21/0.42  tff(u59,axiom,
% 0.21/0.42      (k1_xboole_0 = k3_tarski(k1_xboole_0))).
% 0.21/0.42  
% 0.21/0.42  tff(u58,negated_conjecture,
% 0.21/0.42      (k1_xboole_0 = k5_setfam_1(u1_struct_0(sK0),k1_xboole_0))).
% 0.21/0.42  
% 0.21/0.42  tff(u57,axiom,
% 0.21/0.42      (![X0] : ((k1_xboole_0 = k5_setfam_1(X0,k1_xboole_0))))).
% 0.21/0.42  
% 0.21/0.42  tff(u56,negated_conjecture,
% 0.21/0.42      (k1_xboole_0 = u1_struct_0(sK0))).
% 0.21/0.42  
% 0.21/0.42  tff(u55,negated_conjecture,
% 0.21/0.42      (k1_xboole_0 = sK1)).
% 0.21/0.42  
% 0.21/0.42  tff(u54,axiom,
% 0.21/0.42      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | (k5_setfam_1(X0,X1) = X0) | ~m1_setfam_1(X1,X0))))).
% 0.21/0.42  
% 0.21/0.42  tff(u53,axiom,
% 0.21/0.42      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | (k5_setfam_1(X0,X1) = k3_tarski(X1)))))).
% 0.21/0.42  
% 0.21/0.42  tff(u52,negated_conjecture,
% 0.21/0.42      m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.21/0.42  
% 0.21/0.42  tff(u51,axiom,
% 0.21/0.42      (![X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))))).
% 0.21/0.42  
% 0.21/0.42  tff(u50,axiom,
% 0.21/0.42      (![X0] : ((~m1_setfam_1(k1_xboole_0,X0) | (k1_xboole_0 = X0))))).
% 0.21/0.42  
% 0.21/0.42  tff(u49,negated_conjecture,
% 0.21/0.42      m1_setfam_1(k1_xboole_0,u1_struct_0(sK0))).
% 0.21/0.42  
% 0.21/0.42  tff(u48,negated_conjecture,
% 0.21/0.42      m1_setfam_1(k1_xboole_0,k1_xboole_0)).
% 0.21/0.42  
% 0.21/0.42  tff(u47,axiom,
% 0.21/0.42      (![X1, X0] : ((m1_setfam_1(X1,X0) | (k5_setfam_1(X0,X1) != X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))))).
% 0.21/0.42  
% 0.21/0.42  % (31827)# SZS output end Saturation.
% 0.21/0.42  % (31827)------------------------------
% 0.21/0.42  % (31827)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (31827)Termination reason: Satisfiable
% 0.21/0.42  
% 0.21/0.42  % (31827)Memory used [KB]: 10490
% 0.21/0.42  % (31827)Time elapsed: 0.005 s
% 0.21/0.42  % (31827)------------------------------
% 0.21/0.42  % (31827)------------------------------
% 0.21/0.42  % (31826)Success in time 0.063 s
%------------------------------------------------------------------------------
