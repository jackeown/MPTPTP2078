%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:24 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   12 (  12 expanded)
%              Number of leaves         :   12 (  12 expanded)
%              Depth                    :    0
%              Number of atoms          :   17 (  17 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u51,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) )).

tff(u50,negated_conjecture,(
    r2_hidden(k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)),u1_struct_0(sK1)) )).

tff(u49,negated_conjecture,(
    ~ v1_xboole_0(u1_struct_0(sK1)) )).

tff(u48,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK1)) )).

tff(u47,negated_conjecture,(
    m1_subset_1(sK3,u1_struct_0(sK1)) )).

tff(u46,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) )).

tff(u45,negated_conjecture,(
    m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1))) )).

tff(u44,negated_conjecture,(
    m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK3,sK2),k1_zfmisc_1(u1_struct_0(sK1))) )).

tff(u43,negated_conjecture,(
    m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1))) )).

tff(u42,negated_conjecture,(
    m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK3,sK3),k1_zfmisc_1(u1_struct_0(sK1))) )).

tff(u41,negated_conjecture,
    ( ~ ~ r2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | ~ r2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) )).

tff(u40,negated_conjecture,(
    r2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n013.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 18:47:54 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.42  % (1948)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.43  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.43  % (1948)# SZS output start Saturation.
% 0.21/0.43  tff(u51,axiom,
% 0.21/0.43      (![X1, X0] : ((~r2_hidden(X0,X1) | ~v1_xboole_0(X1))))).
% 0.21/0.43  
% 0.21/0.43  tff(u50,negated_conjecture,
% 0.21/0.43      r2_hidden(k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)),u1_struct_0(sK1))).
% 0.21/0.43  
% 0.21/0.43  tff(u49,negated_conjecture,
% 0.21/0.43      ~v1_xboole_0(u1_struct_0(sK1))).
% 0.21/0.43  
% 0.21/0.43  tff(u48,negated_conjecture,
% 0.21/0.43      m1_subset_1(sK2,u1_struct_0(sK1))).
% 0.21/0.43  
% 0.21/0.43  tff(u47,negated_conjecture,
% 0.21/0.43      m1_subset_1(sK3,u1_struct_0(sK1))).
% 0.21/0.43  
% 0.21/0.43  tff(u46,axiom,
% 0.21/0.43      (![X1, X0, X2] : ((m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))))).
% 0.21/0.43  
% 0.21/0.43  tff(u45,negated_conjecture,
% 0.21/0.43      m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1)))).
% 0.21/0.43  
% 0.21/0.43  tff(u44,negated_conjecture,
% 0.21/0.43      m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK3,sK2),k1_zfmisc_1(u1_struct_0(sK1)))).
% 0.21/0.43  
% 0.21/0.43  tff(u43,negated_conjecture,
% 0.21/0.43      m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))).
% 0.21/0.43  
% 0.21/0.43  tff(u42,negated_conjecture,
% 0.21/0.43      m1_subset_1(k7_domain_1(u1_struct_0(sK1),sK3,sK3),k1_zfmisc_1(u1_struct_0(sK1)))).
% 0.21/0.43  
% 0.21/0.43  tff(u41,negated_conjecture,
% 0.21/0.43      ((~~r2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))) | ~r2_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)))).
% 0.21/0.43  
% 0.21/0.43  tff(u40,negated_conjecture,
% 0.21/0.43      r2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3))).
% 0.21/0.43  
% 0.21/0.43  % (1948)# SZS output end Saturation.
% 0.21/0.43  % (1948)------------------------------
% 0.21/0.43  % (1948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (1948)Termination reason: Satisfiable
% 0.21/0.43  
% 0.21/0.43  % (1948)Memory used [KB]: 6140
% 0.21/0.43  % (1948)Time elapsed: 0.004 s
% 0.21/0.43  % (1948)------------------------------
% 0.21/0.43  % (1948)------------------------------
% 0.21/0.43  % (1950)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.43  % (1945)Success in time 0.071 s
%------------------------------------------------------------------------------
