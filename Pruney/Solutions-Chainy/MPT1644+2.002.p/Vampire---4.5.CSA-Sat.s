%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:04 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   16 (  16 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    0
%              Number of atoms          :   42 (  42 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u58,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_tarski(X0,X2)
      | r2_hidden(sK3(X0,X1),X2)
      | r1_tarski(X0,X1) ) )).

tff(u57,negated_conjecture,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK1),sK1)
    | ! [X1,X0] :
        ( ~ r1_tarski(sK1,X1)
        | r2_hidden(sK3(k4_waybel_0(sK0,sK1),X0),X1)
        | r1_tarski(k4_waybel_0(sK0,sK1),X0) ) )).

tff(u56,negated_conjecture,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK1),sK1)
    | r1_tarski(k4_waybel_0(sK0,sK1),sK1) )).

tff(u55,axiom,(
    ! [X0] : r1_tarski(X0,X0) )).

tff(u54,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) )).

tff(u53,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) )).

tff(u52,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_tarski(X1,X2) ) )).

tff(u51,axiom,(
    ! [X1,X0] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) )).

tff(u50,negated_conjecture,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK1),sK1)
    | ! [X0] :
        ( r2_hidden(sK3(k4_waybel_0(sK0,sK1),X0),sK1)
        | r1_tarski(k4_waybel_0(sK0,sK1),X0) ) )).

tff(u49,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r1_tarski(X1,X2) ) )).

tff(u48,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(sK2(X0,X1,X2),X0)
      | r1_tarski(X1,X2) ) )).

tff(u47,negated_conjecture,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2(u1_struct_0(sK0),sK1,X0),sK1)
      | r1_tarski(sK1,X0) ) )).

tff(u46,negated_conjecture,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK2(u1_struct_0(sK0),sK1,X0),u1_struct_0(sK0))
      | r1_tarski(sK1,X0) ) )).

tff(u45,negated_conjecture,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u44,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u43,negated_conjecture,
    ( ~ ~ v13_waybel_0(sK1,sK0)
    | ~ v13_waybel_0(sK1,sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:28:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.44  % (16437)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.44  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.46  % (16437)# SZS output start Saturation.
% 0.21/0.46  tff(u58,axiom,
% 0.21/0.46      (![X1, X0, X2] : ((~r1_tarski(X0,X2) | r2_hidden(sK3(X0,X1),X2) | r1_tarski(X0,X1))))).
% 0.21/0.46  
% 0.21/0.46  tff(u57,negated_conjecture,
% 0.21/0.46      ((~r1_tarski(k4_waybel_0(sK0,sK1),sK1)) | (![X1, X0] : ((~r1_tarski(sK1,X1) | r2_hidden(sK3(k4_waybel_0(sK0,sK1),X0),X1) | r1_tarski(k4_waybel_0(sK0,sK1),X0)))))).
% 0.21/0.46  
% 0.21/0.46  tff(u56,negated_conjecture,
% 0.21/0.46      ((~r1_tarski(k4_waybel_0(sK0,sK1),sK1)) | r1_tarski(k4_waybel_0(sK0,sK1),sK1))).
% 0.21/0.46  
% 0.21/0.46  tff(u55,axiom,
% 0.21/0.46      (![X0] : (r1_tarski(X0,X0)))).
% 0.21/0.46  
% 0.21/0.46  tff(u54,axiom,
% 0.21/0.46      (![X1, X0] : ((~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1))))).
% 0.21/0.46  
% 0.21/0.46  tff(u53,axiom,
% 0.21/0.46      (![X1, X0, X2] : ((~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1))))).
% 0.21/0.46  
% 0.21/0.46  tff(u52,axiom,
% 0.21/0.46      (![X1, X0, X2] : ((~r2_hidden(sK2(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X2))))).
% 0.21/0.46  
% 0.21/0.46  tff(u51,axiom,
% 0.21/0.46      (![X1, X0] : ((r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1))))).
% 0.21/0.46  
% 0.21/0.46  tff(u50,negated_conjecture,
% 0.21/0.46      ((~r1_tarski(k4_waybel_0(sK0,sK1),sK1)) | (![X0] : ((r2_hidden(sK3(k4_waybel_0(sK0,sK1),X0),sK1) | r1_tarski(k4_waybel_0(sK0,sK1),X0)))))).
% 0.21/0.46  
% 0.21/0.46  tff(u49,axiom,
% 0.21/0.46      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r2_hidden(sK2(X0,X1,X2),X1) | r1_tarski(X1,X2))))).
% 0.21/0.46  
% 0.21/0.46  tff(u48,axiom,
% 0.21/0.46      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(sK2(X0,X1,X2),X0) | r1_tarski(X1,X2))))).
% 0.21/0.46  
% 0.21/0.46  tff(u47,negated_conjecture,
% 0.21/0.46      (![X0] : ((~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK2(u1_struct_0(sK0),sK1,X0),sK1) | r1_tarski(sK1,X0))))).
% 0.21/0.46  
% 0.21/0.46  tff(u46,negated_conjecture,
% 0.21/0.46      (![X0] : ((~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK2(u1_struct_0(sK0),sK1,X0),u1_struct_0(sK0)) | r1_tarski(sK1,X0))))).
% 0.21/0.46  
% 0.21/0.46  tff(u45,negated_conjecture,
% 0.21/0.46      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.46  
% 0.21/0.46  tff(u44,negated_conjecture,
% 0.21/0.46      l1_orders_2(sK0)).
% 0.21/0.46  
% 0.21/0.46  tff(u43,negated_conjecture,
% 0.21/0.46      ((~~v13_waybel_0(sK1,sK0)) | ~v13_waybel_0(sK1,sK0))).
% 0.21/0.46  
% 0.21/0.46  % (16437)# SZS output end Saturation.
% 0.21/0.46  % (16437)------------------------------
% 0.21/0.46  % (16437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (16437)Termination reason: Satisfiable
% 0.21/0.46  
% 0.21/0.46  % (16437)Memory used [KB]: 5373
% 0.21/0.46  % (16437)Time elapsed: 0.038 s
% 0.21/0.46  % (16437)------------------------------
% 0.21/0.46  % (16437)------------------------------
% 0.21/0.46  % (16430)Success in time 0.1 s
%------------------------------------------------------------------------------
