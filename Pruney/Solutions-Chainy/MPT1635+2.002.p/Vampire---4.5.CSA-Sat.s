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
% DateTime   : Thu Dec  3 13:16:56 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   13 (  13 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    0
%              Number of atoms          :   29 (  29 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u56,negated_conjecture,
    ( ~ ( k4_waybel_0(sK0,sK1) != a_2_1_waybel_0(sK0,sK1) )
    | k4_waybel_0(sK0,sK1) != a_2_1_waybel_0(sK0,sK1) )).

tff(u55,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_tarski(X0,X2)
      | r2_hidden(sK2(X0,X1),X2)
      | r1_tarski(X0,X1) ) )).

tff(u54,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) )).

tff(u53,negated_conjecture,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | ! [X1,X0] :
        ( ~ r1_tarski(u1_struct_0(sK0),X1)
        | r2_hidden(sK2(sK1,X0),X1)
        | r1_tarski(sK1,X0) ) )).

tff(u52,negated_conjecture,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | r1_tarski(sK1,u1_struct_0(sK0)) )).

tff(u51,axiom,(
    ! [X0] : r1_tarski(X0,X0) )).

tff(u50,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) )).

tff(u49,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) )).

tff(u48,axiom,(
    ! [X1,X0] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) )).

tff(u47,negated_conjecture,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | ! [X0] :
        ( r2_hidden(sK2(sK1,X0),u1_struct_0(sK0))
        | r1_tarski(sK1,X0) ) )).

tff(u46,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) )).

tff(u45,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u44,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:57:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (16469)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.49  % (16477)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.49  % (16462)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.50  % (16472)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.50  % (16469)# SZS output start Saturation.
% 0.20/0.50  tff(u56,negated_conjecture,
% 0.20/0.50      ((~(k4_waybel_0(sK0,sK1) != a_2_1_waybel_0(sK0,sK1))) | (k4_waybel_0(sK0,sK1) != a_2_1_waybel_0(sK0,sK1)))).
% 0.20/0.50  
% 0.20/0.50  tff(u55,axiom,
% 0.20/0.50      (![X1, X0, X2] : ((~r1_tarski(X0,X2) | r2_hidden(sK2(X0,X1),X2) | r1_tarski(X0,X1))))).
% 0.20/0.50  
% 0.20/0.50  tff(u54,axiom,
% 0.20/0.50      (![X1, X0] : ((~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)))))).
% 0.20/0.50  
% 0.20/0.50  tff(u53,negated_conjecture,
% 0.20/0.50      ((~r1_tarski(sK1,u1_struct_0(sK0))) | (![X1, X0] : ((~r1_tarski(u1_struct_0(sK0),X1) | r2_hidden(sK2(sK1,X0),X1) | r1_tarski(sK1,X0)))))).
% 0.20/0.50  
% 0.20/0.50  tff(u52,negated_conjecture,
% 0.20/0.50      ((~r1_tarski(sK1,u1_struct_0(sK0))) | r1_tarski(sK1,u1_struct_0(sK0)))).
% 0.20/0.50  
% 0.20/0.50  tff(u51,axiom,
% 0.20/0.50      (![X0] : (r1_tarski(X0,X0)))).
% 0.20/0.50  
% 0.20/0.50  tff(u50,axiom,
% 0.20/0.50      (![X1, X0] : ((~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1))))).
% 0.20/0.50  
% 0.20/0.50  tff(u49,axiom,
% 0.20/0.50      (![X1, X0, X2] : ((~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1))))).
% 0.20/0.50  
% 0.20/0.50  tff(u48,axiom,
% 0.20/0.50      (![X1, X0] : ((r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1))))).
% 0.20/0.50  
% 0.20/0.50  tff(u47,negated_conjecture,
% 0.20/0.50      ((~r1_tarski(sK1,u1_struct_0(sK0))) | (![X0] : ((r2_hidden(sK2(sK1,X0),u1_struct_0(sK0)) | r1_tarski(sK1,X0)))))).
% 0.20/0.50  
% 0.20/0.50  tff(u46,axiom,
% 0.20/0.50      (![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1))))).
% 0.20/0.50  
% 0.20/0.50  tff(u45,negated_conjecture,
% 0.20/0.50      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u44,axiom,
% 0.20/0.50      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 0.20/0.50  
% 0.20/0.50  % (16469)# SZS output end Saturation.
% 0.20/0.50  % (16469)------------------------------
% 0.20/0.50  % (16469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (16469)Termination reason: Satisfiable
% 0.20/0.50  
% 0.20/0.50  % (16469)Memory used [KB]: 10618
% 0.20/0.50  % (16469)Time elapsed: 0.082 s
% 0.20/0.50  % (16469)------------------------------
% 0.20/0.50  % (16469)------------------------------
% 0.20/0.50  % (16452)Success in time 0.138 s
%------------------------------------------------------------------------------
