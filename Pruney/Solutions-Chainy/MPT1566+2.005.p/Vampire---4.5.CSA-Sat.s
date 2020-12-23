%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:17 EST 2020

% Result     : CounterSatisfiable 0.84s
% Output     : Saturation 0.84s
% Verified   : 
% Statistics : Number of clauses        :    6 (   6 expanded)
%              Number of leaves         :    6 (   6 expanded)
%              Depth                    :    0
%              Number of atoms          :    6 (   6 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u6,negated_conjecture,
    ( ~ r1_orders_2(sK0,k3_yellow_0(sK0),sK1) )).

cnf(u5,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u10,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u9,negated_conjecture,
    ( v1_yellow_0(sK0) )).

cnf(u8,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u7,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:35:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (1209401344)
% 0.14/0.38  ipcrm: permission denied for id (1212678145)
% 0.14/0.38  ipcrm: permission denied for id (1209434114)
% 0.14/0.38  ipcrm: permission denied for id (1209466883)
% 0.14/0.38  ipcrm: permission denied for id (1209532422)
% 0.14/0.38  ipcrm: permission denied for id (1209565191)
% 0.14/0.39  ipcrm: permission denied for id (1209663499)
% 0.14/0.39  ipcrm: permission denied for id (1212973070)
% 0.14/0.39  ipcrm: permission denied for id (1209761807)
% 0.14/0.39  ipcrm: permission denied for id (1213005840)
% 0.14/0.40  ipcrm: permission denied for id (1209892882)
% 0.14/0.40  ipcrm: permission denied for id (1209925651)
% 0.14/0.40  ipcrm: permission denied for id (1213071380)
% 0.14/0.40  ipcrm: permission denied for id (1213202456)
% 0.14/0.40  ipcrm: permission denied for id (1213235225)
% 0.14/0.41  ipcrm: permission denied for id (1210089500)
% 0.14/0.41  ipcrm: permission denied for id (1213366302)
% 0.14/0.41  ipcrm: permission denied for id (1213399071)
% 0.14/0.41  ipcrm: permission denied for id (1210155040)
% 0.14/0.42  ipcrm: permission denied for id (1213464610)
% 0.14/0.42  ipcrm: permission denied for id (1210220579)
% 0.14/0.42  ipcrm: permission denied for id (1210253348)
% 0.14/0.42  ipcrm: permission denied for id (1210286118)
% 0.14/0.42  ipcrm: permission denied for id (1213530151)
% 0.23/0.42  ipcrm: permission denied for id (1213562920)
% 0.23/0.42  ipcrm: permission denied for id (1213595689)
% 0.23/0.43  ipcrm: permission denied for id (1213628458)
% 0.23/0.43  ipcrm: permission denied for id (1210417195)
% 0.23/0.43  ipcrm: permission denied for id (1213661228)
% 0.23/0.43  ipcrm: permission denied for id (1210515502)
% 0.23/0.43  ipcrm: permission denied for id (1210548271)
% 0.23/0.44  ipcrm: permission denied for id (1213792306)
% 0.23/0.44  ipcrm: permission denied for id (1210679347)
% 0.23/0.44  ipcrm: permission denied for id (1213825076)
% 0.23/0.44  ipcrm: permission denied for id (1210744885)
% 0.23/0.44  ipcrm: permission denied for id (1210777654)
% 0.23/0.44  ipcrm: permission denied for id (1210810423)
% 0.23/0.44  ipcrm: permission denied for id (1210843192)
% 0.23/0.44  ipcrm: permission denied for id (1213857849)
% 0.23/0.45  ipcrm: permission denied for id (1211072575)
% 0.23/0.45  ipcrm: permission denied for id (1214087232)
% 0.23/0.45  ipcrm: permission denied for id (1211138113)
% 0.23/0.46  ipcrm: permission denied for id (1211170882)
% 0.23/0.46  ipcrm: permission denied for id (1211269188)
% 0.23/0.46  ipcrm: permission denied for id (1214185541)
% 0.23/0.46  ipcrm: permission denied for id (1211301958)
% 0.23/0.46  ipcrm: permission denied for id (1211334727)
% 0.23/0.46  ipcrm: permission denied for id (1211367496)
% 0.23/0.47  ipcrm: permission denied for id (1214218313)
% 0.23/0.47  ipcrm: permission denied for id (1214251082)
% 0.23/0.47  ipcrm: permission denied for id (1211465803)
% 0.23/0.47  ipcrm: permission denied for id (1211498572)
% 0.23/0.47  ipcrm: permission denied for id (1211531341)
% 0.23/0.47  ipcrm: permission denied for id (1211564110)
% 0.23/0.47  ipcrm: permission denied for id (1211596879)
% 0.23/0.47  ipcrm: permission denied for id (1211629648)
% 0.23/0.48  ipcrm: permission denied for id (1211662417)
% 0.23/0.48  ipcrm: permission denied for id (1214283858)
% 0.23/0.48  ipcrm: permission denied for id (1211695187)
% 0.23/0.48  ipcrm: permission denied for id (1211727956)
% 0.23/0.48  ipcrm: permission denied for id (1211760726)
% 0.23/0.48  ipcrm: permission denied for id (1211826264)
% 0.23/0.49  ipcrm: permission denied for id (1214382169)
% 0.23/0.49  ipcrm: permission denied for id (1211859034)
% 0.23/0.49  ipcrm: permission denied for id (1214414939)
% 0.23/0.49  ipcrm: permission denied for id (1211891804)
% 0.23/0.49  ipcrm: permission denied for id (1211957342)
% 0.23/0.50  ipcrm: permission denied for id (1214513248)
% 0.23/0.50  ipcrm: permission denied for id (1214546017)
% 0.23/0.50  ipcrm: permission denied for id (1214677093)
% 0.23/0.50  ipcrm: permission denied for id (1214709862)
% 0.23/0.51  ipcrm: permission denied for id (1214775400)
% 0.23/0.51  ipcrm: permission denied for id (1214808169)
% 0.23/0.51  ipcrm: permission denied for id (1212088426)
% 0.23/0.51  ipcrm: permission denied for id (1212121195)
% 0.23/0.51  ipcrm: permission denied for id (1212153964)
% 0.23/0.51  ipcrm: permission denied for id (1214840941)
% 0.23/0.51  ipcrm: permission denied for id (1214873710)
% 0.23/0.52  ipcrm: permission denied for id (1212219503)
% 0.23/0.52  ipcrm: permission denied for id (1215004785)
% 0.23/0.52  ipcrm: permission denied for id (1212317810)
% 0.23/0.52  ipcrm: permission denied for id (1212350579)
% 0.23/0.52  ipcrm: permission denied for id (1215037557)
% 0.23/0.52  ipcrm: permission denied for id (1212416118)
% 0.23/0.53  ipcrm: permission denied for id (1212448887)
% 0.23/0.53  ipcrm: permission denied for id (1215070328)
% 0.23/0.53  ipcrm: permission denied for id (1212514426)
% 0.23/0.53  ipcrm: permission denied for id (1212547195)
% 0.23/0.53  ipcrm: permission denied for id (1215168637)
% 0.23/0.53  ipcrm: permission denied for id (1212612734)
% 0.23/0.54  ipcrm: permission denied for id (1215201407)
% 0.84/0.64  % (20448)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.84/0.64  % (20445)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.84/0.65  % SZS status CounterSatisfiable for theBenchmark
% 0.84/0.65  % (20445)# SZS output start Saturation.
% 0.84/0.65  cnf(u6,negated_conjecture,
% 0.84/0.65      ~r1_orders_2(sK0,k3_yellow_0(sK0),sK1)).
% 0.84/0.65  
% 0.84/0.65  cnf(u5,negated_conjecture,
% 0.84/0.65      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.84/0.65  
% 0.84/0.65  cnf(u10,negated_conjecture,
% 0.84/0.65      l1_orders_2(sK0)).
% 0.84/0.65  
% 0.84/0.65  cnf(u9,negated_conjecture,
% 0.84/0.65      v1_yellow_0(sK0)).
% 0.84/0.65  
% 0.84/0.65  cnf(u8,negated_conjecture,
% 0.84/0.65      v5_orders_2(sK0)).
% 0.84/0.65  
% 0.84/0.65  cnf(u7,negated_conjecture,
% 0.84/0.65      ~v2_struct_0(sK0)).
% 0.84/0.65  
% 0.84/0.65  % (20445)# SZS output end Saturation.
% 0.84/0.65  % (20445)------------------------------
% 0.84/0.65  % (20445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.84/0.65  % (20445)Termination reason: Satisfiable
% 0.84/0.65  
% 0.84/0.65  % (20445)Memory used [KB]: 767
% 0.84/0.65  % (20445)Time elapsed: 0.004 s
% 0.84/0.65  % (20445)------------------------------
% 0.84/0.65  % (20445)------------------------------
% 0.84/0.65  % (20259)Success in time 0.281 s
%------------------------------------------------------------------------------
