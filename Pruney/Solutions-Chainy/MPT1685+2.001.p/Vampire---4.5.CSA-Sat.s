%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:19 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   75 (  75 expanded)
%              Number of leaves         :   75 (  75 expanded)
%              Depth                    :    0
%              Number of atoms          :  148 ( 148 expanded)
%              Number of equality atoms :   47 (  47 expanded)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u56,negated_conjecture,
    ( r3_waybel_0(sK0,sK1,sK4,sK6)
    | r4_waybel_0(sK0,sK1,sK4,sK6) )).

cnf(u78,negated_conjecture,
    ( r3_waybel_0(sK0,sK1,sK4,sK6)
    | ~ r4_waybel_0(sK2,sK3,sK5,sK6) )).

cnf(u241,negated_conjecture,
    ( ~ r3_waybel_0(sK2,sK3,sK4,sK6)
    | r4_waybel_0(sK0,sK1,sK4,sK6) )).

cnf(u242,negated_conjecture,
    ( ~ r3_waybel_0(sK2,sK3,sK4,sK6)
    | ~ r4_waybel_0(sK2,sK3,sK4,sK6) )).

cnf(u79,negated_conjecture,
    ( ~ r3_waybel_0(sK2,sK3,sK5,sK6)
    | r4_waybel_0(sK0,sK1,sK4,sK6) )).

cnf(u81,negated_conjecture,
    ( ~ r3_waybel_0(sK2,sK3,sK5,sK6)
    | ~ r4_waybel_0(sK2,sK3,sK5,sK6) )).

cnf(u72,axiom,
    ( r1_funct_2(X0,X1,X2,X3,X5,X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_2(X5,X2,X3)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(X5,X0,X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X1) )).

cnf(u248,negated_conjecture,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4) )).

cnf(u119,negated_conjecture,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK5) )).

cnf(u91,negated_conjecture,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK3),sK4,sK5) )).

cnf(u52,negated_conjecture,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5) )).

cnf(u117,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1)) )).

cnf(u94,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK3)) )).

cnf(u50,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) )).

cnf(u47,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) )).

cnf(u49,negated_conjecture,
    ( v1_funct_1(sK5) )).

cnf(u46,negated_conjecture,
    ( v1_funct_1(sK4) )).

cnf(u69,axiom,
    ( ~ v1_funct_1(X4)
    | ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_2(X5,X2,X3)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(X4,X0,X1)
    | X4 = X5
    | v1_xboole_0(X3)
    | v1_xboole_0(X1) )).

cnf(u220,negated_conjecture,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X1,X2,sK4,X0)
    | sK4 = X0
    | v1_xboole_0(X2) )).

cnf(u63,axiom,
    ( ~ r2_yellow_0(X0,X2)
    | r2_yellow_0(X1,X2)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X0) )).

cnf(u65,axiom,
    ( ~ r2_yellow_0(X0,X2)
    | k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X0) )).

cnf(u62,axiom,
    ( ~ r1_yellow_0(X0,X2)
    | r1_yellow_0(X1,X2)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X0) )).

cnf(u64,axiom,
    ( ~ r1_yellow_0(X0,X2)
    | k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X0) )).

cnf(u181,negated_conjecture,
    ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) )).

cnf(u120,negated_conjecture,
    ( m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) )).

cnf(u167,negated_conjecture,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

cnf(u98,negated_conjecture,
    ( m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

cnf(u61,axiom,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) )).

cnf(u118,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) )).

cnf(u93,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3)))) )).

cnf(u51,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) )).

cnf(u48,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) )).

cnf(u77,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2))) )).

cnf(u53,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u216,negated_conjecture,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_2(X4,X2,X3)
    | ~ v1_funct_1(X4)
    | ~ r1_funct_2(X0,X1,X2,X3,sK4,X4)
    | ~ v1_funct_2(sK4,X0,X1)
    | sK4 = X4
    | v1_xboole_0(X3)
    | v1_xboole_0(X1) )).

cnf(u67,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
    | X0 = X2 )).

cnf(u68,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
    | X1 = X3 )).

cnf(u43,negated_conjecture,
    ( l1_orders_2(sK3) )).

cnf(u41,negated_conjecture,
    ( l1_orders_2(sK2) )).

cnf(u39,negated_conjecture,
    ( l1_orders_2(sK1) )).

cnf(u37,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u60,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u82,axiom,
    ( ~ l1_orders_2(X0)
    | u1_struct_0(X0) = X1
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2) )).

cnf(u144,axiom,
    ( ~ l1_orders_2(X0)
    | u1_orders_2(X0) = X2
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2) )).

cnf(u122,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(sK1)) )).

cnf(u100,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(sK0)) )).

cnf(u66,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u76,negated_conjecture,
    ( l1_struct_0(sK3) )).

cnf(u75,negated_conjecture,
    ( l1_struct_0(sK2) )).

cnf(u74,negated_conjecture,
    ( l1_struct_0(sK1) )).

cnf(u73,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u42,negated_conjecture,
    ( ~ v2_struct_0(sK3) )).

cnf(u40,negated_conjecture,
    ( ~ v2_struct_0(sK2) )).

cnf(u38,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

cnf(u36,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u55,negated_conjecture,
    ( sK6 = sK7 )).

cnf(u229,negated_conjecture,
    ( sK4 = sK5 )).

cnf(u108,negated_conjecture,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK3)) )).

cnf(u45,negated_conjecture,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) )).

cnf(u92,negated_conjecture,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK2)) )).

cnf(u44,negated_conjecture,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) )).

cnf(u177,negated_conjecture,
    ( u1_orders_2(sK1) = u1_orders_2(sK3) )).

cnf(u164,negated_conjecture,
    ( u1_orders_2(sK0) = u1_orders_2(sK2) )).

cnf(u106,negated_conjecture,
    ( u1_struct_0(sK1) = u1_struct_0(sK3) )).

cnf(u90,negated_conjecture,
    ( u1_struct_0(sK0) = u1_struct_0(sK2) )).

cnf(u129,negated_conjecture,
    ( g1_orders_2(X6,X7) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK3))
    | u1_struct_0(sK1) = X6 )).

cnf(u146,negated_conjecture,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK3)) != g1_orders_2(X5,X6)
    | u1_orders_2(sK3) = X6 )).

cnf(u84,negated_conjecture,
    ( g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    | u1_struct_0(sK1) = X2 )).

cnf(u155,negated_conjecture,
    ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    | u1_orders_2(sK3) = X1 )).

cnf(u179,negated_conjecture,
    ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    | u1_orders_2(sK1) = X1 )).

cnf(u127,negated_conjecture,
    ( g1_orders_2(X4,X5) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK2))
    | u1_struct_0(sK0) = X4 )).

cnf(u145,negated_conjecture,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK2)) != g1_orders_2(X3,X4)
    | u1_orders_2(sK2) = X4 )).

cnf(u83,negated_conjecture,
    ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | u1_struct_0(sK0) = X0 )).

cnf(u147,negated_conjecture,
    ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | u1_orders_2(sK2) = X1 )).

cnf(u165,negated_conjecture,
    ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | u1_orders_2(sK0) = X1 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:16:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (9857)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.46  % (9848)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.48  % (9857)# SZS output start Saturation.
% 0.21/0.48  cnf(u56,negated_conjecture,
% 0.21/0.48      r3_waybel_0(sK0,sK1,sK4,sK6) | r4_waybel_0(sK0,sK1,sK4,sK6)).
% 0.21/0.48  
% 0.21/0.48  cnf(u78,negated_conjecture,
% 0.21/0.48      r3_waybel_0(sK0,sK1,sK4,sK6) | ~r4_waybel_0(sK2,sK3,sK5,sK6)).
% 0.21/0.48  
% 0.21/0.48  cnf(u241,negated_conjecture,
% 0.21/0.48      ~r3_waybel_0(sK2,sK3,sK4,sK6) | r4_waybel_0(sK0,sK1,sK4,sK6)).
% 0.21/0.48  
% 0.21/0.48  cnf(u242,negated_conjecture,
% 0.21/0.48      ~r3_waybel_0(sK2,sK3,sK4,sK6) | ~r4_waybel_0(sK2,sK3,sK4,sK6)).
% 0.21/0.48  
% 0.21/0.48  cnf(u79,negated_conjecture,
% 0.21/0.48      ~r3_waybel_0(sK2,sK3,sK5,sK6) | r4_waybel_0(sK0,sK1,sK4,sK6)).
% 0.21/0.48  
% 0.21/0.48  cnf(u81,negated_conjecture,
% 0.21/0.48      ~r3_waybel_0(sK2,sK3,sK5,sK6) | ~r4_waybel_0(sK2,sK3,sK5,sK6)).
% 0.21/0.48  
% 0.21/0.48  cnf(u72,axiom,
% 0.21/0.48      r1_funct_2(X0,X1,X2,X3,X5,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | v1_xboole_0(X3) | v1_xboole_0(X1)).
% 0.21/0.48  
% 0.21/0.48  cnf(u248,negated_conjecture,
% 0.21/0.48      r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)).
% 0.21/0.48  
% 0.21/0.48  cnf(u119,negated_conjecture,
% 0.21/0.48      r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK5)).
% 0.21/0.48  
% 0.21/0.48  cnf(u91,negated_conjecture,
% 0.21/0.48      r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK3),sK4,sK5)).
% 0.21/0.48  
% 0.21/0.48  cnf(u52,negated_conjecture,
% 0.21/0.48      r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5)).
% 0.21/0.48  
% 0.21/0.48  cnf(u117,negated_conjecture,
% 0.21/0.48      v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))).
% 0.21/0.48  
% 0.21/0.48  cnf(u94,negated_conjecture,
% 0.21/0.48      v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK3))).
% 0.21/0.48  
% 0.21/0.48  cnf(u50,negated_conjecture,
% 0.21/0.48      v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))).
% 0.21/0.48  
% 0.21/0.48  cnf(u47,negated_conjecture,
% 0.21/0.48      v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))).
% 0.21/0.48  
% 0.21/0.48  cnf(u49,negated_conjecture,
% 0.21/0.48      v1_funct_1(sK5)).
% 0.21/0.48  
% 0.21/0.48  cnf(u46,negated_conjecture,
% 0.21/0.48      v1_funct_1(sK4)).
% 0.21/0.48  
% 0.21/0.48  cnf(u69,axiom,
% 0.21/0.48      ~v1_funct_1(X4) | ~r1_funct_2(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | X4 = X5 | v1_xboole_0(X3) | v1_xboole_0(X1)).
% 0.21/0.48  
% 0.21/0.48  cnf(u220,negated_conjecture,
% 0.21/0.48      ~v1_funct_1(X0) | ~v1_funct_2(X0,X1,X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X1,X2,sK4,X0) | sK4 = X0 | v1_xboole_0(X2)).
% 0.21/0.48  
% 0.21/0.48  cnf(u63,axiom,
% 0.21/0.48      ~r2_yellow_0(X0,X2) | r2_yellow_0(X1,X2) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) | ~l1_orders_2(X1) | ~l1_orders_2(X0)).
% 0.21/0.48  
% 0.21/0.48  cnf(u65,axiom,
% 0.21/0.48      ~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) | ~l1_orders_2(X1) | ~l1_orders_2(X0)).
% 0.21/0.48  
% 0.21/0.48  cnf(u62,axiom,
% 0.21/0.48      ~r1_yellow_0(X0,X2) | r1_yellow_0(X1,X2) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) | ~l1_orders_2(X1) | ~l1_orders_2(X0)).
% 0.21/0.48  
% 0.21/0.48  cnf(u64,axiom,
% 0.21/0.48      ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) | ~l1_orders_2(X1) | ~l1_orders_2(X0)).
% 0.21/0.48  
% 0.21/0.48  cnf(u181,negated_conjecture,
% 0.21/0.48      m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))).
% 0.21/0.48  
% 0.21/0.48  cnf(u120,negated_conjecture,
% 0.21/0.48      m1_subset_1(u1_orders_2(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))).
% 0.21/0.48  
% 0.21/0.48  cnf(u167,negated_conjecture,
% 0.21/0.48      m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 0.21/0.48  
% 0.21/0.48  cnf(u98,negated_conjecture,
% 0.21/0.48      m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 0.21/0.48  
% 0.21/0.48  cnf(u61,axiom,
% 0.21/0.48      m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)).
% 0.21/0.48  
% 0.21/0.48  cnf(u118,negated_conjecture,
% 0.21/0.48      m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))).
% 0.21/0.48  
% 0.21/0.48  cnf(u93,negated_conjecture,
% 0.21/0.48      m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3))))).
% 0.21/0.48  
% 0.21/0.48  cnf(u51,negated_conjecture,
% 0.21/0.48      m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))).
% 0.21/0.48  
% 0.21/0.48  cnf(u48,negated_conjecture,
% 0.21/0.48      m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))).
% 0.21/0.48  
% 0.21/0.48  cnf(u77,negated_conjecture,
% 0.21/0.48      m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK2)))).
% 0.21/0.48  
% 0.21/0.48  cnf(u53,negated_conjecture,
% 0.21/0.48      m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.48  
% 0.21/0.48  cnf(u216,negated_conjecture,
% 0.21/0.48      ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X4,X2,X3) | ~v1_funct_1(X4) | ~r1_funct_2(X0,X1,X2,X3,sK4,X4) | ~v1_funct_2(sK4,X0,X1) | sK4 = X4 | v1_xboole_0(X3) | v1_xboole_0(X1)).
% 0.21/0.48  
% 0.21/0.48  cnf(u67,axiom,
% 0.21/0.48      ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X0 = X2).
% 0.21/0.48  
% 0.21/0.48  cnf(u68,axiom,
% 0.21/0.48      ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X1 = X3).
% 0.21/0.48  
% 0.21/0.48  cnf(u43,negated_conjecture,
% 0.21/0.48      l1_orders_2(sK3)).
% 0.21/0.48  
% 0.21/0.48  cnf(u41,negated_conjecture,
% 0.21/0.48      l1_orders_2(sK2)).
% 0.21/0.48  
% 0.21/0.48  cnf(u39,negated_conjecture,
% 0.21/0.48      l1_orders_2(sK1)).
% 0.21/0.48  
% 0.21/0.48  cnf(u37,negated_conjecture,
% 0.21/0.48      l1_orders_2(sK0)).
% 0.21/0.48  
% 0.21/0.48  cnf(u60,axiom,
% 0.21/0.48      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.21/0.48  
% 0.21/0.48  cnf(u82,axiom,
% 0.21/0.48      ~l1_orders_2(X0) | u1_struct_0(X0) = X1 | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)).
% 0.21/0.48  
% 0.21/0.48  cnf(u144,axiom,
% 0.21/0.48      ~l1_orders_2(X0) | u1_orders_2(X0) = X2 | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)).
% 0.21/0.48  
% 0.21/0.48  cnf(u122,negated_conjecture,
% 0.21/0.48      ~v1_xboole_0(u1_struct_0(sK1))).
% 0.21/0.48  
% 0.21/0.48  cnf(u100,negated_conjecture,
% 0.21/0.48      ~v1_xboole_0(u1_struct_0(sK0))).
% 0.21/0.48  
% 0.21/0.48  cnf(u66,axiom,
% 0.21/0.48      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.21/0.48  
% 0.21/0.48  cnf(u76,negated_conjecture,
% 0.21/0.48      l1_struct_0(sK3)).
% 0.21/0.48  
% 0.21/0.48  cnf(u75,negated_conjecture,
% 0.21/0.48      l1_struct_0(sK2)).
% 0.21/0.48  
% 0.21/0.48  cnf(u74,negated_conjecture,
% 0.21/0.48      l1_struct_0(sK1)).
% 0.21/0.48  
% 0.21/0.48  cnf(u73,negated_conjecture,
% 0.21/0.48      l1_struct_0(sK0)).
% 0.21/0.48  
% 0.21/0.48  cnf(u42,negated_conjecture,
% 0.21/0.48      ~v2_struct_0(sK3)).
% 0.21/0.48  
% 0.21/0.48  cnf(u40,negated_conjecture,
% 0.21/0.48      ~v2_struct_0(sK2)).
% 0.21/0.48  
% 0.21/0.48  cnf(u38,negated_conjecture,
% 0.21/0.48      ~v2_struct_0(sK1)).
% 0.21/0.48  
% 0.21/0.48  cnf(u36,negated_conjecture,
% 0.21/0.48      ~v2_struct_0(sK0)).
% 0.21/0.48  
% 0.21/0.48  cnf(u55,negated_conjecture,
% 0.21/0.48      sK6 = sK7).
% 0.21/0.48  
% 0.21/0.48  cnf(u229,negated_conjecture,
% 0.21/0.48      sK4 = sK5).
% 0.21/0.48  
% 0.21/0.48  cnf(u108,negated_conjecture,
% 0.21/0.48      g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK3))).
% 0.21/0.48  
% 0.21/0.48  cnf(u45,negated_conjecture,
% 0.21/0.48      g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))).
% 0.21/0.48  
% 0.21/0.48  cnf(u92,negated_conjecture,
% 0.21/0.48      g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK2))).
% 0.21/0.48  
% 0.21/0.48  cnf(u44,negated_conjecture,
% 0.21/0.48      g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))).
% 0.21/0.48  
% 0.21/0.48  cnf(u177,negated_conjecture,
% 0.21/0.48      u1_orders_2(sK1) = u1_orders_2(sK3)).
% 0.21/0.48  
% 0.21/0.48  cnf(u164,negated_conjecture,
% 0.21/0.48      u1_orders_2(sK0) = u1_orders_2(sK2)).
% 0.21/0.48  
% 0.21/0.48  cnf(u106,negated_conjecture,
% 0.21/0.48      u1_struct_0(sK1) = u1_struct_0(sK3)).
% 0.21/0.48  
% 0.21/0.48  cnf(u90,negated_conjecture,
% 0.21/0.48      u1_struct_0(sK0) = u1_struct_0(sK2)).
% 0.21/0.48  
% 0.21/0.48  cnf(u129,negated_conjecture,
% 0.21/0.48      g1_orders_2(X6,X7) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK3)) | u1_struct_0(sK1) = X6).
% 0.21/0.48  
% 0.21/0.48  cnf(u146,negated_conjecture,
% 0.21/0.48      g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK3)) != g1_orders_2(X5,X6) | u1_orders_2(sK3) = X6).
% 0.21/0.48  
% 0.21/0.48  cnf(u84,negated_conjecture,
% 0.21/0.48      g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) | u1_struct_0(sK1) = X2).
% 0.21/0.48  
% 0.21/0.48  cnf(u155,negated_conjecture,
% 0.21/0.48      g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) | u1_orders_2(sK3) = X1).
% 0.21/0.48  
% 0.21/0.48  cnf(u179,negated_conjecture,
% 0.21/0.48      g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) | u1_orders_2(sK1) = X1).
% 0.21/0.48  
% 0.21/0.48  cnf(u127,negated_conjecture,
% 0.21/0.48      g1_orders_2(X4,X5) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK2)) | u1_struct_0(sK0) = X4).
% 0.21/0.48  
% 0.21/0.48  cnf(u145,negated_conjecture,
% 0.21/0.48      g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK2)) != g1_orders_2(X3,X4) | u1_orders_2(sK2) = X4).
% 0.21/0.48  
% 0.21/0.48  cnf(u83,negated_conjecture,
% 0.21/0.48      g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) | u1_struct_0(sK0) = X0).
% 0.21/0.48  
% 0.21/0.48  cnf(u147,negated_conjecture,
% 0.21/0.48      g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) | u1_orders_2(sK2) = X1).
% 0.21/0.48  
% 0.21/0.48  cnf(u165,negated_conjecture,
% 0.21/0.48      g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) | u1_orders_2(sK0) = X1).
% 0.21/0.48  
% 0.21/0.48  % (9857)# SZS output end Saturation.
% 0.21/0.48  % (9857)------------------------------
% 0.21/0.48  % (9857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (9857)Termination reason: Satisfiable
% 0.21/0.48  
% 0.21/0.48  % (9857)Memory used [KB]: 6268
% 0.21/0.48  % (9857)Time elapsed: 0.082 s
% 0.21/0.48  % (9857)------------------------------
% 0.21/0.48  % (9857)------------------------------
% 0.21/0.48  % (9835)Success in time 0.126 s
%------------------------------------------------------------------------------
