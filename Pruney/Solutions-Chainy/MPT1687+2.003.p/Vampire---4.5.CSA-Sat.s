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
% DateTime   : Thu Dec  3 13:17:20 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 131 expanded)
%              Number of leaves         :  131 ( 131 expanded)
%              Depth                    :    0
%              Number of atoms          :  378 ( 378 expanded)
%              Number of equality atoms :  127 ( 127 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u1031,axiom,(
    ! [X4] :
      ( k1_xboole_0 != X4
      | k1_xboole_0 = sK6(k1_xboole_0,k1_zfmisc_1(X4))
      | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(X4) ) )).

tff(u1030,axiom,(
    ! [X1,X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X0) ) )).

tff(u1029,axiom,(
    ! [X2] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k3_tarski(k1_zfmisc_1(X2)) ) )).

tff(u1028,axiom,(
    ! [X0,X2] :
      ( k1_xboole_0 != k3_tarski(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X2 ) )).

tff(u1027,negated_conjecture,
    ( ~ ( k1_xboole_0 != k2_relat_1(sK2) )
    | k1_xboole_0 != k2_relat_1(sK2) )).

tff(u1026,negated_conjecture,
    ( ~ ( k1_xboole_0 != k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) )
    | k1_xboole_0 != k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) )).

tff(u1025,negated_conjecture,
    ( ~ ( k1_xboole_0 != u1_struct_0(sK1) )
    | k1_xboole_0 != u1_struct_0(sK1) )).

tff(u1024,axiom,(
    ! [X0] :
      ( k1_xboole_0 != sK3(X0)
      | k1_xboole_0 = k3_tarski(X0) ) )).

tff(u1023,axiom,(
    ! [X0] : k1_xboole_0 = sK5(X0) )).

tff(u1022,axiom,
    ( ~ ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) )).

tff(u1021,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 )).

tff(u1020,negated_conjecture,
    ( ~ ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)
    | ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) )).

tff(u1019,negated_conjecture,
    ( k2_relat_1(sK2) != k9_relat_1(sK2,k1_relat_1(sK2))
    | k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) )).

tff(u1018,axiom,
    ( ~ ! [X1] : k9_relat_1(k1_xboole_0,X1) = k2_relat_1(k1_xboole_0)
    | ! [X1] : k9_relat_1(k1_xboole_0,X1) = k2_relat_1(k1_xboole_0) )).

tff(u1017,axiom,
    ( ~ ! [X1,X0,X2] : k2_relat_1(k1_xboole_0) = k7_relset_1(X0,X1,k1_xboole_0,X2)
    | ! [X1,X0,X2] : k2_relat_1(k1_xboole_0) = k7_relset_1(X0,X1,k1_xboole_0,X2) )).

tff(u1016,negated_conjecture,
    ( k2_relat_1(sK2) != k7_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2,k1_relat_1(sK2))
    | k2_relat_1(sK2) = k7_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2,k1_relat_1(sK2)) )).

tff(u1015,negated_conjecture,
    ( k2_relat_1(sK2) != k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,k1_relat_1(sK2))
    | k2_relat_1(sK2) = k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,k1_relat_1(sK2)) )).

% (29611)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
tff(u1014,negated_conjecture,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2)
    | k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) )).

tff(u1013,negated_conjecture,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) )).

tff(u1012,negated_conjecture,
    ( ~ ! [X0] : k9_relat_1(sK2,X0) = k7_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2,X0)
    | ! [X0] : k9_relat_1(sK2,X0) = k7_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2,X0) )).

tff(u1011,negated_conjecture,
    ( ~ ! [X0] : k9_relat_1(sK2,X0) = k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X0)
    | ! [X0] : k9_relat_1(sK2,X0) = k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X0) )).

tff(u1010,negated_conjecture,
    ( k1_relat_1(sK2) != k8_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2,u1_struct_0(sK1))
    | k1_relat_1(sK2) = k8_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2,u1_struct_0(sK1)) )).

% (29591)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
tff(u1009,negated_conjecture,
    ( k1_relat_1(sK2) != k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,k2_relat_1(sK2))
    | k1_relat_1(sK2) = k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,k2_relat_1(sK2)) )).

tff(u1008,negated_conjecture,
    ( k1_relat_1(sK2) != k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) )).

tff(u1007,axiom,(
    ! [X1,X0] : k2_relset_1(X0,X1,k1_xboole_0) = k2_relat_1(k1_xboole_0) )).

tff(u1006,axiom,
    ( ~ ! [X1,X0] : k1_relset_1(X0,X1,k1_xboole_0) = k8_relset_1(X0,X1,k1_xboole_0,k2_relat_1(k1_xboole_0))
    | ! [X1,X0] : k1_relset_1(X0,X1,k1_xboole_0) = k8_relset_1(X0,X1,k1_xboole_0,k2_relat_1(k1_xboole_0)) )).

tff(u1005,negated_conjecture,
    ( k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) != k8_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2,k2_relat_1(sK2))
    | k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) = k8_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2,k2_relat_1(sK2)) )).

tff(u1004,negated_conjecture,
    ( u1_struct_0(sK0) != k1_relat_1(sK2)
    | u1_struct_0(sK0) = k1_relat_1(sK2) )).

tff(u1003,negated_conjecture,
    ( sK2 != k7_relat_1(sK2,k1_relat_1(sK2))
    | sK2 = k7_relat_1(sK2,k1_relat_1(sK2)) )).

tff(u1002,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(sK6(X0,X1),X0)
      | k1_zfmisc_1(X0) = X1
      | ~ r2_hidden(sK6(X0,X1),X1) ) )).

tff(u1001,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) )).

tff(u1000,axiom,(
    ! [X1,X3,X2] :
      ( ~ r1_tarski(k2_relat_1(X3),X1)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ sP7(X3,X2) ) )).

tff(u999,axiom,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) )).

tff(u998,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_orders_2(X1)
      | ~ m1_yellow_0(X0,X1)
      | u1_struct_0(X0) = u1_struct_0(X1) ) )).

tff(u997,negated_conjecture,
    ( ~ ! [X1] :
          ( ~ r1_tarski(k1_relat_1(sK2),u1_struct_0(X1))
          | ~ m1_yellow_0(X1,sK0)
          | u1_struct_0(X1) = k1_relat_1(sK2) )
    | ! [X1] :
        ( ~ r1_tarski(k1_relat_1(sK2),u1_struct_0(X1))
        | ~ m1_yellow_0(X1,sK0)
        | u1_struct_0(X1) = k1_relat_1(sK2) ) )).

tff(u996,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
      | ~ l1_orders_2(X1)
      | ~ m1_yellow_0(X0,X1)
      | u1_orders_2(X1) = u1_orders_2(X0) ) )).

tff(u995,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
      | m1_yellow_0(X1,X0)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) )).

tff(u994,axiom,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK3(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X0
      | sK3(k1_zfmisc_1(X0)) = X0 ) )).

tff(u993,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,sK6(X0,X1))
      | k1_zfmisc_1(X0) = X1
      | r2_hidden(sK6(X0,X1),X1)
      | sK6(X0,X1) = X0 ) )).

tff(u992,axiom,(
    ! [X3,X2] :
      ( ~ r1_tarski(X2,sK6(X2,k1_zfmisc_1(X3)))
      | k1_xboole_0 != X3
      | k1_zfmisc_1(X2) = k1_zfmisc_1(X3)
      | k1_xboole_0 = sK6(X2,k1_zfmisc_1(X3))
      | sK6(X2,k1_zfmisc_1(X3)) = X2 ) )).

tff(u991,axiom,(
    ! [X3,X2] :
      ( ~ r1_tarski(X2,sK6(X2,k1_zfmisc_1(X3)))
      | k1_zfmisc_1(X2) = k1_zfmisc_1(X3)
      | r1_tarski(sK6(X2,k1_zfmisc_1(X3)),X3)
      | sK6(X2,k1_zfmisc_1(X3)) = X2 ) )).

tff(u990,axiom,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK6(X1,k1_zfmisc_1(k1_xboole_0)))
      | k1_xboole_0 = sK6(X1,k1_zfmisc_1(k1_xboole_0))
      | k1_zfmisc_1(X1) = k1_zfmisc_1(k1_xboole_0)
      | sK6(X1,k1_zfmisc_1(k1_xboole_0)) = X1 ) )).

tff(u989,axiom,(
    ! [X1,X2] :
      ( ~ r1_tarski(X2,sK6(X1,k1_zfmisc_1(X2)))
      | k1_zfmisc_1(X1) = k1_zfmisc_1(X2)
      | r1_tarski(sK6(X1,k1_zfmisc_1(X2)),X1)
      | sK6(X1,k1_zfmisc_1(X2)) = X2 ) )).

tff(u988,axiom,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK6(k1_xboole_0,k1_zfmisc_1(X0)))
      | k1_xboole_0 = sK6(k1_xboole_0,k1_zfmisc_1(X0))
      | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)
      | sK6(k1_xboole_0,k1_zfmisc_1(X0)) = X0 ) )).

tff(u987,axiom,(
    ! [X1] : r1_tarski(X1,X1) )).

tff(u986,axiom,(
    ! [X1,X0] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) )).

tff(u985,negated_conjecture,
    ( ~ ! [X2] :
          ( r1_tarski(u1_struct_0(X2),k1_relat_1(sK2))
          | ~ m1_yellow_0(X2,sK0) )
    | ! [X2] :
        ( r1_tarski(u1_struct_0(X2),k1_relat_1(sK2))
        | ~ m1_yellow_0(X2,sK0) ) )).

tff(u984,axiom,(
    ! [X1,X0] :
      ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) )).

tff(u983,axiom,(
    ! [X0] :
      ( r1_tarski(sK3(k1_zfmisc_1(X0)),X0)
      | k1_xboole_0 = X0 ) )).

tff(u982,axiom,(
    ! [X3,X4] :
      ( r1_tarski(sK6(X4,k1_zfmisc_1(X3)),X4)
      | k1_xboole_0 = sK6(X4,k1_zfmisc_1(X3))
      | k1_xboole_0 != X3
      | k1_zfmisc_1(X3) = k1_zfmisc_1(X4) ) )).

tff(u981,axiom,(
    ! [X3] :
      ( r1_tarski(sK6(X3,k1_zfmisc_1(k1_xboole_0)),X3)
      | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(X3)
      | k1_xboole_0 = sK6(X3,k1_zfmisc_1(k1_xboole_0)) ) )).

tff(u980,axiom,(
    ! [X1,X0] :
      ( r1_tarski(sK6(X0,k1_zfmisc_1(X1)),X0)
      | r1_tarski(sK6(X0,k1_zfmisc_1(X1)),X1)
      | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ) )).

tff(u979,axiom,(
    ! [X4] :
      ( r1_tarski(sK6(k1_xboole_0,k1_zfmisc_1(X4)),X4)
      | k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(X4)
      | k1_xboole_0 = sK6(k1_xboole_0,k1_zfmisc_1(X4)) ) )).

tff(u978,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) )).

tff(u977,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u976,negated_conjecture,
    ( ~ ~ v1_xboole_0(k1_relat_1(sK2))
    | ~ v1_xboole_0(k1_relat_1(sK2)) )).

tff(u975,axiom,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) )).

tff(u974,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(X1,k1_zfmisc_1(X0))
      | k1_xboole_0 != X0
      | k1_xboole_0 = X1 ) )).

tff(u973,axiom,(
    ! [X3,X0] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) )).

tff(u972,axiom,(
    ! [X0] :
      ( ~ r2_hidden(sK6(X0,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = sK6(X0,k1_zfmisc_1(k1_xboole_0))
      | k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0) ) )).

tff(u971,axiom,(
    ! [X3,X0] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) )).

tff(u970,axiom,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = k3_tarski(X0) ) )).

tff(u969,axiom,(
    ! [X1,X0] :
      ( r1_tarski(sK6(X0,X1),X0)
      | r2_hidden(sK6(X0,X1),X1)
      | k1_zfmisc_1(X0) = X1 ) )).

tff(u968,axiom,(
    ! [X0] :
      ( r2_hidden(sK6(k1_xboole_0,X0),X0)
      | k1_xboole_0 = sK6(k1_xboole_0,X0)
      | k1_zfmisc_1(k1_xboole_0) = X0 ) )).

tff(u967,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) )).

tff(u966,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) )).

tff(u965,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) )).

tff(u964,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) )).

tff(u963,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) )).

tff(u962,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) ) )).

tff(u961,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) )).

tff(u960,axiom,(
    ! [X3,X0,X2] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | sP7(X3,X2) ) )).

tff(u959,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0)))
          | v1_funct_2(sK2,k1_relat_1(sK2),X0) )
    | ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0)))
        | v1_funct_2(sK2,k1_relat_1(sK2),X0) ) )).

tff(u958,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | k1_xboole_0 = X0
          | ~ v1_funct_2(sK2,X1,X0)
          | k8_relset_1(X1,X0,sK2,X0) = X1 )
    | ! [X1,X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | k1_xboole_0 = X0
        | ~ v1_funct_2(sK2,X1,X0)
        | k8_relset_1(X1,X0,sK2,X0) = X1 ) )).

tff(u957,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

tff(u956,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) )).

tff(u955,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) )).

tff(u954,axiom,(
    ! [X1,X0] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) )).

tff(u953,negated_conjecture,
    ( ~ v1_relat_1(sK2)
    | v1_relat_1(sK2) )).

tff(u952,axiom,
    ( ~ v1_relat_1(k1_xboole_0)
    | v1_relat_1(k1_xboole_0) )).

tff(u951,axiom,(
    ! [X1,X0] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) )).

tff(u950,axiom,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) )).

tff(u949,negated_conjecture,
    ( ~ v4_relat_1(sK2,k1_relat_1(sK2))
    | v4_relat_1(sK2,k1_relat_1(sK2)) )).

tff(u948,axiom,(
    ! [X1,X0,X2] :
      ( ~ v1_funct_1(X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k8_relset_1(X0,X1,X2,X1) = X0 ) )).

tff(u947,axiom,(
    ! [X1,X0,X2] :
      ( ~ v1_funct_1(X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) )).

tff(u946,axiom,(
    ! [X1,X0,X2] :
      ( ~ v1_funct_1(X2)
      | ~ v1_partfun1(X2,X0)
      | v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) )).

tff(u945,negated_conjecture,
    ( ~ ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2)) )).

tff(u944,negated_conjecture,
    ( ~ v1_funct_1(sK2)
    | v1_funct_1(sK2) )).

tff(u943,axiom,(
    ! [X1,X0,X2] :
      ( ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) )).

tff(u942,axiom,(
    ! [X1,X0,X2] :
      ( ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) )).

tff(u941,axiom,(
    ! [X1,X0,X2] :
      ( ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_1(k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) )).

tff(u940,axiom,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) )).

tff(u939,axiom,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) )).

tff(u938,axiom,(
    ! [X0] : v5_relat_1(k1_xboole_0,X0) )).

tff(u937,negated_conjecture,
    ( ~ v5_relat_1(sK2,u1_struct_0(sK1))
    | v5_relat_1(sK2,u1_struct_0(sK1)) )).

tff(u936,negated_conjecture,
    ( ~ v5_relat_1(sK2,k2_relat_1(sK2))
    | v5_relat_1(sK2,k2_relat_1(sK2)) )).

tff(u935,axiom,(
    ! [X1,X0] :
      ( ~ v1_partfun1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) )).

% (29609)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
tff(u934,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( ~ v1_partfun1(sK2,X0)
          | v1_funct_2(sK2,X0,X1)
          | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ! [X1,X0] :
        ( ~ v1_partfun1(sK2,X0)
        | v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) )).

tff(u933,axiom,(
    ! [X1] :
      ( v1_partfun1(X1,k1_relat_1(X1))
      | ~ v4_relat_1(X1,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) )).

tff(u932,negated_conjecture,
    ( ~ v1_partfun1(sK2,k1_relat_1(sK2))
    | v1_partfun1(sK2,k1_relat_1(sK2)) )).

tff(u931,axiom,(
    ! [X1,X2] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X2,X1)
      | ~ v1_funct_1(X2) ) )).

tff(u930,axiom,(
    ! [X1,X2] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | v1_partfun1(X2,k1_xboole_0)
      | ~ v1_funct_1(X2) ) )).

tff(u929,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( ~ v1_funct_2(sK2,X1,X0)
          | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | k1_xboole_0 = X0
          | v1_partfun1(sK2,X1) )
    | ! [X1,X0] :
        ( ~ v1_funct_2(sK2,X1,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | k1_xboole_0 = X0
        | v1_partfun1(sK2,X1) ) )).

tff(u928,negated_conjecture,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) )).

tff(u927,negated_conjecture,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) )).

tff(u926,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v2_struct_0(sK0) )).

tff(u925,negated_conjecture,
    ( ~ ~ v2_struct_0(sK1)
    | ~ v2_struct_0(sK1) )).

tff(u924,axiom,(
    ! [X0] :
      ( ~ v2_struct_0(sK4(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u923,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | l1_struct_0(sK0) )).

tff(u922,negated_conjecture,
    ( ~ l1_struct_0(sK1)
    | l1_struct_0(sK1) )).

tff(u921,axiom,(
    ! [X0] :
      ( l1_struct_0(sK4(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u920,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) )).

tff(u919,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK0) )).

tff(u918,negated_conjecture,
    ( ~ l1_orders_2(sK1)
    | l1_orders_2(sK1) )).

tff(u917,axiom,(
    ! [X0] :
      ( l1_orders_2(sK4(X0))
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) )).

tff(u916,axiom,(
    ! [X1,X0] :
      ( ~ m1_yellow_0(X0,X1)
      | u1_orders_2(X1) = u1_orders_2(X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X1) ) )).

tff(u915,axiom,(
    ! [X1,X0] :
      ( ~ m1_yellow_0(X0,X1)
      | u1_struct_0(X0) = u1_struct_0(X1)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X1) ) )).

tff(u914,axiom,(
    ! [X1,X0] :
      ( ~ m1_yellow_0(X1,X0)
      | l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) )).

tff(u913,axiom,(
    ! [X0] :
      ( ~ m1_yellow_0(X0,sK4(X0))
      | u1_orders_2(X0) = u1_orders_2(sK4(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u912,axiom,(
    ! [X0] :
      ( ~ m1_yellow_0(X0,sK4(X0))
      | u1_struct_0(X0) = u1_struct_0(sK4(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u911,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ m1_yellow_0(sK0,X0)
          | ~ l1_orders_2(X0)
          | ~ r1_tarski(u1_struct_0(X0),k1_relat_1(sK2))
          | u1_struct_0(X0) = k1_relat_1(sK2) )
    | ! [X0] :
        ( ~ m1_yellow_0(sK0,X0)
        | ~ l1_orders_2(X0)
        | ~ r1_tarski(u1_struct_0(X0),k1_relat_1(sK2))
        | u1_struct_0(X0) = k1_relat_1(sK2) ) )).

tff(u910,negated_conjecture,
    ( ~ ! [X3] :
          ( ~ m1_yellow_0(sK0,X3)
          | r1_tarski(k1_relat_1(sK2),u1_struct_0(X3))
          | ~ l1_orders_2(X3) )
    | ! [X3] :
        ( ~ m1_yellow_0(sK0,X3)
        | r1_tarski(k1_relat_1(sK2),u1_struct_0(X3))
        | ~ l1_orders_2(X3) ) )).

tff(u909,axiom,(
    ! [X0] :
      ( m1_yellow_0(sK4(X0),X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u908,axiom,(
    ! [X2] :
      ( m1_yellow_0(X2,X2)
      | ~ l1_orders_2(X2) ) )).

tff(u907,axiom,(
    ! [X0] :
      ( v1_orders_2(sK4(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u906,axiom,(
    ! [X0] :
      ( v4_yellow_0(sK4(X0),X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u905,negated_conjecture,
    ( ~ v23_waybel_0(sK2,sK0,sK1)
    | v23_waybel_0(sK2,sK0,sK1) )).

tff(u904,axiom,(
    ! [X1,X0] :
      ( ~ sP7(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ) )).

tff(u903,negated_conjecture,
    ( ~ ! [X1,X0,X2] :
          ( ~ sP7(k7_relat_1(sK2,X0),X2)
          | m1_subset_1(k7_relat_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          | ~ r1_tarski(k9_relat_1(sK2,X0),X1) )
    | ! [X1,X0,X2] :
        ( ~ sP7(k7_relat_1(sK2,X0),X2)
        | m1_subset_1(k7_relat_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ r1_tarski(k9_relat_1(sK2,X0),X1) ) )).

tff(u902,axiom,(
    ! [X0] : sP7(k1_xboole_0,X0) )).

tff(u901,negated_conjecture,
    ( ~ sP7(sK2,k1_relat_1(sK2))
    | sP7(sK2,k1_relat_1(sK2)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:10:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (29593)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (29596)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (29602)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (29590)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (29604)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (29589)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (29601)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (29589)Refutation not found, incomplete strategy% (29589)------------------------------
% 0.21/0.52  % (29589)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (29589)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (29589)Memory used [KB]: 10746
% 0.21/0.52  % (29589)Time elapsed: 0.109 s
% 0.21/0.52  % (29589)------------------------------
% 0.21/0.52  % (29589)------------------------------
% 0.21/0.52  % (29592)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % (29595)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (29603)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (29607)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.53  % (29593)Refutation not found, incomplete strategy% (29593)------------------------------
% 0.21/0.53  % (29593)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (29593)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (29593)Memory used [KB]: 6140
% 0.21/0.53  % (29593)Time elapsed: 0.121 s
% 0.21/0.53  % (29593)------------------------------
% 0.21/0.53  % (29593)------------------------------
% 0.21/0.53  % (29600)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.53  % (29610)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.53  % (29608)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.53  % (29588)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.53  % (29597)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.53  % (29588)Refutation not found, incomplete strategy% (29588)------------------------------
% 0.21/0.53  % (29588)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (29588)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (29588)Memory used [KB]: 10618
% 0.21/0.53  % (29588)Time elapsed: 0.123 s
% 0.21/0.53  % (29588)------------------------------
% 0.21/0.53  % (29588)------------------------------
% 0.21/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.54  % (29601)Refutation not found, incomplete strategy% (29601)------------------------------
% 0.21/0.54  % (29601)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (29601)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (29601)Memory used [KB]: 6140
% 0.21/0.54  % (29601)Time elapsed: 0.133 s
% 0.21/0.54  % (29601)------------------------------
% 0.21/0.54  % (29601)------------------------------
% 0.21/0.54  % (29594)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.54  % (29594)Refutation not found, incomplete strategy% (29594)------------------------------
% 0.21/0.54  % (29594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (29594)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (29594)Memory used [KB]: 10618
% 0.21/0.54  % (29594)Time elapsed: 0.104 s
% 0.21/0.54  % (29594)------------------------------
% 0.21/0.54  % (29594)------------------------------
% 0.21/0.54  % (29590)# SZS output start Saturation.
% 0.21/0.54  tff(u1031,axiom,
% 0.21/0.54      (![X4] : (((k1_xboole_0 != X4) | (k1_xboole_0 = sK6(k1_xboole_0,k1_zfmisc_1(X4))) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(X4)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u1030,axiom,
% 0.21/0.54      (![X1, X0] : (((k1_xboole_0 != X0) | (k1_xboole_0 = X1) | ~r1_tarski(X1,X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u1029,axiom,
% 0.21/0.54      (![X2] : (((k1_xboole_0 != X2) | (k1_xboole_0 = k3_tarski(k1_zfmisc_1(X2))))))).
% 0.21/0.54  
% 0.21/0.54  tff(u1028,axiom,
% 0.21/0.54      (![X0, X2] : (((k1_xboole_0 != k3_tarski(X0)) | ~r2_hidden(X2,X0) | (k1_xboole_0 = X2))))).
% 0.21/0.54  
% 0.21/0.54  tff(u1027,negated_conjecture,
% 0.21/0.54      ((~(k1_xboole_0 != k2_relat_1(sK2))) | (k1_xboole_0 != k2_relat_1(sK2)))).
% 0.21/0.54  
% 0.21/0.54  tff(u1026,negated_conjecture,
% 0.21/0.54      ((~(k1_xboole_0 != k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2))) | (k1_xboole_0 != k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2)))).
% 0.21/0.54  
% 0.21/0.54  tff(u1025,negated_conjecture,
% 0.21/0.54      ((~(k1_xboole_0 != u1_struct_0(sK1))) | (k1_xboole_0 != u1_struct_0(sK1)))).
% 0.21/0.54  
% 0.21/0.54  tff(u1024,axiom,
% 0.21/0.54      (![X0] : (((k1_xboole_0 != sK3(X0)) | (k1_xboole_0 = k3_tarski(X0)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u1023,axiom,
% 0.21/0.54      (![X0] : ((k1_xboole_0 = sK5(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u1022,axiom,
% 0.21/0.54      ((~(![X0] : ((k1_xboole_0 = k7_relat_1(k1_xboole_0,X0))))) | (![X0] : ((k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u1021,axiom,
% 0.21/0.54      (![X0] : ((k3_tarski(k1_zfmisc_1(X0)) = X0)))).
% 0.21/0.54  
% 0.21/0.54  tff(u1020,negated_conjecture,
% 0.21/0.54      ((~(![X0] : ((k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0))))) | (![X0] : ((k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u1019,negated_conjecture,
% 0.21/0.54      ((~(k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)))) | (k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))))).
% 0.21/0.54  
% 0.21/0.54  tff(u1018,axiom,
% 0.21/0.54      ((~(![X1] : ((k9_relat_1(k1_xboole_0,X1) = k2_relat_1(k1_xboole_0))))) | (![X1] : ((k9_relat_1(k1_xboole_0,X1) = k2_relat_1(k1_xboole_0)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u1017,axiom,
% 0.21/0.54      ((~(![X1, X0, X2] : ((k2_relat_1(k1_xboole_0) = k7_relset_1(X0,X1,k1_xboole_0,X2))))) | (![X1, X0, X2] : ((k2_relat_1(k1_xboole_0) = k7_relset_1(X0,X1,k1_xboole_0,X2)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u1016,negated_conjecture,
% 0.21/0.54      ((~(k2_relat_1(sK2) = k7_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2,k1_relat_1(sK2)))) | (k2_relat_1(sK2) = k7_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2,k1_relat_1(sK2))))).
% 0.21/0.54  
% 0.21/0.54  tff(u1015,negated_conjecture,
% 0.21/0.54      ((~(k2_relat_1(sK2) = k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,k1_relat_1(sK2)))) | (k2_relat_1(sK2) = k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,k1_relat_1(sK2))))).
% 0.21/0.54  
% 0.21/0.54  % (29611)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.54  tff(u1014,negated_conjecture,
% 0.21/0.54      ((~(k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2))) | (k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2)))).
% 0.21/0.54  
% 0.21/0.54  tff(u1013,negated_conjecture,
% 0.21/0.54      ((~(k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) | (k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)))).
% 0.21/0.54  
% 0.21/0.54  tff(u1012,negated_conjecture,
% 0.21/0.54      ((~(![X0] : ((k9_relat_1(sK2,X0) = k7_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2,X0))))) | (![X0] : ((k9_relat_1(sK2,X0) = k7_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2,X0)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u1011,negated_conjecture,
% 0.21/0.54      ((~(![X0] : ((k9_relat_1(sK2,X0) = k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X0))))) | (![X0] : ((k9_relat_1(sK2,X0) = k7_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X0)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u1010,negated_conjecture,
% 0.21/0.54      ((~(k1_relat_1(sK2) = k8_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2,u1_struct_0(sK1)))) | (k1_relat_1(sK2) = k8_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2,u1_struct_0(sK1))))).
% 0.21/0.54  
% 0.21/0.54  % (29591)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.54  tff(u1009,negated_conjecture,
% 0.21/0.54      ((~(k1_relat_1(sK2) = k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,k2_relat_1(sK2)))) | (k1_relat_1(sK2) = k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,k2_relat_1(sK2))))).
% 0.21/0.54  
% 0.21/0.54  tff(u1008,negated_conjecture,
% 0.21/0.54      ((~(k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) | (k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)))).
% 0.21/0.54  
% 0.21/0.54  tff(u1007,axiom,
% 0.21/0.54      (![X1, X0] : ((k2_relset_1(X0,X1,k1_xboole_0) = k2_relat_1(k1_xboole_0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u1006,axiom,
% 0.21/0.54      ((~(![X1, X0] : ((k1_relset_1(X0,X1,k1_xboole_0) = k8_relset_1(X0,X1,k1_xboole_0,k2_relat_1(k1_xboole_0)))))) | (![X1, X0] : ((k1_relset_1(X0,X1,k1_xboole_0) = k8_relset_1(X0,X1,k1_xboole_0,k2_relat_1(k1_xboole_0))))))).
% 0.21/0.54  
% 0.21/0.54  tff(u1005,negated_conjecture,
% 0.21/0.54      ((~(k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) = k8_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2,k2_relat_1(sK2)))) | (k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) = k8_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2,k2_relat_1(sK2))))).
% 0.21/0.54  
% 0.21/0.54  tff(u1004,negated_conjecture,
% 0.21/0.54      ((~(u1_struct_0(sK0) = k1_relat_1(sK2))) | (u1_struct_0(sK0) = k1_relat_1(sK2)))).
% 0.21/0.54  
% 0.21/0.54  tff(u1003,negated_conjecture,
% 0.21/0.54      ((~(sK2 = k7_relat_1(sK2,k1_relat_1(sK2)))) | (sK2 = k7_relat_1(sK2,k1_relat_1(sK2))))).
% 0.21/0.54  
% 0.21/0.54  tff(u1002,axiom,
% 0.21/0.54      (![X1, X0] : ((~r1_tarski(sK6(X0,X1),X0) | (k1_zfmisc_1(X0) = X1) | ~r2_hidden(sK6(X0,X1),X1))))).
% 0.21/0.54  
% 0.21/0.54  tff(u1001,axiom,
% 0.21/0.54      (![X1, X0] : ((~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | (X0 = X1))))).
% 0.21/0.54  
% 0.21/0.54  tff(u1000,axiom,
% 0.21/0.54      (![X1, X3, X2] : ((~r1_tarski(k2_relat_1(X3),X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~sP7(X3,X2))))).
% 0.21/0.54  
% 0.21/0.54  tff(u999,axiom,
% 0.21/0.54      (![X0] : ((~r1_tarski(X0,k1_xboole_0) | (k1_xboole_0 = X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u998,axiom,
% 0.21/0.54      (![X1, X0] : ((~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~l1_orders_2(X1) | ~m1_yellow_0(X0,X1) | (u1_struct_0(X0) = u1_struct_0(X1)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u997,negated_conjecture,
% 0.21/0.54      ((~(![X1] : ((~r1_tarski(k1_relat_1(sK2),u1_struct_0(X1)) | ~m1_yellow_0(X1,sK0) | (u1_struct_0(X1) = k1_relat_1(sK2)))))) | (![X1] : ((~r1_tarski(k1_relat_1(sK2),u1_struct_0(X1)) | ~m1_yellow_0(X1,sK0) | (u1_struct_0(X1) = k1_relat_1(sK2))))))).
% 0.21/0.54  
% 0.21/0.54  tff(u996,axiom,
% 0.21/0.54      (![X1, X0] : ((~r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~l1_orders_2(X1) | ~m1_yellow_0(X0,X1) | (u1_orders_2(X1) = u1_orders_2(X0)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u995,axiom,
% 0.21/0.54      (![X1, X0] : ((~r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | m1_yellow_0(X1,X0) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~l1_orders_2(X1) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u994,axiom,
% 0.21/0.54      (![X0] : ((~r1_tarski(X0,sK3(k1_zfmisc_1(X0))) | (k1_xboole_0 = X0) | (sK3(k1_zfmisc_1(X0)) = X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u993,axiom,
% 0.21/0.54      (![X1, X0] : ((~r1_tarski(X0,sK6(X0,X1)) | (k1_zfmisc_1(X0) = X1) | r2_hidden(sK6(X0,X1),X1) | (sK6(X0,X1) = X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u992,axiom,
% 0.21/0.54      (![X3, X2] : ((~r1_tarski(X2,sK6(X2,k1_zfmisc_1(X3))) | (k1_xboole_0 != X3) | (k1_zfmisc_1(X2) = k1_zfmisc_1(X3)) | (k1_xboole_0 = sK6(X2,k1_zfmisc_1(X3))) | (sK6(X2,k1_zfmisc_1(X3)) = X2))))).
% 0.21/0.54  
% 0.21/0.54  tff(u991,axiom,
% 0.21/0.54      (![X3, X2] : ((~r1_tarski(X2,sK6(X2,k1_zfmisc_1(X3))) | (k1_zfmisc_1(X2) = k1_zfmisc_1(X3)) | r1_tarski(sK6(X2,k1_zfmisc_1(X3)),X3) | (sK6(X2,k1_zfmisc_1(X3)) = X2))))).
% 0.21/0.54  
% 0.21/0.54  tff(u990,axiom,
% 0.21/0.54      (![X1] : ((~r1_tarski(X1,sK6(X1,k1_zfmisc_1(k1_xboole_0))) | (k1_xboole_0 = sK6(X1,k1_zfmisc_1(k1_xboole_0))) | (k1_zfmisc_1(X1) = k1_zfmisc_1(k1_xboole_0)) | (sK6(X1,k1_zfmisc_1(k1_xboole_0)) = X1))))).
% 0.21/0.54  
% 0.21/0.54  tff(u989,axiom,
% 0.21/0.54      (![X1, X2] : ((~r1_tarski(X2,sK6(X1,k1_zfmisc_1(X2))) | (k1_zfmisc_1(X1) = k1_zfmisc_1(X2)) | r1_tarski(sK6(X1,k1_zfmisc_1(X2)),X1) | (sK6(X1,k1_zfmisc_1(X2)) = X2))))).
% 0.21/0.54  
% 0.21/0.54  tff(u988,axiom,
% 0.21/0.54      (![X0] : ((~r1_tarski(X0,sK6(k1_xboole_0,k1_zfmisc_1(X0))) | (k1_xboole_0 = sK6(k1_xboole_0,k1_zfmisc_1(X0))) | (k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)) | (sK6(k1_xboole_0,k1_zfmisc_1(X0)) = X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u987,axiom,
% 0.21/0.54      (![X1] : (r1_tarski(X1,X1)))).
% 0.21/0.54  
% 0.21/0.54  tff(u986,axiom,
% 0.21/0.54      (![X1, X0] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u985,negated_conjecture,
% 0.21/0.54      ((~(![X2] : ((r1_tarski(u1_struct_0(X2),k1_relat_1(sK2)) | ~m1_yellow_0(X2,sK0))))) | (![X2] : ((r1_tarski(u1_struct_0(X2),k1_relat_1(sK2)) | ~m1_yellow_0(X2,sK0)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u984,axiom,
% 0.21/0.54      (![X1, X0] : ((r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u983,axiom,
% 0.21/0.54      (![X0] : ((r1_tarski(sK3(k1_zfmisc_1(X0)),X0) | (k1_xboole_0 = X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u982,axiom,
% 0.21/0.54      (![X3, X4] : ((r1_tarski(sK6(X4,k1_zfmisc_1(X3)),X4) | (k1_xboole_0 = sK6(X4,k1_zfmisc_1(X3))) | (k1_xboole_0 != X3) | (k1_zfmisc_1(X3) = k1_zfmisc_1(X4)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u981,axiom,
% 0.21/0.54      (![X3] : ((r1_tarski(sK6(X3,k1_zfmisc_1(k1_xboole_0)),X3) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(X3)) | (k1_xboole_0 = sK6(X3,k1_zfmisc_1(k1_xboole_0))))))).
% 0.21/0.54  
% 0.21/0.54  tff(u980,axiom,
% 0.21/0.54      (![X1, X0] : ((r1_tarski(sK6(X0,k1_zfmisc_1(X1)),X0) | r1_tarski(sK6(X0,k1_zfmisc_1(X1)),X1) | (k1_zfmisc_1(X0) = k1_zfmisc_1(X1)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u979,axiom,
% 0.21/0.54      (![X4] : ((r1_tarski(sK6(k1_xboole_0,k1_zfmisc_1(X4)),X4) | (k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(X4)) | (k1_xboole_0 = sK6(k1_xboole_0,k1_zfmisc_1(X4))))))).
% 0.21/0.54  
% 0.21/0.54  tff(u978,axiom,
% 0.21/0.54      (![X0] : ((~v1_xboole_0(X0) | (k1_xboole_0 = X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u977,axiom,
% 0.21/0.54      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u976,negated_conjecture,
% 0.21/0.54      ((~~v1_xboole_0(k1_relat_1(sK2))) | ~v1_xboole_0(k1_relat_1(sK2)))).
% 0.21/0.54  
% 0.21/0.54  tff(u975,axiom,
% 0.21/0.54      ((~v1_xboole_0(k1_xboole_0)) | v1_xboole_0(k1_xboole_0))).
% 0.21/0.54  
% 0.21/0.54  tff(u974,axiom,
% 0.21/0.54      (![X1, X0] : ((~r2_hidden(X1,k1_zfmisc_1(X0)) | (k1_xboole_0 != X0) | (k1_xboole_0 = X1))))).
% 0.21/0.54  
% 0.21/0.54  tff(u973,axiom,
% 0.21/0.54      (![X3, X0] : ((~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u972,axiom,
% 0.21/0.54      (![X0] : ((~r2_hidden(sK6(X0,k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) | (k1_xboole_0 = sK6(X0,k1_zfmisc_1(k1_xboole_0))) | (k1_zfmisc_1(X0) = k1_zfmisc_1(k1_xboole_0)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u971,axiom,
% 0.21/0.54      (![X3, X0] : ((r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u970,axiom,
% 0.21/0.54      (![X0] : ((r2_hidden(sK3(X0),X0) | (k1_xboole_0 = k3_tarski(X0)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u969,axiom,
% 0.21/0.54      (![X1, X0] : ((r1_tarski(sK6(X0,X1),X0) | r2_hidden(sK6(X0,X1),X1) | (k1_zfmisc_1(X0) = X1))))).
% 0.21/0.54  
% 0.21/0.54  tff(u968,axiom,
% 0.21/0.54      (![X0] : ((r2_hidden(sK6(k1_xboole_0,X0),X0) | (k1_xboole_0 = sK6(k1_xboole_0,X0)) | (k1_zfmisc_1(k1_xboole_0) = X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u967,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2))))).
% 0.21/0.54  
% 0.21/0.54  tff(u966,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (k2_relset_1(X0,X1,X2) = k2_relat_1(X2)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u965,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u964,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1))))).
% 0.21/0.54  
% 0.21/0.54  tff(u963,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | (k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u962,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u961,axiom,
% 0.21/0.54      (![X1, X3, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u960,axiom,
% 0.21/0.54      (![X3, X0, X2] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | sP7(X3,X2))))).
% 0.21/0.54  
% 0.21/0.54  tff(u959,negated_conjecture,
% 0.21/0.54      ((~(![X0] : ((~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) | v1_funct_2(sK2,k1_relat_1(sK2),X0))))) | (![X0] : ((~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) | v1_funct_2(sK2,k1_relat_1(sK2),X0)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u958,negated_conjecture,
% 0.21/0.54      ((~(![X1, X0] : ((~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | (k1_xboole_0 = X0) | ~v1_funct_2(sK2,X1,X0) | (k8_relset_1(X1,X0,sK2,X0) = X1))))) | (![X1, X0] : ((~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | (k1_xboole_0 = X0) | ~v1_funct_2(sK2,X1,X0) | (k8_relset_1(X1,X0,sK2,X0) = X1)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u957,axiom,
% 0.21/0.54      (![X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u956,negated_conjecture,
% 0.21/0.54      ((~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u955,negated_conjecture,
% 0.21/0.54      ((~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u954,axiom,
% 0.21/0.54      (![X1, X0] : ((~v1_relat_1(X1) | (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u953,negated_conjecture,
% 0.21/0.54      ((~v1_relat_1(sK2)) | v1_relat_1(sK2))).
% 0.21/0.54  
% 0.21/0.54  tff(u952,axiom,
% 0.21/0.54      ((~v1_relat_1(k1_xboole_0)) | v1_relat_1(k1_xboole_0))).
% 0.21/0.54  
% 0.21/0.54  tff(u951,axiom,
% 0.21/0.54      (![X1, X0] : ((~v4_relat_1(X1,X0) | (k7_relat_1(X1,X0) = X1) | ~v1_relat_1(X1))))).
% 0.21/0.54  
% 0.21/0.54  tff(u950,axiom,
% 0.21/0.54      (![X0] : (v4_relat_1(k1_xboole_0,X0)))).
% 0.21/0.54  
% 0.21/0.54  tff(u949,negated_conjecture,
% 0.21/0.54      ((~v4_relat_1(sK2,k1_relat_1(sK2))) | v4_relat_1(sK2,k1_relat_1(sK2)))).
% 0.21/0.54  
% 0.21/0.54  tff(u948,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~v1_funct_1(X2) | (k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | (k8_relset_1(X0,X1,X2,X1) = X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u947,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~v1_funct_1(X2) | (k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u946,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~v1_funct_1(X2) | ~v1_partfun1(X2,X0) | v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))))).
% 0.21/0.54  
% 0.21/0.54  tff(u945,negated_conjecture,
% 0.21/0.54      ((~~v1_funct_1(k2_funct_1(sK2))) | ~v1_funct_1(k2_funct_1(sK2)))).
% 0.21/0.54  
% 0.21/0.54  tff(u944,negated_conjecture,
% 0.21/0.54      ((~v1_funct_1(sK2)) | v1_funct_1(sK2))).
% 0.21/0.54  
% 0.21/0.54  tff(u943,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~v2_funct_1(X2) | (k2_relset_1(X0,X1,X2) != X1) | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))))).
% 0.21/0.54  
% 0.21/0.54  tff(u942,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~v2_funct_1(X2) | (k2_relset_1(X0,X1,X2) != X1) | v1_funct_2(k2_funct_1(X2),X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))))).
% 0.21/0.54  
% 0.21/0.54  tff(u941,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~v2_funct_1(X2) | (k2_relset_1(X0,X1,X2) != X1) | v1_funct_1(k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))))).
% 0.21/0.54  
% 0.21/0.54  tff(u940,axiom,
% 0.21/0.54      (![X0] : ((~v2_funct_1(X0) | (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u939,axiom,
% 0.21/0.54      (![X0] : ((~v2_funct_1(X0) | (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u938,axiom,
% 0.21/0.54      (![X0] : (v5_relat_1(k1_xboole_0,X0)))).
% 0.21/0.54  
% 0.21/0.54  tff(u937,negated_conjecture,
% 0.21/0.54      ((~v5_relat_1(sK2,u1_struct_0(sK1))) | v5_relat_1(sK2,u1_struct_0(sK1)))).
% 0.21/0.54  
% 0.21/0.54  tff(u936,negated_conjecture,
% 0.21/0.54      ((~v5_relat_1(sK2,k2_relat_1(sK2))) | v5_relat_1(sK2,k2_relat_1(sK2)))).
% 0.21/0.54  
% 0.21/0.54  tff(u935,axiom,
% 0.21/0.54      (![X1, X0] : ((~v1_partfun1(X1,X0) | (k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))))).
% 0.21/0.54  
% 0.21/0.54  % (29609)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.54  tff(u934,negated_conjecture,
% 0.21/0.54      ((~(![X1, X0] : ((~v1_partfun1(sK2,X0) | v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))))) | (![X1, X0] : ((~v1_partfun1(sK2,X0) | v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))))).
% 0.21/0.54  
% 0.21/0.54  tff(u933,axiom,
% 0.21/0.54      (![X1] : ((v1_partfun1(X1,k1_relat_1(X1)) | ~v4_relat_1(X1,k1_relat_1(X1)) | ~v1_relat_1(X1))))).
% 0.21/0.54  
% 0.21/0.54  tff(u932,negated_conjecture,
% 0.21/0.54      ((~v1_partfun1(sK2,k1_relat_1(sK2))) | v1_partfun1(sK2,k1_relat_1(sK2)))).
% 0.21/0.54  
% 0.21/0.54  tff(u931,axiom,
% 0.21/0.54      (![X1, X2] : ((~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | (k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X2,X1)) | ~v1_funct_1(X2))))).
% 0.21/0.54  
% 0.21/0.54  tff(u930,axiom,
% 0.21/0.54      (![X1, X2] : ((~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_partfun1(X2,k1_xboole_0) | ~v1_funct_1(X2))))).
% 0.21/0.54  
% 0.21/0.54  tff(u929,negated_conjecture,
% 0.21/0.54      ((~(![X1, X0] : ((~v1_funct_2(sK2,X1,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | (k1_xboole_0 = X0) | v1_partfun1(sK2,X1))))) | (![X1, X0] : ((~v1_funct_2(sK2,X1,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | (k1_xboole_0 = X0) | v1_partfun1(sK2,X1)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u928,negated_conjecture,
% 0.21/0.54      ((~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))) | v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)))).
% 0.21/0.54  
% 0.21/0.54  tff(u927,negated_conjecture,
% 0.21/0.54      ((~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))) | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)))).
% 0.21/0.54  
% 0.21/0.54  tff(u926,negated_conjecture,
% 0.21/0.54      ((~~v2_struct_0(sK0)) | ~v2_struct_0(sK0))).
% 0.21/0.54  
% 0.21/0.54  tff(u925,negated_conjecture,
% 0.21/0.54      ((~~v2_struct_0(sK1)) | ~v2_struct_0(sK1))).
% 0.21/0.54  
% 0.21/0.54  tff(u924,axiom,
% 0.21/0.54      (![X0] : ((~v2_struct_0(sK4(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u923,negated_conjecture,
% 0.21/0.54      ((~l1_struct_0(sK0)) | l1_struct_0(sK0))).
% 0.21/0.54  
% 0.21/0.54  tff(u922,negated_conjecture,
% 0.21/0.54      ((~l1_struct_0(sK1)) | l1_struct_0(sK1))).
% 0.21/0.54  
% 0.21/0.54  tff(u921,axiom,
% 0.21/0.54      (![X0] : ((l1_struct_0(sK4(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u920,axiom,
% 0.21/0.54      (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u919,negated_conjecture,
% 0.21/0.54      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 0.21/0.54  
% 0.21/0.54  tff(u918,negated_conjecture,
% 0.21/0.54      ((~l1_orders_2(sK1)) | l1_orders_2(sK1))).
% 0.21/0.54  
% 0.21/0.54  tff(u917,axiom,
% 0.21/0.54      (![X0] : ((l1_orders_2(sK4(X0)) | v2_struct_0(X0) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u916,axiom,
% 0.21/0.54      (![X1, X0] : ((~m1_yellow_0(X0,X1) | (u1_orders_2(X1) = u1_orders_2(X0)) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X1))))).
% 0.21/0.54  
% 0.21/0.54  tff(u915,axiom,
% 0.21/0.54      (![X1, X0] : ((~m1_yellow_0(X0,X1) | (u1_struct_0(X0) = u1_struct_0(X1)) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X1))))).
% 0.21/0.54  
% 0.21/0.54  tff(u914,axiom,
% 0.21/0.54      (![X1, X0] : ((~m1_yellow_0(X1,X0) | l1_orders_2(X1) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u913,axiom,
% 0.21/0.54      (![X0] : ((~m1_yellow_0(X0,sK4(X0)) | (u1_orders_2(X0) = u1_orders_2(sK4(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u912,axiom,
% 0.21/0.54      (![X0] : ((~m1_yellow_0(X0,sK4(X0)) | (u1_struct_0(X0) = u1_struct_0(sK4(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u911,negated_conjecture,
% 0.21/0.54      ((~(![X0] : ((~m1_yellow_0(sK0,X0) | ~l1_orders_2(X0) | ~r1_tarski(u1_struct_0(X0),k1_relat_1(sK2)) | (u1_struct_0(X0) = k1_relat_1(sK2)))))) | (![X0] : ((~m1_yellow_0(sK0,X0) | ~l1_orders_2(X0) | ~r1_tarski(u1_struct_0(X0),k1_relat_1(sK2)) | (u1_struct_0(X0) = k1_relat_1(sK2))))))).
% 0.21/0.54  
% 0.21/0.54  tff(u910,negated_conjecture,
% 0.21/0.54      ((~(![X3] : ((~m1_yellow_0(sK0,X3) | r1_tarski(k1_relat_1(sK2),u1_struct_0(X3)) | ~l1_orders_2(X3))))) | (![X3] : ((~m1_yellow_0(sK0,X3) | r1_tarski(k1_relat_1(sK2),u1_struct_0(X3)) | ~l1_orders_2(X3)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u909,axiom,
% 0.21/0.54      (![X0] : ((m1_yellow_0(sK4(X0),X0) | ~l1_orders_2(X0) | v2_struct_0(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u908,axiom,
% 0.21/0.54      (![X2] : ((m1_yellow_0(X2,X2) | ~l1_orders_2(X2))))).
% 0.21/0.54  
% 0.21/0.54  tff(u907,axiom,
% 0.21/0.54      (![X0] : ((v1_orders_2(sK4(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u906,axiom,
% 0.21/0.54      (![X0] : ((v4_yellow_0(sK4(X0),X0) | ~l1_orders_2(X0) | v2_struct_0(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u905,negated_conjecture,
% 0.21/0.54      ((~v23_waybel_0(sK2,sK0,sK1)) | v23_waybel_0(sK2,sK0,sK1))).
% 0.21/0.54  
% 0.21/0.54  tff(u904,axiom,
% 0.21/0.54      (![X1, X0] : ((~sP7(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))))))).
% 0.21/0.54  
% 0.21/0.54  tff(u903,negated_conjecture,
% 0.21/0.54      ((~(![X1, X0, X2] : ((~sP7(k7_relat_1(sK2,X0),X2) | m1_subset_1(k7_relat_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k9_relat_1(sK2,X0),X1))))) | (![X1, X0, X2] : ((~sP7(k7_relat_1(sK2,X0),X2) | m1_subset_1(k7_relat_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k9_relat_1(sK2,X0),X1)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u902,axiom,
% 0.21/0.54      (![X0] : (sP7(k1_xboole_0,X0)))).
% 0.21/0.54  
% 0.21/0.54  tff(u901,negated_conjecture,
% 0.21/0.54      ((~sP7(sK2,k1_relat_1(sK2))) | sP7(sK2,k1_relat_1(sK2)))).
% 0.21/0.54  
% 0.21/0.54  % (29590)# SZS output end Saturation.
% 0.21/0.54  % (29590)------------------------------
% 0.21/0.54  % (29590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (29590)Termination reason: Satisfiable
% 0.21/0.54  
% 0.21/0.54  % (29590)Memory used [KB]: 6652
% 0.21/0.54  % (29590)Time elapsed: 0.105 s
% 0.21/0.54  % (29590)------------------------------
% 0.21/0.54  % (29590)------------------------------
% 0.21/0.55  % (29587)Success in time 0.188 s
%------------------------------------------------------------------------------
