%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:37 EST 2020

% Result     : CounterSatisfiable 1.66s
% Output     : Saturation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   56 (  56 expanded)
%              Number of leaves         :   56 (  56 expanded)
%              Depth                    :    0
%              Number of atoms          :  195 ( 195 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u280,negated_conjecture,
    ( ~ ( k9_tmap_1(sK0,sK1) != k3_struct_0(sK0) )
    | k9_tmap_1(sK0,sK1) != k3_struct_0(sK0) )).

tff(u279,negated_conjecture,(
    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) )).

tff(u278,negated_conjecture,(
    k7_tmap_1(sK0,u1_struct_0(sK1)) = k6_partfun1(u1_struct_0(sK0)) )).

tff(u277,axiom,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) )).

tff(u276,negated_conjecture,(
    l1_pre_topc(sK0) )).

tff(u275,negated_conjecture,(
    l1_pre_topc(k8_tmap_1(sK0,sK1)) )).

tff(u274,negated_conjecture,(
    l1_struct_0(sK0) )).

tff(u273,negated_conjecture,(
    l1_struct_0(k8_tmap_1(sK0,sK1)) )).

tff(u272,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u271,negated_conjecture,(
    ~ v2_struct_0(sK1) )).

tff(u270,axiom,(
    ! [X1,X0] :
      ( ~ v2_struct_0(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u269,negated_conjecture,
    ( ~ ~ v2_struct_0(k8_tmap_1(sK0,sK1))
    | ~ v2_struct_0(k8_tmap_1(sK0,sK1)) )).

tff(u268,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u267,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0)) )).

tff(u266,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1))) )).

tff(u265,negated_conjecture,(
    v1_funct_1(k3_struct_0(sK0)) )).

tff(u264,negated_conjecture,
    ( ~ v1_funct_1(k3_struct_0(k8_tmap_1(sK0,sK1)))
    | v1_funct_1(k3_struct_0(k8_tmap_1(sK0,sK1))) )).

tff(u263,negated_conjecture,(
    v1_funct_1(k9_tmap_1(sK0,sK1)) )).

tff(u262,negated_conjecture,(
    v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0)) )).

tff(u261,negated_conjecture,(
    v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) )).

tff(u260,negated_conjecture,
    ( ~ v1_funct_2(k3_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | v1_funct_2(k3_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(k8_tmap_1(sK0,sK1))) )).

tff(u259,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u258,axiom,(
    ! [X1,X3,X5,X0,X2] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | r1_funct_2(X0,X1,X2,X3,X5,X5)
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X5,X0,X1)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) )).

tff(u257,axiom,(
    ! [X3,X0,X2] :
      ( ~ m1_subset_1(X3,u1_struct_0(X2))
      | r1_tmap_1(X2,k6_tmap_1(X0,u1_struct_0(X2)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u256,negated_conjecture,
    ( ~ ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

tff(u255,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | v1_xboole_0(X1)
          | ~ v1_funct_2(k9_tmap_1(sK0,sK1),X0,X1)
          | r1_funct_2(X0,X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1)) )
    | ! [X1,X0] :
        ( ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1)
        | ~ v1_funct_2(k9_tmap_1(sK0,sK1),X0,X1)
        | r1_funct_2(X0,X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1)) ) )).

tff(u254,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK1)) )).

tff(u253,negated_conjecture,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u252,negated_conjecture,(
    m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) )).

tff(u251,axiom,(
    ! [X1,X3,X5,X0,X2,X4] :
      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
      | X4 = X5
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) )).

tff(u250,negated_conjecture,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k3_struct_0(sK0)) )).

tff(u249,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ ! [X1,X0] :
          ( ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | v1_xboole_0(X1)
          | ~ v1_funct_2(k9_tmap_1(sK0,sK1),X0,X1)
          | r1_funct_2(X0,X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1)) )
    | r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1)) )).

tff(u248,axiom,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
      | v2_struct_0(X0) ) )).

tff(u247,axiom,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_funct_1(k3_struct_0(X0))
      | v2_struct_0(X0) ) )).

tff(u246,negated_conjecture,(
    v2_pre_topc(sK0) )).

tff(u245,negated_conjecture,(
    v2_pre_topc(k8_tmap_1(sK0,sK1)) )).

tff(u244,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) )).

tff(u243,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u242,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u241,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u240,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u239,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_funct_1(k9_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u238,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u237,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u236,negated_conjecture,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X0,X1)
      | k8_tmap_1(sK0,sK1) = k8_tmap_1(X1,X0)
      | u1_struct_0(X0) = sK3(X1,X0,k8_tmap_1(sK0,sK1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) )).

tff(u235,negated_conjecture,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | k8_tmap_1(X0,X1) = k8_tmap_1(sK0,sK1)
      | m1_subset_1(sK3(X0,X1,k8_tmap_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u234,negated_conjecture,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | k8_tmap_1(X0,X1) = k8_tmap_1(sK0,sK1)
      | k8_tmap_1(sK0,sK1) != k6_tmap_1(X0,sK3(X0,X1,k8_tmap_1(sK0,sK1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u233,negated_conjecture,(
    ! [X0] :
      ( ~ m1_pre_topc(sK1,X0)
      | r1_tmap_1(sK1,k6_tmap_1(X0,u1_struct_0(sK1)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK1)),k7_tmap_1(X0,u1_struct_0(sK1)),sK1),sK2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u232,negated_conjecture,(
    m1_pre_topc(sK1,sK0) )).

tff(u231,axiom,(
    ! [X1,X0,X2] :
      ( ~ v1_pre_topc(X2)
      | k6_tmap_1(X0,sK3(X0,X1,X2)) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | k8_tmap_1(X0,X1) = X2
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u230,axiom,(
    ! [X1,X0,X2] :
      ( ~ v1_pre_topc(X2)
      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | k8_tmap_1(X0,X1) = X2
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u229,axiom,(
    ! [X1,X0,X2] :
      ( ~ v1_pre_topc(X2)
      | u1_struct_0(X1) = sK3(X0,X1,X2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | k8_tmap_1(X0,X1) = X2
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u228,axiom,(
    ! [X1,X0] :
      ( ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) )).

tff(u227,negated_conjecture,(
    v1_pre_topc(k8_tmap_1(sK0,sK1)) )).

tff(u226,negated_conjecture,(
    ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK2) )).

tff(u225,negated_conjecture,(
    r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),sK2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:55:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (28094)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.52  % (28086)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.52  % (28086)Refutation not found, incomplete strategy% (28086)------------------------------
% 0.22/0.52  % (28086)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (28086)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (28086)Memory used [KB]: 1663
% 0.22/0.52  % (28086)Time elapsed: 0.009 s
% 0.22/0.52  % (28086)------------------------------
% 0.22/0.52  % (28086)------------------------------
% 0.22/0.53  % (28091)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.53  % (28099)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.56  % (28082)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.57  % (28089)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.66/0.58  % (28097)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.66/0.58  % (28080)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.66/0.58  % (28082)Refutation not found, incomplete strategy% (28082)------------------------------
% 1.66/0.58  % (28082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.58  % (28082)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.58  
% 1.66/0.58  % (28082)Memory used [KB]: 6268
% 1.66/0.58  % (28082)Time elapsed: 0.144 s
% 1.66/0.58  % (28082)------------------------------
% 1.66/0.58  % (28082)------------------------------
% 1.66/0.59  % (28080)Refutation not found, incomplete strategy% (28080)------------------------------
% 1.66/0.59  % (28080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.59  % (28080)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.59  
% 1.66/0.59  % (28080)Memory used [KB]: 10618
% 1.66/0.59  % (28080)Time elapsed: 0.144 s
% 1.66/0.59  % (28080)------------------------------
% 1.66/0.59  % (28080)------------------------------
% 1.66/0.59  % SZS status CounterSatisfiable for theBenchmark
% 1.84/0.60  % (28101)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.84/0.60  % (28089)# SZS output start Saturation.
% 1.84/0.60  tff(u280,negated_conjecture,
% 1.84/0.60      ((~(k9_tmap_1(sK0,sK1) != k3_struct_0(sK0))) | (k9_tmap_1(sK0,sK1) != k3_struct_0(sK0)))).
% 1.84/0.60  
% 1.84/0.60  tff(u279,negated_conjecture,
% 1.84/0.60      (k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)))).
% 1.84/0.60  
% 1.84/0.60  tff(u278,negated_conjecture,
% 1.84/0.60      (k7_tmap_1(sK0,u1_struct_0(sK1)) = k6_partfun1(u1_struct_0(sK0)))).
% 1.84/0.60  
% 1.84/0.60  tff(u277,axiom,
% 1.84/0.60      (![X0] : ((~l1_pre_topc(X0) | l1_struct_0(X0))))).
% 1.84/0.60  
% 1.84/0.60  tff(u276,negated_conjecture,
% 1.84/0.60      l1_pre_topc(sK0)).
% 1.84/0.60  
% 1.84/0.60  tff(u275,negated_conjecture,
% 1.84/0.60      l1_pre_topc(k8_tmap_1(sK0,sK1))).
% 1.84/0.60  
% 1.84/0.60  tff(u274,negated_conjecture,
% 1.84/0.60      l1_struct_0(sK0)).
% 1.84/0.60  
% 1.84/0.60  tff(u273,negated_conjecture,
% 1.84/0.60      l1_struct_0(k8_tmap_1(sK0,sK1))).
% 1.84/0.60  
% 1.84/0.60  tff(u272,negated_conjecture,
% 1.84/0.60      ~v2_struct_0(sK0)).
% 1.84/0.60  
% 1.84/0.60  tff(u271,negated_conjecture,
% 1.84/0.60      ~v2_struct_0(sK1)).
% 1.84/0.60  
% 1.84/0.60  tff(u270,axiom,
% 1.84/0.60      (![X1, X0] : ((~v2_struct_0(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 1.84/0.60  
% 1.84/0.60  tff(u269,negated_conjecture,
% 1.84/0.60      ((~~v2_struct_0(k8_tmap_1(sK0,sK1))) | ~v2_struct_0(k8_tmap_1(sK0,sK1)))).
% 1.84/0.60  
% 1.84/0.60  tff(u268,axiom,
% 1.84/0.60      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 1.84/0.60  
% 1.84/0.60  tff(u267,negated_conjecture,
% 1.84/0.60      ((~~v1_xboole_0(u1_struct_0(sK0))) | ~v1_xboole_0(u1_struct_0(sK0)))).
% 1.84/0.60  
% 1.84/0.60  tff(u266,negated_conjecture,
% 1.84/0.60      ((~~v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1)))) | ~v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1))))).
% 1.84/0.60  
% 1.84/0.60  tff(u265,negated_conjecture,
% 1.84/0.60      v1_funct_1(k3_struct_0(sK0))).
% 1.84/0.60  
% 1.84/0.60  tff(u264,negated_conjecture,
% 1.84/0.60      ((~v1_funct_1(k3_struct_0(k8_tmap_1(sK0,sK1)))) | v1_funct_1(k3_struct_0(k8_tmap_1(sK0,sK1))))).
% 1.84/0.60  
% 1.84/0.60  tff(u263,negated_conjecture,
% 1.84/0.60      v1_funct_1(k9_tmap_1(sK0,sK1))).
% 1.84/0.60  
% 1.84/0.60  tff(u262,negated_conjecture,
% 1.84/0.60      v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))).
% 1.84/0.60  
% 1.84/0.60  tff(u261,negated_conjecture,
% 1.84/0.60      v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))).
% 1.84/0.60  
% 1.84/0.60  tff(u260,negated_conjecture,
% 1.84/0.60      ((~v1_funct_2(k3_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(k8_tmap_1(sK0,sK1)))) | v1_funct_2(k3_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(k8_tmap_1(sK0,sK1))))).
% 1.84/0.60  
% 1.84/0.60  tff(u259,axiom,
% 1.84/0.60      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 1.84/0.60  
% 1.84/0.60  tff(u258,axiom,
% 1.84/0.60      (![X1, X3, X5, X0, X2] : ((~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | r1_funct_2(X0,X1,X2,X3,X5,X5) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | v1_xboole_0(X3) | v1_xboole_0(X1))))).
% 1.84/0.60  
% 1.84/0.60  tff(u257,axiom,
% 1.84/0.60      (![X3, X0, X2] : ((~m1_subset_1(X3,u1_struct_0(X2)) | r1_tmap_1(X2,k6_tmap_1(X0,u1_struct_0(X2)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 1.84/0.60  
% 1.84/0.60  tff(u256,negated_conjecture,
% 1.84/0.60      ((~~m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) | ~m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))).
% 1.84/0.60  
% 1.84/0.60  tff(u255,negated_conjecture,
% 1.84/0.60      ((~(![X1, X0] : ((~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(k9_tmap_1(sK0,sK1),X0,X1) | r1_funct_2(X0,X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1)))))) | (![X1, X0] : ((~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(k9_tmap_1(sK0,sK1),X0,X1) | r1_funct_2(X0,X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1))))))).
% 1.84/0.60  
% 1.84/0.60  tff(u254,negated_conjecture,
% 1.84/0.60      m1_subset_1(sK2,u1_struct_0(sK1))).
% 1.84/0.60  
% 1.84/0.60  tff(u253,negated_conjecture,
% 1.84/0.60      m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.84/0.60  
% 1.84/0.60  tff(u252,negated_conjecture,
% 1.84/0.60      m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))).
% 1.84/0.60  
% 1.84/0.60  tff(u251,axiom,
% 1.84/0.60      (![X1, X3, X5, X0, X2, X4] : ((~r1_funct_2(X0,X1,X2,X3,X4,X5) | (X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))))).
% 1.84/0.60  
% 1.84/0.60  tff(u250,negated_conjecture,
% 1.84/0.60      r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k3_struct_0(sK0))).
% 1.84/0.60  
% 1.84/0.60  tff(u249,negated_conjecture,
% 1.84/0.60      ((~~v1_xboole_0(u1_struct_0(k8_tmap_1(sK0,sK1)))) | (~(![X1, X0] : ((~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(k9_tmap_1(sK0,sK1),X0,X1) | r1_funct_2(X0,X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1)))))) | r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1)))).
% 1.84/0.60  
% 1.84/0.60  tff(u248,axiom,
% 1.84/0.60      (![X0] : ((~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0)) | v2_struct_0(X0))))).
% 1.84/0.60  
% 1.84/0.60  tff(u247,axiom,
% 1.84/0.60      (![X0] : ((~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_funct_1(k3_struct_0(X0)) | v2_struct_0(X0))))).
% 1.84/0.60  
% 1.84/0.60  tff(u246,negated_conjecture,
% 1.84/0.60      v2_pre_topc(sK0)).
% 1.84/0.60  
% 1.84/0.60  tff(u245,negated_conjecture,
% 1.84/0.60      v2_pre_topc(k8_tmap_1(sK0,sK1))).
% 1.84/0.60  
% 1.84/0.60  tff(u244,axiom,
% 1.84/0.60      (![X1, X0] : ((~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))))).
% 1.84/0.60  
% 1.84/0.60  tff(u243,axiom,
% 1.84/0.60      (![X1, X0] : ((~m1_pre_topc(X1,X0) | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0)) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 1.84/0.60  
% 1.84/0.60  tff(u242,axiom,
% 1.84/0.60      (![X1, X0] : ((~m1_pre_topc(X1,X0) | v1_pre_topc(k8_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 1.84/0.60  
% 1.84/0.60  tff(u241,axiom,
% 1.84/0.60      (![X1, X0] : ((~m1_pre_topc(X1,X0) | v2_pre_topc(k8_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 1.84/0.60  
% 1.84/0.60  tff(u240,axiom,
% 1.84/0.60      (![X1, X0] : ((~m1_pre_topc(X1,X0) | l1_pre_topc(k8_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 1.84/0.60  
% 1.84/0.60  tff(u239,axiom,
% 1.84/0.60      (![X1, X0] : ((~m1_pre_topc(X1,X0) | v1_funct_1(k9_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 1.84/0.60  
% 1.84/0.60  tff(u238,axiom,
% 1.84/0.60      (![X1, X0] : ((~m1_pre_topc(X1,X0) | v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 1.84/0.60  
% 1.84/0.60  tff(u237,axiom,
% 1.84/0.60      (![X1, X0] : ((~m1_pre_topc(X1,X0) | m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 1.84/0.60  
% 1.84/0.60  tff(u236,negated_conjecture,
% 1.84/0.60      (![X1, X0] : ((~m1_pre_topc(X0,X1) | (k8_tmap_1(sK0,sK1) = k8_tmap_1(X1,X0)) | (u1_struct_0(X0) = sK3(X1,X0,k8_tmap_1(sK0,sK1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))))).
% 1.84/0.60  
% 1.84/0.60  tff(u235,negated_conjecture,
% 1.84/0.60      (![X1, X0] : ((~m1_pre_topc(X1,X0) | (k8_tmap_1(X0,X1) = k8_tmap_1(sK0,sK1)) | m1_subset_1(sK3(X0,X1,k8_tmap_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 1.84/0.60  
% 1.84/0.60  tff(u234,negated_conjecture,
% 1.84/0.60      (![X1, X0] : ((~m1_pre_topc(X1,X0) | (k8_tmap_1(X0,X1) = k8_tmap_1(sK0,sK1)) | (k8_tmap_1(sK0,sK1) != k6_tmap_1(X0,sK3(X0,X1,k8_tmap_1(sK0,sK1)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 1.84/0.60  
% 1.84/0.60  tff(u233,negated_conjecture,
% 1.84/0.60      (![X0] : ((~m1_pre_topc(sK1,X0) | r1_tmap_1(sK1,k6_tmap_1(X0,u1_struct_0(sK1)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK1)),k7_tmap_1(X0,u1_struct_0(sK1)),sK1),sK2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 1.84/0.60  
% 1.84/0.60  tff(u232,negated_conjecture,
% 1.84/0.60      m1_pre_topc(sK1,sK0)).
% 1.84/0.60  
% 1.84/0.60  tff(u231,axiom,
% 1.84/0.60      (![X1, X0, X2] : ((~v1_pre_topc(X2) | (k6_tmap_1(X0,sK3(X0,X1,X2)) != X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | (k8_tmap_1(X0,X1) = X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 1.84/0.60  
% 1.84/0.60  tff(u230,axiom,
% 1.84/0.60      (![X1, X0, X2] : ((~v1_pre_topc(X2) | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | (k8_tmap_1(X0,X1) = X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 1.84/0.60  
% 1.84/0.60  tff(u229,axiom,
% 1.84/0.60      (![X1, X0, X2] : ((~v1_pre_topc(X2) | (u1_struct_0(X1) = sK3(X0,X1,X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | (k8_tmap_1(X0,X1) = X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 1.84/0.60  
% 1.84/0.60  tff(u228,axiom,
% 1.84/0.60      (![X1, X0] : ((~v1_pre_topc(k8_tmap_1(X0,X1)) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))))).
% 1.84/0.60  
% 1.84/0.60  tff(u227,negated_conjecture,
% 1.84/0.60      v1_pre_topc(k8_tmap_1(sK0,sK1))).
% 1.84/0.60  
% 1.84/0.60  tff(u226,negated_conjecture,
% 1.84/0.60      ~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK2)).
% 1.84/0.60  
% 1.84/0.60  tff(u225,negated_conjecture,
% 1.84/0.60      r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),sK2)).
% 1.84/0.60  
% 1.84/0.60  % (28089)# SZS output end Saturation.
% 1.84/0.60  % (28089)------------------------------
% 1.84/0.60  % (28089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.60  % (28089)Termination reason: Satisfiable
% 1.84/0.60  
% 1.84/0.60  % (28089)Memory used [KB]: 10746
% 1.84/0.60  % (28089)Time elapsed: 0.149 s
% 1.84/0.60  % (28089)------------------------------
% 1.84/0.60  % (28089)------------------------------
% 1.84/0.60  % (28078)Success in time 0.233 s
%------------------------------------------------------------------------------
