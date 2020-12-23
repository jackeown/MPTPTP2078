%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1475+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:21 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 448 expanded)
%              Number of leaves         :   10 ( 120 expanded)
%              Depth                    :   16
%              Number of atoms          :  115 ( 911 expanded)
%              Number of equality atoms :   55 ( 342 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3576,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3575,f2989])).

fof(f2989,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != k7_lattice3(k7_lattice3(sK0)) ),
    inference(cnf_transformation,[],[f2942])).

fof(f2942,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != k7_lattice3(k7_lattice3(sK0))
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f2836,f2941])).

fof(f2941,plain,
    ( ? [X0] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(X0))
        & l1_orders_2(X0) )
   => ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != k7_lattice3(k7_lattice3(sK0))
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2836,plain,(
    ? [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(X0))
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2832])).

fof(f2832,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0)) ) ),
    inference(negated_conjecture,[],[f2831])).

fof(f2831,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_lattice3)).

fof(f3575,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = k7_lattice3(k7_lattice3(sK0)) ),
    inference(forward_demodulation,[],[f3559,f3436])).

fof(f3436,plain,(
    u1_orders_2(sK0) = k4_relat_1(k4_relat_1(u1_orders_2(sK0))) ),
    inference(forward_demodulation,[],[f3405,f3194])).

fof(f3194,plain,(
    u1_orders_2(sK0) = k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_relat_1(u1_orders_2(sK0))) ),
    inference(forward_demodulation,[],[f3161,f3162])).

fof(f3162,plain,(
    k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)) = k4_relat_1(u1_orders_2(sK0)) ),
    inference(unit_resulting_resolution,[],[f3140,f3020])).

fof(f3020,plain,(
    ! [X2,X0,X1] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2859])).

fof(f2859,plain,(
    ! [X0,X1,X2] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1229])).

fof(f1229,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

fof(f3140,plain,(
    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f2988,f3009])).

fof(f3009,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2855])).

fof(f2855,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1905])).

fof(f1905,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f2988,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f2942])).

fof(f3161,plain,(
    u1_orders_2(sK0) = k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0))) ),
    inference(unit_resulting_resolution,[],[f3140,f3019])).

fof(f3019,plain,(
    ! [X2,X0,X1] :
      ( k3_relset_1(X0,X1,k3_relset_1(X0,X1,X2)) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2858])).

fof(f2858,plain,(
    ! [X0,X1,X2] :
      ( k3_relset_1(X0,X1,k3_relset_1(X0,X1,X2)) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1226])).

fof(f1226,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k3_relset_1(X0,X1,k3_relset_1(X0,X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_relset_1)).

fof(f3405,plain,(
    k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_relat_1(u1_orders_2(sK0))) = k4_relat_1(k4_relat_1(u1_orders_2(sK0))) ),
    inference(unit_resulting_resolution,[],[f3195,f3020])).

fof(f3195,plain,(
    m1_subset_1(k4_relat_1(u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f3160,f3162])).

fof(f3160,plain,(
    m1_subset_1(k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f3140,f3018])).

fof(f3018,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2857])).

fof(f2857,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1217])).

fof(f1217,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_relset_1)).

fof(f3559,plain,(
    k7_lattice3(k7_lattice3(sK0)) = g1_orders_2(u1_struct_0(sK0),k4_relat_1(k4_relat_1(u1_orders_2(sK0)))) ),
    inference(backward_demodulation,[],[f3509,f3539])).

fof(f3539,plain,(
    u1_orders_2(k7_lattice3(sK0)) = k4_relat_1(u1_orders_2(sK0)) ),
    inference(unit_resulting_resolution,[],[f3464,f3204])).

fof(f3204,plain,(
    ! [X6,X7] :
      ( k7_lattice3(sK0) != g1_orders_2(X6,X7)
      | k4_relat_1(u1_orders_2(sK0)) = X7 ) ),
    inference(subsumption_resolution,[],[f3202,f3195])).

fof(f3202,plain,(
    ! [X6,X7] :
      ( k7_lattice3(sK0) != g1_orders_2(X6,X7)
      | k4_relat_1(u1_orders_2(sK0)) = X7
      | ~ m1_subset_1(k4_relat_1(u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ) ),
    inference(superposition,[],[f3004,f3193])).

fof(f3193,plain,(
    k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),k4_relat_1(u1_orders_2(sK0))) ),
    inference(backward_demodulation,[],[f3139,f3162])).

fof(f3139,plain,(
    k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0))) ),
    inference(unit_resulting_resolution,[],[f2988,f2994])).

fof(f2994,plain,(
    ! [X0] :
      ( k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2840])).

fof(f2840,plain,(
    ! [X0] :
      ( k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2809])).

fof(f2809,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_lattice3)).

fof(f3004,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f2849])).

fof(f2849,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f1926])).

fof(f1926,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f3464,plain,(
    k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(k7_lattice3(sK0))) ),
    inference(backward_demodulation,[],[f3154,f3455])).

fof(f3455,plain,(
    u1_struct_0(sK0) = u1_struct_0(k7_lattice3(sK0)) ),
    inference(unit_resulting_resolution,[],[f3154,f3203])).

fof(f3203,plain,(
    ! [X2,X3] :
      ( g1_orders_2(X2,X3) != k7_lattice3(sK0)
      | u1_struct_0(sK0) = X2 ) ),
    inference(subsumption_resolution,[],[f3200,f3195])).

fof(f3200,plain,(
    ! [X2,X3] :
      ( g1_orders_2(X2,X3) != k7_lattice3(sK0)
      | u1_struct_0(sK0) = X2
      | ~ m1_subset_1(k4_relat_1(u1_orders_2(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ) ),
    inference(superposition,[],[f3003,f3193])).

fof(f3003,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f2849])).

fof(f3154,plain,(
    k7_lattice3(sK0) = g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) ),
    inference(unit_resulting_resolution,[],[f3137,f3138,f3007])).

fof(f3007,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2852])).

fof(f2852,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f2851])).

fof(f2851,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1859])).

fof(f1859,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(f3138,plain,(
    l1_orders_2(k7_lattice3(sK0)) ),
    inference(unit_resulting_resolution,[],[f2988,f2993])).

fof(f2993,plain,(
    ! [X0] :
      ( l1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2839])).

% (10670)Refutation not found, incomplete strategy% (10670)------------------------------
% (10670)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10670)Termination reason: Refutation not found, incomplete strategy

% (10670)Memory used [KB]: 10490
% (10670)Time elapsed: 0.164 s
% (10670)------------------------------
% (10670)------------------------------
fof(f2839,plain,(
    ! [X0] :
      ( ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2814])).

fof(f2814,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattice3)).

fof(f3137,plain,(
    v1_orders_2(k7_lattice3(sK0)) ),
    inference(unit_resulting_resolution,[],[f2988,f2992])).

fof(f2992,plain,(
    ! [X0] :
      ( v1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2839])).

fof(f3509,plain,(
    k7_lattice3(k7_lattice3(sK0)) = g1_orders_2(u1_struct_0(sK0),k4_relat_1(u1_orders_2(k7_lattice3(sK0)))) ),
    inference(backward_demodulation,[],[f3463,f3478])).

fof(f3478,plain,(
    k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(k7_lattice3(sK0))) = k4_relat_1(u1_orders_2(k7_lattice3(sK0))) ),
    inference(unit_resulting_resolution,[],[f3465,f3020])).

fof(f3465,plain,(
    m1_subset_1(u1_orders_2(k7_lattice3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(backward_demodulation,[],[f3155,f3455])).

fof(f3155,plain,(
    m1_subset_1(u1_orders_2(k7_lattice3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_lattice3(sK0)),u1_struct_0(k7_lattice3(sK0))))) ),
    inference(unit_resulting_resolution,[],[f3138,f3009])).

fof(f3463,plain,(
    k7_lattice3(k7_lattice3(sK0)) = g1_orders_2(u1_struct_0(sK0),k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(k7_lattice3(sK0)))) ),
    inference(backward_demodulation,[],[f3153,f3455])).

fof(f3153,plain,(
    k7_lattice3(k7_lattice3(sK0)) = g1_orders_2(u1_struct_0(k7_lattice3(sK0)),k3_relset_1(u1_struct_0(k7_lattice3(sK0)),u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0)))) ),
    inference(unit_resulting_resolution,[],[f3138,f2994])).
%------------------------------------------------------------------------------
