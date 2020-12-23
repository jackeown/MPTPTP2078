%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1914+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:37 EST 2020

% Result     : Theorem 9.46s
% Output     : Refutation 9.46s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 226 expanded)
%              Number of leaves         :    9 (  60 expanded)
%              Depth                    :   16
%              Number of atoms          :   96 ( 446 expanded)
%              Number of equality atoms :   35 ( 158 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17111,plain,(
    $false ),
    inference(subsumption_resolution,[],[f17110,f8302])).

fof(f8302,plain,(
    m1_subset_1(u1_orders_2(k7_lattice3(sK53)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_lattice3(sK53)),u1_struct_0(k7_lattice3(sK53))))) ),
    inference(resolution,[],[f8271,f6332])).

fof(f6332,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f4457])).

fof(f4457,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1905])).

fof(f1905,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f8271,plain,(
    l1_orders_2(k7_lattice3(sK53)) ),
    inference(forward_demodulation,[],[f8208,f6733])).

fof(f6733,plain,(
    k7_lattice3(sK53) = g1_orders_2(u1_struct_0(sK53),k4_relat_1(u1_orders_2(sK53))) ),
    inference(backward_demodulation,[],[f6554,f6697])).

fof(f6697,plain,(
    k3_relset_1(u1_struct_0(sK53),u1_struct_0(sK53),u1_orders_2(sK53)) = k4_relat_1(u1_orders_2(sK53)) ),
    inference(resolution,[],[f6564,f6327])).

fof(f6327,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f4453])).

fof(f4453,plain,(
    ! [X0,X1,X2] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1229])).

fof(f1229,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

fof(f6564,plain,(
    m1_subset_1(u1_orders_2(sK53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK53),u1_struct_0(sK53)))) ),
    inference(resolution,[],[f5197,f6332])).

fof(f5197,plain,(
    l1_orders_2(sK53) ),
    inference(cnf_transformation,[],[f4600])).

fof(f4600,plain,
    ( u1_struct_0(sK53) != u1_struct_0(k7_lattice3(sK53))
    & l1_orders_2(sK53) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK53])],[f3872,f4599])).

fof(f4599,plain,
    ( ? [X0] :
        ( u1_struct_0(X0) != u1_struct_0(k7_lattice3(X0))
        & l1_orders_2(X0) )
   => ( u1_struct_0(sK53) != u1_struct_0(k7_lattice3(sK53))
      & l1_orders_2(sK53) ) ),
    introduced(choice_axiom,[])).

fof(f3872,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != u1_struct_0(k7_lattice3(X0))
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3831])).

fof(f3831,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => u1_struct_0(X0) = u1_struct_0(k7_lattice3(X0)) ) ),
    inference(negated_conjecture,[],[f3830])).

fof(f3830,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => u1_struct_0(X0) = u1_struct_0(k7_lattice3(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_yellow_6)).

fof(f6554,plain,(
    k7_lattice3(sK53) = g1_orders_2(u1_struct_0(sK53),k3_relset_1(u1_struct_0(sK53),u1_struct_0(sK53),u1_orders_2(sK53))) ),
    inference(resolution,[],[f5197,f5258])).

fof(f5258,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) ) ),
    inference(cnf_transformation,[],[f3910])).

fof(f3910,plain,(
    ! [X0] :
      ( k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2827])).

fof(f2827,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_lattice3)).

fof(f8208,plain,(
    l1_orders_2(g1_orders_2(u1_struct_0(sK53),k4_relat_1(u1_orders_2(sK53)))) ),
    inference(resolution,[],[f6931,f5840])).

fof(f5840,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | l1_orders_2(g1_orders_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f4207])).

fof(f4207,plain,(
    ! [X0,X1] :
      ( ( l1_orders_2(g1_orders_2(X0,X1))
        & v1_orders_2(g1_orders_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f1886])).

fof(f1886,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ( l1_orders_2(g1_orders_2(X0,X1))
        & v1_orders_2(g1_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_orders_2)).

fof(f6931,plain,(
    m1_subset_1(k4_relat_1(u1_orders_2(sK53)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK53),u1_struct_0(sK53)))) ),
    inference(subsumption_resolution,[],[f6930,f6564])).

fof(f6930,plain,
    ( m1_subset_1(k4_relat_1(u1_orders_2(sK53)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK53),u1_struct_0(sK53))))
    | ~ m1_subset_1(u1_orders_2(sK53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK53),u1_struct_0(sK53)))) ),
    inference(superposition,[],[f6325,f6697])).

fof(f6325,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f4451])).

fof(f4451,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1217])).

fof(f1217,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_relset_1)).

fof(f17110,plain,(
    ~ m1_subset_1(u1_orders_2(k7_lattice3(sK53)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_lattice3(sK53)),u1_struct_0(k7_lattice3(sK53))))) ),
    inference(subsumption_resolution,[],[f17041,f5198])).

fof(f5198,plain,(
    u1_struct_0(sK53) != u1_struct_0(k7_lattice3(sK53)) ),
    inference(cnf_transformation,[],[f4600])).

fof(f17041,plain,
    ( u1_struct_0(sK53) = u1_struct_0(k7_lattice3(sK53))
    | ~ m1_subset_1(u1_orders_2(k7_lattice3(sK53)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_lattice3(sK53)),u1_struct_0(k7_lattice3(sK53))))) ),
    inference(trivial_inequality_removal,[],[f17034])).

fof(f17034,plain,
    ( k7_lattice3(sK53) != k7_lattice3(sK53)
    | u1_struct_0(sK53) = u1_struct_0(k7_lattice3(sK53))
    | ~ m1_subset_1(u1_orders_2(k7_lattice3(sK53)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_lattice3(sK53)),u1_struct_0(k7_lattice3(sK53))))) ),
    inference(superposition,[],[f6748,f8281])).

fof(f8281,plain,(
    k7_lattice3(sK53) = g1_orders_2(u1_struct_0(k7_lattice3(sK53)),u1_orders_2(k7_lattice3(sK53))) ),
    inference(subsumption_resolution,[],[f8280,f8271])).

fof(f8280,plain,
    ( k7_lattice3(sK53) = g1_orders_2(u1_struct_0(k7_lattice3(sK53)),u1_orders_2(k7_lattice3(sK53)))
    | ~ l1_orders_2(k7_lattice3(sK53)) ),
    inference(resolution,[],[f8270,f5867])).

fof(f5867,plain,(
    ! [X0] :
      ( ~ v1_orders_2(X0)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4220])).

fof(f4220,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f4219])).

fof(f4219,plain,(
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

fof(f8270,plain,(
    v1_orders_2(k7_lattice3(sK53)) ),
    inference(forward_demodulation,[],[f8207,f6733])).

fof(f8207,plain,(
    v1_orders_2(g1_orders_2(u1_struct_0(sK53),k4_relat_1(u1_orders_2(sK53)))) ),
    inference(resolution,[],[f6931,f5839])).

fof(f5839,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | v1_orders_2(g1_orders_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f4207])).

fof(f6748,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != k7_lattice3(sK53)
      | u1_struct_0(sK53) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(superposition,[],[f6305,f6733])).

fof(f6305,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f4427])).

fof(f4427,plain,(
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

% (14651)Time limit reached!
% (14651)------------------------------
% (14651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14651)Termination reason: Time limit
% (14651)Termination phase: Saturation

% (14651)Memory used [KB]: 25713
% (14651)Time elapsed: 1.100 s
% (14651)------------------------------
% (14651)------------------------------
%------------------------------------------------------------------------------
