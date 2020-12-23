%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1143+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:09 EST 2020

% Result     : Theorem 17.99s
% Output     : Refutation 17.99s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 458 expanded)
%              Number of leaves         :   13 (  88 expanded)
%              Depth                    :   17
%              Number of atoms          :  227 (1657 expanded)
%              Number of equality atoms :   13 (  48 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10316,plain,(
    $false ),
    inference(subsumption_resolution,[],[f10313,f3732])).

fof(f3732,plain,(
    r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f3731,f2503])).

fof(f2503,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f1897])).

fof(f1897,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f1896])).

fof(f1896,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1888])).

fof(f1888,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
              & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f1887])).

fof(f1887,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_orders_2)).

fof(f3731,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f3730,f2506])).

fof(f2506,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f1897])).

fof(f3730,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0)) ),
    inference(duplicate_literal_removal,[],[f3713])).

fof(f3713,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0)) ),
    inference(resolution,[],[f3629,f3248])).

fof(f3248,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2362])).

fof(f2362,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1868])).

fof(f1868,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

fof(f3629,plain,(
    r1_orders_2(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f3628,f2506])).

fof(f3628,plain,
    ( ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f3627,f2505])).

fof(f2505,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f1897])).

fof(f3627,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f3595,f2504])).

fof(f2504,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f1897])).

fof(f3595,plain,
    ( v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,sK1,sK1) ),
    inference(resolution,[],[f2503,f2579])).

fof(f2579,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X1) ) ),
    inference(cnf_transformation,[],[f1954])).

fof(f1954,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f1953])).

fof(f1953,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1880])).

fof(f1880,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

fof(f10313,plain,(
    ~ r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0)) ),
    inference(backward_demodulation,[],[f10027,f10176])).

fof(f10176,plain,(
    sK1 = sK115(u1_orders_2(sK0),k1_tarski(sK1)) ),
    inference(resolution,[],[f4914,f3493])).

fof(f3493,plain,(
    ! [X2,X0] :
      ( X0 = X2
      | ~ r2_hidden(X2,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f3111])).

fof(f3111,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f175])).

fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f4914,plain,(
    r2_hidden(sK115(u1_orders_2(sK0),k1_tarski(sK1)),k1_tarski(sK1)) ),
    inference(subsumption_resolution,[],[f4889,f4465])).

fof(f4465,plain,(
    v1_relat_1(u1_orders_2(sK0)) ),
    inference(resolution,[],[f3572,f2517])).

fof(f2517,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1910])).

fof(f1910,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f3572,plain,(
    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f2506,f2576])).

fof(f2576,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f1949])).

fof(f1949,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1872])).

fof(f1872,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f4889,plain,
    ( ~ v1_relat_1(u1_orders_2(sK0))
    | r2_hidden(sK115(u1_orders_2(sK0),k1_tarski(sK1)),k1_tarski(sK1)) ),
    inference(resolution,[],[f4862,f3244])).

fof(f3244,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK115(X0,X1),X1)
      | r7_relat_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f2361])).

fof(f2361,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r7_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1867])).

fof(f1867,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r7_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ~ ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_2)).

fof(f4862,plain,(
    ~ r7_relat_2(u1_orders_2(sK0),k1_tarski(sK1)) ),
    inference(forward_demodulation,[],[f4861,f4814])).

fof(f4814,plain,(
    k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    inference(resolution,[],[f3621,f3689])).

fof(f3689,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f3668,f2504])).

fof(f3668,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f3573,f2603])).

fof(f2603,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f1973])).

fof(f1973,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f1972])).

fof(f1972,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1795])).

fof(f1795,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f3573,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f2506,f2577])).

fof(f2577,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f1950])).

fof(f1950,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1871])).

fof(f1871,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f3621,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    inference(resolution,[],[f2503,f2567])).

fof(f2567,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f1944])).

fof(f1944,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f1943])).

fof(f1943,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1879])).

fof(f1879,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f4861,plain,(
    ~ r7_relat_2(u1_orders_2(sK0),k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f4856,f4249])).

fof(f4249,plain,(
    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f4127,f3689])).

fof(f4127,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f3622,f2541])).

fof(f2541,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f1926])).

fof(f1926,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f535])).

fof(f535,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f3622,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f2503,f2569])).

fof(f2569,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1947])).

fof(f1947,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f1946])).

fof(f1946,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f599])).

fof(f599,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f4856,plain,
    ( ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r7_relat_2(u1_orders_2(sK0),k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(backward_demodulation,[],[f3658,f4814])).

fof(f3658,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r7_relat_2(u1_orders_2(sK0),k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f3655,f2506])).

fof(f3655,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ r7_relat_2(u1_orders_2(sK0),k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(duplicate_literal_removal,[],[f3653])).

fof(f3653,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r7_relat_2(u1_orders_2(sK0),k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f2502,f2563])).

fof(f2563,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r7_relat_2(u1_orders_2(X0),X1)
      | v6_orders_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f1938])).

fof(f1938,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1863])).

fof(f1863,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_orders_2)).

fof(f2502,plain,
    ( ~ v6_orders_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f1897])).

fof(f10027,plain,(
    ~ r2_hidden(k4_tarski(sK1,sK115(u1_orders_2(sK0),k1_tarski(sK1))),u1_orders_2(sK0)) ),
    inference(backward_demodulation,[],[f4915,f9889])).

fof(f9889,plain,(
    sK1 = sK114(u1_orders_2(sK0),k1_tarski(sK1)) ),
    inference(resolution,[],[f4913,f3493])).

fof(f4913,plain,(
    r2_hidden(sK114(u1_orders_2(sK0),k1_tarski(sK1)),k1_tarski(sK1)) ),
    inference(subsumption_resolution,[],[f4888,f4465])).

fof(f4888,plain,
    ( ~ v1_relat_1(u1_orders_2(sK0))
    | r2_hidden(sK114(u1_orders_2(sK0),k1_tarski(sK1)),k1_tarski(sK1)) ),
    inference(resolution,[],[f4862,f3243])).

fof(f3243,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK114(X0,X1),X1)
      | r7_relat_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f2361])).

fof(f4915,plain,(
    ~ r2_hidden(k4_tarski(sK114(u1_orders_2(sK0),k1_tarski(sK1)),sK115(u1_orders_2(sK0),k1_tarski(sK1))),u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f4890,f4465])).

fof(f4890,plain,
    ( ~ v1_relat_1(u1_orders_2(sK0))
    | ~ r2_hidden(k4_tarski(sK114(u1_orders_2(sK0),k1_tarski(sK1)),sK115(u1_orders_2(sK0),k1_tarski(sK1))),u1_orders_2(sK0)) ),
    inference(resolution,[],[f4862,f3245])).

fof(f3245,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(sK114(X0,X1),sK115(X0,X1)),X0)
      | r7_relat_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f2361])).
%------------------------------------------------------------------------------
