%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : orders_2__t62_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:22 EDT 2019

% Result     : Theorem 51.40s
% Output     : Refutation 51.40s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 264 expanded)
%              Number of leaves         :   13 (  47 expanded)
%              Depth                    :   25
%              Number of atoms          :  417 (1466 expanded)
%              Number of equality atoms :   45 (  48 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7673,plain,(
    $false ),
    inference(subsumption_resolution,[],[f7672,f87])).

fof(f87,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X1,k3_orders_2(X0,X2,X1))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X1,k3_orders_2(X0,X2,X1))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ r2_hidden(X1,k3_orders_2(X0,X2,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ r2_hidden(X1,k3_orders_2(X0,X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t62_orders_2.p',t62_orders_2)).

fof(f7672,plain,(
    ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f7671,f90])).

fof(f90,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t62_orders_2.p',dt_l1_orders_2)).

fof(f7671,plain,(
    ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f7666,f83])).

fof(f83,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f7666,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f7665,f94])).

fof(f94,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t62_orders_2.p',fc2_struct_0)).

fof(f7665,plain,(
    v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f7664,f82])).

fof(f82,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f7664,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f7663,f138])).

fof(f138,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f137])).

fof(f137,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t62_orders_2.p',d1_tarski)).

fof(f7663,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(superposition,[],[f7658,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t62_orders_2.p',redefinition_k6_domain_1)).

fof(f7658,plain,(
    ~ r2_hidden(sK1,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f7645,f268])).

fof(f268,plain,(
    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f267,f87])).

fof(f267,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f255,f90])).

fof(f255,plain,
    ( ~ l1_struct_0(sK0)
    | m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f250,f83])).

fof(f250,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f198,f94])).

fof(f198,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f82,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t62_orders_2.p',dt_k6_domain_1)).

fof(f7645,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f7641,f1635])).

fof(f1635,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k2_orders_2(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f1634])).

fof(f1634,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k2_orders_2(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f1630,f160])).

fof(f160,plain,(
    ! [X0] :
      ( k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f159,f83])).

fof(f159,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f158,f86])).

fof(f86,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f158,plain,(
    ! [X0] :
      ( ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f157,f85])).

fof(f85,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f157,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f146,f84])).

fof(f84,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f146,plain,(
    ! [X0] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) ) ),
    inference(resolution,[],[f87,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t62_orders_2.p',d13_orders_2)).

fof(f1630,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f1629])).

fof(f1629,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1)) ) ),
    inference(superposition,[],[f591,f185])).

fof(f185,plain,(
    ! [X12,X11] :
      ( sK6(X12,sK0,X11) = X12
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X12,a_2_1_orders_2(sK0,X11)) ) ),
    inference(subsumption_resolution,[],[f184,f83])).

fof(f184,plain,(
    ! [X12,X11] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK6(X12,sK0,X11) = X12
      | ~ r2_hidden(X12,a_2_1_orders_2(sK0,X11)) ) ),
    inference(subsumption_resolution,[],[f183,f86])).

fof(f183,plain,(
    ! [X12,X11] :
      ( ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK6(X12,sK0,X11) = X12
      | ~ r2_hidden(X12,a_2_1_orders_2(sK0,X11)) ) ),
    inference(subsumption_resolution,[],[f182,f85])).

fof(f182,plain,(
    ! [X12,X11] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK6(X12,sK0,X11) = X12
      | ~ r2_hidden(X12,a_2_1_orders_2(sK0,X11)) ) ),
    inference(subsumption_resolution,[],[f152,f84])).

fof(f152,plain,(
    ! [X12,X11] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK6(X12,sK0,X11) = X12
      | ~ r2_hidden(X12,a_2_1_orders_2(sK0,X11)) ) ),
    inference(resolution,[],[f87,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | sK6(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X3,X4) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t62_orders_2.p',fraenkel_a_2_1_orders_2)).

fof(f591,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,sK0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f588,f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t62_orders_2.p',t4_subset)).

fof(f588,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,sK0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(sK6(X0,sK0,X1),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f177,f156])).

fof(f156,plain,(
    ! [X19] :
      ( ~ r2_orders_2(sK0,X19,X19)
      | ~ m1_subset_1(X19,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f87,f145])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r2_orders_2(X1,X0,X0) ) ),
    inference(condensation,[],[f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_orders_2(X0,X1,X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => ~ r2_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t62_orders_2.p',irreflexivity_r2_orders_2)).

fof(f177,plain,(
    ! [X6,X8,X7] :
      ( r2_orders_2(sK0,sK6(X8,sK0,X6),X7)
      | ~ r2_hidden(X7,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X8,a_2_1_orders_2(sK0,X6)) ) ),
    inference(subsumption_resolution,[],[f176,f126])).

fof(f176,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ r2_hidden(X7,X6)
      | r2_orders_2(sK0,sK6(X8,sK0,X6),X7)
      | ~ r2_hidden(X8,a_2_1_orders_2(sK0,X6)) ) ),
    inference(subsumption_resolution,[],[f175,f83])).

fof(f175,plain,(
    ! [X6,X8,X7] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ r2_hidden(X7,X6)
      | r2_orders_2(sK0,sK6(X8,sK0,X6),X7)
      | ~ r2_hidden(X8,a_2_1_orders_2(sK0,X6)) ) ),
    inference(subsumption_resolution,[],[f174,f86])).

fof(f174,plain,(
    ! [X6,X8,X7] :
      ( ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ r2_hidden(X7,X6)
      | r2_orders_2(sK0,sK6(X8,sK0,X6),X7)
      | ~ r2_hidden(X8,a_2_1_orders_2(sK0,X6)) ) ),
    inference(subsumption_resolution,[],[f173,f85])).

fof(f173,plain,(
    ! [X6,X8,X7] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ r2_hidden(X7,X6)
      | r2_orders_2(sK0,sK6(X8,sK0,X6),X7)
      | ~ r2_hidden(X8,a_2_1_orders_2(sK0,X6)) ) ),
    inference(subsumption_resolution,[],[f150,f84])).

fof(f150,plain,(
    ! [X6,X8,X7] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ r2_hidden(X7,X6)
      | r2_orders_2(sK0,sK6(X8,sK0,X6),X7)
      | ~ r2_hidden(X8,a_2_1_orders_2(sK0,X6)) ) ),
    inference(resolution,[],[f87,f122])).

fof(f122,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ r2_hidden(X4,X2)
      | r2_orders_2(X1,sK6(X0,X1,X2),X4)
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f7641,plain,(
    r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f2618,f81])).

fof(f81,plain,(
    r2_hidden(sK1,k3_orders_2(sK0,sK2,sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f2618,plain,(
    ! [X20] :
      ( ~ r2_hidden(X20,k3_orders_2(sK0,sK2,sK1))
      | r2_hidden(X20,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ) ),
    inference(superposition,[],[f144,f2253])).

fof(f2253,plain,(
    k3_orders_2(sK0,sK2,sK1) = k3_xboole_0(k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),sK2) ),
    inference(subsumption_resolution,[],[f2224,f80])).

fof(f80,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f2224,plain,
    ( k3_orders_2(sK0,sK2,sK1) = k3_xboole_0(k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f804,f202])).

fof(f202,plain,(
    ! [X2] : k3_xboole_0(X2,sK2) = k9_subset_1(u1_struct_0(sK0),X2,sK2) ),
    inference(resolution,[],[f80,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t62_orders_2.p',redefinition_k9_subset_1)).

fof(f804,plain,(
    ! [X20] :
      ( k3_orders_2(sK0,X20,sK1) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),X20)
      | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f164,f82])).

fof(f164,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k3_orders_2(sK0,X1,X2) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2)),X1) ) ),
    inference(subsumption_resolution,[],[f163,f83])).

fof(f163,plain,(
    ! [X2,X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k3_orders_2(sK0,X1,X2) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2)),X1) ) ),
    inference(subsumption_resolution,[],[f162,f86])).

fof(f162,plain,(
    ! [X2,X1] :
      ( ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k3_orders_2(sK0,X1,X2) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2)),X1) ) ),
    inference(subsumption_resolution,[],[f161,f85])).

fof(f161,plain,(
    ! [X2,X1] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k3_orders_2(sK0,X1,X2) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2)),X1) ) ),
    inference(subsumption_resolution,[],[f147,f84])).

fof(f147,plain,(
    ! [X2,X1] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k3_orders_2(sK0,X1,X2) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2)),X1) ) ),
    inference(resolution,[],[f87,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k3_orders_2(X0,X1,X2) = k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_orders_2(X0,X1,X2) = k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_orders_2(X0,X1,X2) = k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k3_orders_2(X0,X1,X2) = k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t62_orders_2.p',d14_orders_2)).

fof(f144,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f130])).

fof(f130,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t62_orders_2.p',d4_xboole_0)).
%------------------------------------------------------------------------------
