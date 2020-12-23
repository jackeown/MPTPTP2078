%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:09 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 624 expanded)
%              Number of leaves         :   20 ( 216 expanded)
%              Depth                    :   22
%              Number of atoms          :  452 (3618 expanded)
%              Number of equality atoms :   42 ( 543 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1024,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1023,f55])).

fof(f55,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))
    & ~ r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)))
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_pre_topc(sK2)
    & v3_tdlat_3(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f18,f44,f43,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
                & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1))
              & ~ r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2)))
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_pre_topc(sK2)
      & v3_tdlat_3(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1))
            & ~ r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2)))
            & m1_subset_1(X2,u1_struct_0(sK2)) )
        & m1_subset_1(X1,u1_struct_0(sK2)) )
   => ( ? [X2] :
          ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3))
          & ~ r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2)))
          & m1_subset_1(X2,u1_struct_0(sK2)) )
      & m1_subset_1(sK3,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X2] :
        ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3))
        & ~ r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2)))
        & m1_subset_1(X2,u1_struct_0(sK2)) )
   => ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))
      & ~ r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)))
      & m1_subset_1(sK4,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
                  | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
                | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tex_2)).

fof(f1023,plain,(
    v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f1022,f87])).

fof(f87,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f64,f58])).

fof(f58,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f64,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f1022,plain,
    ( ~ l1_struct_0(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f1021,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f1021,plain,(
    v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f1020,f125])).

fof(f125,plain,(
    k2_pre_topc(sK2,k2_tarski(sK3,sK3)) != k2_pre_topc(sK2,k2_tarski(sK4,sK4)) ),
    inference(forward_demodulation,[],[f120,f124])).

fof(f124,plain,(
    k6_domain_1(u1_struct_0(sK2),sK4) = k2_tarski(sK4,sK4) ),
    inference(subsumption_resolution,[],[f123,f55])).

fof(f123,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK4) = k2_tarski(sK4,sK4)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f122,f87])).

fof(f122,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK4) = k2_tarski(sK4,sK4)
    | ~ l1_struct_0(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f112,f65])).

fof(f112,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK4) = k2_tarski(sK4,sK4) ),
    inference(resolution,[],[f86,f60])).

fof(f60,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f45])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f81,f63])).

fof(f63,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f81,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f120,plain,(
    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) != k2_pre_topc(sK2,k2_tarski(sK3,sK3)) ),
    inference(backward_demodulation,[],[f62,f119])).

fof(f119,plain,(
    k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3) ),
    inference(subsumption_resolution,[],[f118,f55])).

fof(f118,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f117,f87])).

fof(f117,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3)
    | ~ l1_struct_0(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f111,f65])).

fof(f111,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3) ),
    inference(resolution,[],[f86,f59])).

fof(f59,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f45])).

fof(f62,plain,(
    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) ),
    inference(cnf_transformation,[],[f45])).

fof(f1020,plain,
    ( k2_pre_topc(sK2,k2_tarski(sK3,sK3)) = k2_pre_topc(sK2,k2_tarski(sK4,sK4))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f1019,f124])).

fof(f1019,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) = k2_pre_topc(sK2,k2_tarski(sK3,sK3)) ),
    inference(subsumption_resolution,[],[f1016,f60])).

fof(f1016,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) = k2_pre_topc(sK2,k2_tarski(sK3,sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f981,f302])).

fof(f302,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_pre_topc(sK2,k2_tarski(sK3,sK3)))
      | k2_pre_topc(sK2,k2_tarski(sK3,sK3)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f301,f55])).

fof(f301,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_pre_topc(sK2,k2_tarski(sK3,sK3)))
      | k2_pre_topc(sK2,k2_tarski(sK3,sK3)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f300,f56])).

fof(f56,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f300,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_pre_topc(sK2,k2_tarski(sK3,sK3)))
      | k2_pre_topc(sK2,k2_tarski(sK3,sK3)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f299,f57])).

fof(f57,plain,(
    v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f299,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_pre_topc(sK2,k2_tarski(sK3,sK3)))
      | k2_pre_topc(sK2,k2_tarski(sK3,sK3)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ v3_tdlat_3(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f298,f58])).

fof(f298,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_pre_topc(sK2,k2_tarski(sK3,sK3)))
      | k2_pre_topc(sK2,k2_tarski(sK3,sK3)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ l1_pre_topc(sK2)
      | ~ v3_tdlat_3(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f296,f59])).

fof(f296,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_pre_topc(sK2,k2_tarski(sK3,sK3)))
      | k2_pre_topc(sK2,k2_tarski(sK3,sK3)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0))
      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ l1_pre_topc(sK2)
      | ~ v3_tdlat_3(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(superposition,[],[f66,f119])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
      | k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
               => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tex_2)).

fof(f981,plain,
    ( r2_hidden(sK4,k2_pre_topc(sK2,k2_tarski(sK3,sK3)))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f980,f164])).

fof(f164,plain,
    ( v3_pre_topc(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),sK2)
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f163,f146])).

fof(f146,plain,
    ( v4_pre_topc(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),sK2)
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f145,f56])).

fof(f145,plain,
    ( v4_pre_topc(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),sK2)
    | ~ v2_pre_topc(sK2)
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f142,f58])).

fof(f142,plain,
    ( v4_pre_topc(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f82,f102])).

fof(f102,plain,
    ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f85,f94])).

fof(f94,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f80,f59])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) ) ),
    inference(definition_unfolding,[],[f78,f63])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f163,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ v4_pre_topc(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),sK2)
    | v3_pre_topc(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),sK2) ),
    inference(subsumption_resolution,[],[f157,f92])).

fof(f92,plain,(
    sP0(sK2) ),
    inference(subsumption_resolution,[],[f91,f57])).

fof(f91,plain,
    ( ~ v3_tdlat_3(sK2)
    | sP0(sK2) ),
    inference(resolution,[],[f89,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ v3_tdlat_3(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v3_tdlat_3(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f89,plain,(
    sP1(sK2) ),
    inference(subsumption_resolution,[],[f88,f58])).

fof(f88,plain,
    ( ~ l1_pre_topc(sK2)
    | sP1(sK2) ),
    inference(resolution,[],[f73,f56])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | sP1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f25,f40,f39])).

fof(f39,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f25,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

fof(f157,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ v4_pre_topc(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),sK2)
    | v3_pre_topc(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),sK2)
    | ~ sP0(sK2) ),
    inference(resolution,[],[f153,f69])).

fof(f69,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | v3_pre_topc(X2,X0)
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( ~ v3_pre_topc(sK5(X0),X0)
          & v4_pre_topc(sK5(X0),X0)
          & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( v3_pre_topc(X2,X0)
            | ~ v4_pre_topc(X2,X0)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f48,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK5(X0),X0)
        & v4_pre_topc(sK5(X0),X0)
        & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ~ v3_pre_topc(X1,X0)
            & v4_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( v3_pre_topc(X2,X0)
            | ~ v4_pre_topc(X2,X0)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ~ v3_pre_topc(X1,X0)
            & v4_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f153,plain,
    ( m1_subset_1(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f150,f58])).

fof(f150,plain,
    ( m1_subset_1(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f83,f102])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f980,plain,
    ( ~ v3_pre_topc(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),sK2)
    | r2_hidden(sK4,k2_pre_topc(sK2,k2_tarski(sK3,sK3)))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f977,f126])).

fof(f126,plain,(
    ~ r1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),k2_pre_topc(sK2,k2_tarski(sK4,sK4))) ),
    inference(forward_demodulation,[],[f121,f124])).

fof(f121,plain,(
    ~ r1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
    inference(backward_demodulation,[],[f61,f119])).

fof(f61,plain,(
    ~ r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
    inference(cnf_transformation,[],[f45])).

fof(f977,plain,
    ( ~ v3_pre_topc(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),sK2)
    | r1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),k2_pre_topc(sK2,k2_tarski(sK4,sK4)))
    | r2_hidden(sK4,k2_pre_topc(sK2,k2_tarski(sK3,sK3)))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(duplicate_literal_removal,[],[f906])).

fof(f906,plain,
    ( ~ v3_pre_topc(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),sK2)
    | r1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),k2_pre_topc(sK2,k2_tarski(sK4,sK4)))
    | r2_hidden(sK4,k2_pre_topc(sK2,k2_tarski(sK3,sK3)))
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f790,f153])).

fof(f790,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v3_pre_topc(X1,sK2)
      | r1_xboole_0(X1,k2_pre_topc(sK2,k2_tarski(sK4,sK4)))
      | r2_hidden(sK4,X1)
      | v1_xboole_0(u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f789,f56])).

fof(f789,plain,(
    ! [X1] :
      ( r1_xboole_0(X1,k2_pre_topc(sK2,k2_tarski(sK4,sK4)))
      | ~ v3_pre_topc(X1,sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v2_pre_topc(sK2)
      | r2_hidden(sK4,X1)
      | v1_xboole_0(u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f785,f58])).

fof(f785,plain,(
    ! [X1] :
      ( r1_xboole_0(X1,k2_pre_topc(sK2,k2_tarski(sK4,sK4)))
      | ~ v3_pre_topc(X1,sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | r2_hidden(sK4,X1)
      | v1_xboole_0(u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f224,f103])).

fof(f103,plain,
    ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f85,f95])).

fof(f95,plain,
    ( r2_hidden(sK4,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f80,f60])).

fof(f224,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(k2_tarski(X5,X5),k1_zfmisc_1(u1_struct_0(X4)))
      | r1_xboole_0(X3,k2_pre_topc(X4,k2_tarski(X5,X5)))
      | ~ v3_pre_topc(X3,X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | r2_hidden(X5,X3) ) ),
    inference(resolution,[],[f74,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,k2_tarski(X0,X0))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f84,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f77,f63])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | r1_xboole_0(X1,k2_pre_topc(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_xboole_0(X1,k2_pre_topc(X0,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ r1_xboole_0(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_xboole_0(X1,k2_pre_topc(X0,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ r1_xboole_0(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v3_pre_topc(X1,X0)
                  & r1_xboole_0(X1,X2) )
               => r1_xboole_0(X1,k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_tsep_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:32:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.44  % (29818)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.44  % (29820)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.47  % (29820)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f1024,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(subsumption_resolution,[],[f1023,f55])).
% 0.22/0.47  fof(f55,plain,(
% 0.22/0.47    ~v2_struct_0(sK2)),
% 0.22/0.47    inference(cnf_transformation,[],[f45])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    ((k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) & ~r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) & m1_subset_1(sK4,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v3_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f18,f44,f43,f42])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)) & ~r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2))) & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v3_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    ? [X1] : (? [X2] : (k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)) & ~r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X1)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2))) & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,u1_struct_0(sK2))) => (? [X2] : (k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) & ~r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2))) & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK2)))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f44,plain,(
% 0.22/0.47    ? [X2] : (k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) & ~r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2))) & m1_subset_1(X2,u1_struct_0(sK2))) => (k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) & ~r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) & m1_subset_1(sK4,u1_struct_0(sK2)))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.47    inference(flattening,[],[f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (? [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f16])).
% 0.22/0.47  fof(f16,negated_conjecture,(
% 0.22/0.47    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 0.22/0.47    inference(negated_conjecture,[],[f15])).
% 0.22/0.47  fof(f15,conjecture,(
% 0.22/0.47    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tex_2)).
% 0.22/0.47  fof(f1023,plain,(
% 0.22/0.47    v2_struct_0(sK2)),
% 0.22/0.47    inference(subsumption_resolution,[],[f1022,f87])).
% 0.22/0.47  fof(f87,plain,(
% 0.22/0.47    l1_struct_0(sK2)),
% 0.22/0.47    inference(resolution,[],[f64,f58])).
% 0.22/0.47  fof(f58,plain,(
% 0.22/0.47    l1_pre_topc(sK2)),
% 0.22/0.47    inference(cnf_transformation,[],[f45])).
% 0.22/0.47  fof(f64,plain,(
% 0.22/0.47    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,axiom,(
% 0.22/0.47    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.47  fof(f1022,plain,(
% 0.22/0.47    ~l1_struct_0(sK2) | v2_struct_0(sK2)),
% 0.22/0.47    inference(resolution,[],[f1021,f65])).
% 0.22/0.47  fof(f65,plain,(
% 0.22/0.47    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.47    inference(flattening,[],[f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,axiom,(
% 0.22/0.47    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.47  fof(f1021,plain,(
% 0.22/0.47    v1_xboole_0(u1_struct_0(sK2))),
% 0.22/0.47    inference(subsumption_resolution,[],[f1020,f125])).
% 0.22/0.47  fof(f125,plain,(
% 0.22/0.47    k2_pre_topc(sK2,k2_tarski(sK3,sK3)) != k2_pre_topc(sK2,k2_tarski(sK4,sK4))),
% 0.22/0.47    inference(forward_demodulation,[],[f120,f124])).
% 0.22/0.47  fof(f124,plain,(
% 0.22/0.47    k6_domain_1(u1_struct_0(sK2),sK4) = k2_tarski(sK4,sK4)),
% 0.22/0.47    inference(subsumption_resolution,[],[f123,f55])).
% 0.22/0.47  fof(f123,plain,(
% 0.22/0.47    k6_domain_1(u1_struct_0(sK2),sK4) = k2_tarski(sK4,sK4) | v2_struct_0(sK2)),
% 0.22/0.47    inference(subsumption_resolution,[],[f122,f87])).
% 0.22/0.47  fof(f122,plain,(
% 0.22/0.47    k6_domain_1(u1_struct_0(sK2),sK4) = k2_tarski(sK4,sK4) | ~l1_struct_0(sK2) | v2_struct_0(sK2)),
% 0.22/0.47    inference(resolution,[],[f112,f65])).
% 0.22/0.47  fof(f112,plain,(
% 0.22/0.47    v1_xboole_0(u1_struct_0(sK2)) | k6_domain_1(u1_struct_0(sK2),sK4) = k2_tarski(sK4,sK4)),
% 0.22/0.47    inference(resolution,[],[f86,f60])).
% 0.22/0.47  fof(f60,plain,(
% 0.22/0.47    m1_subset_1(sK4,u1_struct_0(sK2))),
% 0.22/0.47    inference(cnf_transformation,[],[f45])).
% 0.22/0.47  fof(f86,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)) )),
% 0.22/0.47    inference(definition_unfolding,[],[f81,f63])).
% 0.22/0.47  fof(f63,plain,(
% 0.22/0.47    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.47  fof(f81,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f34])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.47    inference(flattening,[],[f33])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,axiom,(
% 0.22/0.47    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.47  fof(f120,plain,(
% 0.22/0.47    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) != k2_pre_topc(sK2,k2_tarski(sK3,sK3))),
% 0.22/0.47    inference(backward_demodulation,[],[f62,f119])).
% 0.22/0.47  fof(f119,plain,(
% 0.22/0.47    k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3)),
% 0.22/0.47    inference(subsumption_resolution,[],[f118,f55])).
% 0.22/0.47  fof(f118,plain,(
% 0.22/0.47    k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3) | v2_struct_0(sK2)),
% 0.22/0.47    inference(subsumption_resolution,[],[f117,f87])).
% 0.22/0.47  fof(f117,plain,(
% 0.22/0.47    k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3) | ~l1_struct_0(sK2) | v2_struct_0(sK2)),
% 0.22/0.47    inference(resolution,[],[f111,f65])).
% 0.22/0.47  fof(f111,plain,(
% 0.22/0.47    v1_xboole_0(u1_struct_0(sK2)) | k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3)),
% 0.22/0.47    inference(resolution,[],[f86,f59])).
% 0.22/0.47  fof(f59,plain,(
% 0.22/0.47    m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.22/0.47    inference(cnf_transformation,[],[f45])).
% 0.22/0.47  fof(f62,plain,(
% 0.22/0.47    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))),
% 0.22/0.47    inference(cnf_transformation,[],[f45])).
% 0.22/0.47  fof(f1020,plain,(
% 0.22/0.47    k2_pre_topc(sK2,k2_tarski(sK3,sK3)) = k2_pre_topc(sK2,k2_tarski(sK4,sK4)) | v1_xboole_0(u1_struct_0(sK2))),
% 0.22/0.47    inference(forward_demodulation,[],[f1019,f124])).
% 0.22/0.47  fof(f1019,plain,(
% 0.22/0.47    v1_xboole_0(u1_struct_0(sK2)) | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) = k2_pre_topc(sK2,k2_tarski(sK3,sK3))),
% 0.22/0.47    inference(subsumption_resolution,[],[f1016,f60])).
% 0.22/0.47  fof(f1016,plain,(
% 0.22/0.47    v1_xboole_0(u1_struct_0(sK2)) | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)) = k2_pre_topc(sK2,k2_tarski(sK3,sK3)) | ~m1_subset_1(sK4,u1_struct_0(sK2))),
% 0.22/0.47    inference(resolution,[],[f981,f302])).
% 0.22/0.47  fof(f302,plain,(
% 0.22/0.47    ( ! [X0] : (~r2_hidden(X0,k2_pre_topc(sK2,k2_tarski(sK3,sK3))) | k2_pre_topc(sK2,k2_tarski(sK3,sK3)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)) | ~m1_subset_1(X0,u1_struct_0(sK2))) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f301,f55])).
% 0.22/0.47  fof(f301,plain,(
% 0.22/0.47    ( ! [X0] : (~r2_hidden(X0,k2_pre_topc(sK2,k2_tarski(sK3,sK3))) | k2_pre_topc(sK2,k2_tarski(sK3,sK3)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | v2_struct_0(sK2)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f300,f56])).
% 0.22/0.47  fof(f56,plain,(
% 0.22/0.47    v2_pre_topc(sK2)),
% 0.22/0.47    inference(cnf_transformation,[],[f45])).
% 0.22/0.47  fof(f300,plain,(
% 0.22/0.47    ( ! [X0] : (~r2_hidden(X0,k2_pre_topc(sK2,k2_tarski(sK3,sK3))) | k2_pre_topc(sK2,k2_tarski(sK3,sK3)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f299,f57])).
% 0.22/0.47  fof(f57,plain,(
% 0.22/0.47    v3_tdlat_3(sK2)),
% 0.22/0.47    inference(cnf_transformation,[],[f45])).
% 0.22/0.47  fof(f299,plain,(
% 0.22/0.47    ( ! [X0] : (~r2_hidden(X0,k2_pre_topc(sK2,k2_tarski(sK3,sK3))) | k2_pre_topc(sK2,k2_tarski(sK3,sK3)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~v3_tdlat_3(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f298,f58])).
% 0.22/0.47  fof(f298,plain,(
% 0.22/0.47    ( ! [X0] : (~r2_hidden(X0,k2_pre_topc(sK2,k2_tarski(sK3,sK3))) | k2_pre_topc(sK2,k2_tarski(sK3,sK3)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v3_tdlat_3(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f296,f59])).
% 0.22/0.47  fof(f296,plain,(
% 0.22/0.47    ( ! [X0] : (~r2_hidden(X0,k2_pre_topc(sK2,k2_tarski(sK3,sK3))) | k2_pre_topc(sK2,k2_tarski(sK3,sK3)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X0)) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v3_tdlat_3(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.22/0.47    inference(superposition,[],[f66,f119])).
% 0.22/0.47  fof(f66,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f23])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.47    inference(flattening,[],[f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,axiom,(
% 0.22/0.47    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tex_2)).
% 0.22/0.47  fof(f981,plain,(
% 0.22/0.47    r2_hidden(sK4,k2_pre_topc(sK2,k2_tarski(sK3,sK3))) | v1_xboole_0(u1_struct_0(sK2))),
% 0.22/0.47    inference(subsumption_resolution,[],[f980,f164])).
% 0.22/0.47  fof(f164,plain,(
% 0.22/0.47    v3_pre_topc(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),sK2) | v1_xboole_0(u1_struct_0(sK2))),
% 0.22/0.47    inference(subsumption_resolution,[],[f163,f146])).
% 0.22/0.47  fof(f146,plain,(
% 0.22/0.47    v4_pre_topc(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),sK2) | v1_xboole_0(u1_struct_0(sK2))),
% 0.22/0.47    inference(subsumption_resolution,[],[f145,f56])).
% 0.22/0.47  fof(f145,plain,(
% 0.22/0.47    v4_pre_topc(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),sK2) | ~v2_pre_topc(sK2) | v1_xboole_0(u1_struct_0(sK2))),
% 0.22/0.47    inference(subsumption_resolution,[],[f142,f58])).
% 0.22/0.47  fof(f142,plain,(
% 0.22/0.47    v4_pre_topc(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v1_xboole_0(u1_struct_0(sK2))),
% 0.22/0.47    inference(resolution,[],[f82,f102])).
% 0.22/0.47  fof(f102,plain,(
% 0.22/0.47    m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | v1_xboole_0(u1_struct_0(sK2))),
% 0.22/0.47    inference(resolution,[],[f85,f94])).
% 0.22/0.47  fof(f94,plain,(
% 0.22/0.47    r2_hidden(sK3,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2))),
% 0.22/0.47    inference(resolution,[],[f80,f59])).
% 0.22/0.47  fof(f80,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f32])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.47    inference(flattening,[],[f31])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.47  fof(f85,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f78,f63])).
% 0.22/0.47  fof(f78,plain,(
% 0.22/0.47    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f29])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 0.22/0.47  fof(f82,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f36])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.47    inference(flattening,[],[f35])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,axiom,(
% 0.22/0.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).
% 0.22/0.47  fof(f163,plain,(
% 0.22/0.47    v1_xboole_0(u1_struct_0(sK2)) | ~v4_pre_topc(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),sK2) | v3_pre_topc(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),sK2)),
% 0.22/0.47    inference(subsumption_resolution,[],[f157,f92])).
% 0.22/0.47  fof(f92,plain,(
% 0.22/0.47    sP0(sK2)),
% 0.22/0.47    inference(subsumption_resolution,[],[f91,f57])).
% 0.22/0.47  fof(f91,plain,(
% 0.22/0.47    ~v3_tdlat_3(sK2) | sP0(sK2)),
% 0.22/0.47    inference(resolution,[],[f89,f67])).
% 0.22/0.47  fof(f67,plain,(
% 0.22/0.47    ( ! [X0] : (~sP1(X0) | ~v3_tdlat_3(X0) | sP0(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f46])).
% 0.22/0.47  fof(f46,plain,(
% 0.22/0.47    ! [X0] : (((v3_tdlat_3(X0) | ~sP0(X0)) & (sP0(X0) | ~v3_tdlat_3(X0))) | ~sP1(X0))),
% 0.22/0.47    inference(nnf_transformation,[],[f40])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    ! [X0] : ((v3_tdlat_3(X0) <=> sP0(X0)) | ~sP1(X0))),
% 0.22/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.47  fof(f89,plain,(
% 0.22/0.47    sP1(sK2)),
% 0.22/0.47    inference(subsumption_resolution,[],[f88,f58])).
% 0.22/0.47  fof(f88,plain,(
% 0.22/0.47    ~l1_pre_topc(sK2) | sP1(sK2)),
% 0.22/0.47    inference(resolution,[],[f73,f56])).
% 0.22/0.47  fof(f73,plain,(
% 0.22/0.47    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | sP1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f41])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    ! [X0] : (sP1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.47    inference(definition_folding,[],[f25,f40,f39])).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    ! [X0] : (sP0(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.47    inference(flattening,[],[f24])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,axiom,(
% 0.22/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).
% 0.22/0.47  fof(f157,plain,(
% 0.22/0.47    v1_xboole_0(u1_struct_0(sK2)) | ~v4_pre_topc(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),sK2) | v3_pre_topc(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),sK2) | ~sP0(sK2)),
% 0.22/0.47    inference(resolution,[],[f153,f69])).
% 0.22/0.47  fof(f69,plain,(
% 0.22/0.47    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | v3_pre_topc(X2,X0) | ~sP0(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f50])).
% 0.22/0.47  fof(f50,plain,(
% 0.22/0.47    ! [X0] : ((sP0(X0) | (~v3_pre_topc(sK5(X0),X0) & v4_pre_topc(sK5(X0),X0) & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0)))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f48,f49])).
% 0.22/0.47  fof(f49,plain,(
% 0.22/0.47    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK5(X0),X0) & v4_pre_topc(sK5(X0),X0) & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    ! [X0] : ((sP0(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0)))),
% 0.22/0.47    inference(rectify,[],[f47])).
% 0.22/0.47  fof(f47,plain,(
% 0.22/0.47    ! [X0] : ((sP0(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0)))),
% 0.22/0.47    inference(nnf_transformation,[],[f39])).
% 0.22/0.47  fof(f153,plain,(
% 0.22/0.47    m1_subset_1(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) | v1_xboole_0(u1_struct_0(sK2))),
% 0.22/0.47    inference(subsumption_resolution,[],[f150,f58])).
% 0.22/0.47  fof(f150,plain,(
% 0.22/0.47    m1_subset_1(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | v1_xboole_0(u1_struct_0(sK2))),
% 0.22/0.47    inference(resolution,[],[f83,f102])).
% 0.22/0.47  fof(f83,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f38])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(flattening,[],[f37])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,axiom,(
% 0.22/0.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.22/0.47  fof(f980,plain,(
% 0.22/0.47    ~v3_pre_topc(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),sK2) | r2_hidden(sK4,k2_pre_topc(sK2,k2_tarski(sK3,sK3))) | v1_xboole_0(u1_struct_0(sK2))),
% 0.22/0.47    inference(subsumption_resolution,[],[f977,f126])).
% 0.22/0.47  fof(f126,plain,(
% 0.22/0.47    ~r1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),k2_pre_topc(sK2,k2_tarski(sK4,sK4)))),
% 0.22/0.47    inference(forward_demodulation,[],[f121,f124])).
% 0.22/0.47  fof(f121,plain,(
% 0.22/0.47    ~r1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)))),
% 0.22/0.47    inference(backward_demodulation,[],[f61,f119])).
% 0.22/0.47  fof(f61,plain,(
% 0.22/0.47    ~r1_xboole_0(k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK3)),k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)))),
% 0.22/0.47    inference(cnf_transformation,[],[f45])).
% 0.22/0.47  fof(f977,plain,(
% 0.22/0.47    ~v3_pre_topc(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),sK2) | r1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),k2_pre_topc(sK2,k2_tarski(sK4,sK4))) | r2_hidden(sK4,k2_pre_topc(sK2,k2_tarski(sK3,sK3))) | v1_xboole_0(u1_struct_0(sK2))),
% 0.22/0.47    inference(duplicate_literal_removal,[],[f906])).
% 0.22/0.47  fof(f906,plain,(
% 0.22/0.47    ~v3_pre_topc(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),sK2) | r1_xboole_0(k2_pre_topc(sK2,k2_tarski(sK3,sK3)),k2_pre_topc(sK2,k2_tarski(sK4,sK4))) | r2_hidden(sK4,k2_pre_topc(sK2,k2_tarski(sK3,sK3))) | v1_xboole_0(u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2))),
% 0.22/0.47    inference(resolution,[],[f790,f153])).
% 0.22/0.47  fof(f790,plain,(
% 0.22/0.47    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_pre_topc(X1,sK2) | r1_xboole_0(X1,k2_pre_topc(sK2,k2_tarski(sK4,sK4))) | r2_hidden(sK4,X1) | v1_xboole_0(u1_struct_0(sK2))) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f789,f56])).
% 0.22/0.47  fof(f789,plain,(
% 0.22/0.47    ( ! [X1] : (r1_xboole_0(X1,k2_pre_topc(sK2,k2_tarski(sK4,sK4))) | ~v3_pre_topc(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~v2_pre_topc(sK2) | r2_hidden(sK4,X1) | v1_xboole_0(u1_struct_0(sK2))) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f785,f58])).
% 0.22/0.47  fof(f785,plain,(
% 0.22/0.47    ( ! [X1] : (r1_xboole_0(X1,k2_pre_topc(sK2,k2_tarski(sK4,sK4))) | ~v3_pre_topc(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | r2_hidden(sK4,X1) | v1_xboole_0(u1_struct_0(sK2))) )),
% 0.22/0.47    inference(resolution,[],[f224,f103])).
% 0.22/0.47  fof(f103,plain,(
% 0.22/0.47    m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) | v1_xboole_0(u1_struct_0(sK2))),
% 0.22/0.47    inference(resolution,[],[f85,f95])).
% 0.22/0.47  fof(f95,plain,(
% 0.22/0.47    r2_hidden(sK4,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2))),
% 0.22/0.47    inference(resolution,[],[f80,f60])).
% 0.22/0.47  fof(f224,plain,(
% 0.22/0.47    ( ! [X4,X5,X3] : (~m1_subset_1(k2_tarski(X5,X5),k1_zfmisc_1(u1_struct_0(X4))) | r1_xboole_0(X3,k2_pre_topc(X4,k2_tarski(X5,X5))) | ~v3_pre_topc(X3,X4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4))) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | r2_hidden(X5,X3)) )),
% 0.22/0.47    inference(resolution,[],[f74,f99])).
% 0.22/0.47  fof(f99,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_xboole_0(X1,k2_tarski(X0,X0)) | r2_hidden(X0,X1)) )),
% 0.22/0.47    inference(resolution,[],[f84,f79])).
% 0.22/0.47  fof(f79,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f30])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.22/0.47  fof(f84,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_xboole_0(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.22/0.47    inference(definition_unfolding,[],[f77,f63])).
% 0.22/0.47  fof(f77,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f28])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.22/0.47  fof(f74,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | ~v3_pre_topc(X1,X0) | r1_xboole_0(X1,k2_pre_topc(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f27])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (! [X2] : (r1_xboole_0(X1,k2_pre_topc(X0,X2)) | ~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.47    inference(flattening,[],[f26])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (! [X2] : ((r1_xboole_0(X1,k2_pre_topc(X0,X2)) | (~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,axiom,(
% 0.22/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X1,X0) & r1_xboole_0(X1,X2)) => r1_xboole_0(X1,k2_pre_topc(X0,X2))))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_tsep_1)).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (29820)------------------------------
% 0.22/0.47  % (29820)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (29820)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (29820)Memory used [KB]: 2302
% 0.22/0.47  % (29820)Time elapsed: 0.032 s
% 0.22/0.47  % (29820)------------------------------
% 0.22/0.47  % (29820)------------------------------
% 0.22/0.48  % (29807)Success in time 0.111 s
%------------------------------------------------------------------------------
