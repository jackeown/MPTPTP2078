%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:39 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :  116 (1702 expanded)
%              Number of leaves         :   21 ( 595 expanded)
%              Depth                    :   38
%              Number of atoms          :  438 (10702 expanded)
%              Number of equality atoms :   48 (1567 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f192,plain,(
    $false ),
    inference(subsumption_resolution,[],[f191,f123])).

fof(f123,plain,(
    m1_subset_1(sK4,k1_xboole_0) ),
    inference(backward_demodulation,[],[f53,f121])).

fof(f121,plain,(
    k1_xboole_0 = u1_struct_0(sK2) ),
    inference(resolution,[],[f118,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f118,plain,(
    v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f117,f55])).

fof(f55,plain,(
    r1_orders_2(sK2,sK4,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( sK3 != sK4
    & r1_orders_2(sK2,sK4,sK3)
    & r1_orders_2(sK2,sK3,sK4)
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_orders_2(sK2)
    & v5_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f18,f37,f36,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & r1_orders_2(X0,X2,X1)
                & r1_orders_2(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r1_orders_2(sK2,X2,X1)
              & r1_orders_2(sK2,X1,X2)
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_orders_2(sK2)
      & v5_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( X1 != X2
            & r1_orders_2(sK2,X2,X1)
            & r1_orders_2(sK2,X1,X2)
            & m1_subset_1(X2,u1_struct_0(sK2)) )
        & m1_subset_1(X1,u1_struct_0(sK2)) )
   => ( ? [X2] :
          ( sK3 != X2
          & r1_orders_2(sK2,X2,sK3)
          & r1_orders_2(sK2,sK3,X2)
          & m1_subset_1(X2,u1_struct_0(sK2)) )
      & m1_subset_1(sK3,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X2] :
        ( sK3 != X2
        & r1_orders_2(sK2,X2,sK3)
        & r1_orders_2(sK2,sK3,X2)
        & m1_subset_1(X2,u1_struct_0(sK2)) )
   => ( sK3 != sK4
      & r1_orders_2(sK2,sK4,sK3)
      & r1_orders_2(sK2,sK3,sK4)
      & m1_subset_1(sK4,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r1_orders_2(X0,X2,X1)
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r1_orders_2(X0,X2,X1)
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ( r1_orders_2(X0,X2,X1)
                    & r1_orders_2(X0,X1,X2) )
                 => X1 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_orders_2)).

fof(f117,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ r1_orders_2(sK2,sK4,sK3) ),
    inference(subsumption_resolution,[],[f116,f56])).

fof(f56,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f38])).

fof(f116,plain,
    ( sK3 = sK4
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ r1_orders_2(sK2,sK4,sK3) ),
    inference(subsumption_resolution,[],[f115,f53])).

fof(f115,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | sK3 = sK4
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ r1_orders_2(sK2,sK4,sK3) ),
    inference(resolution,[],[f114,f54])).

fof(f54,plain,(
    r1_orders_2(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f114,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK2,sK3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | sK3 = X0
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ r1_orders_2(sK2,X0,sK3) ) ),
    inference(subsumption_resolution,[],[f113,f51])).

fof(f51,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f113,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK2,sK3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | sK3 = X0
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ r1_orders_2(sK2,X0,sK3)
      | ~ l1_orders_2(sK2) ) ),
    inference(subsumption_resolution,[],[f112,f52])).

fof(f52,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f112,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK2,sK3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | sK3 = X0
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ r1_orders_2(sK2,X0,sK3)
      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
      | ~ l1_orders_2(sK2) ) ),
    inference(duplicate_literal_removal,[],[f111])).

fof(f111,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK2,sK3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | sK3 = X0
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ r1_orders_2(sK2,X0,sK3)
      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ l1_orders_2(sK2) ) ),
    inference(resolution,[],[f108,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

fof(f108,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(X0,sK3),u1_orders_2(sK2))
      | ~ r1_orders_2(sK2,sK3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | sK3 = X0
      | v1_xboole_0(u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f107,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f107,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(sK2))
      | ~ r2_hidden(k4_tarski(X0,sK3),u1_orders_2(sK2))
      | ~ r1_orders_2(sK2,sK3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | sK3 = X0
      | v1_xboole_0(u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f105,f81])).

fof(f81,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f79,f52])).

fof(f105,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,u1_struct_0(sK2))
      | ~ r2_hidden(X0,u1_struct_0(sK2))
      | ~ r2_hidden(k4_tarski(X0,sK3),u1_orders_2(sK2))
      | ~ r1_orders_2(sK2,sK3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | sK3 = X0 ) ),
    inference(resolution,[],[f98,f52])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK2))
      | ~ r2_hidden(X0,u1_struct_0(sK2))
      | ~ r2_hidden(X1,u1_struct_0(sK2))
      | ~ r1_orders_2(sK2,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | X0 = X1 ) ),
    inference(subsumption_resolution,[],[f95,f51])).

fof(f95,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK2))
      | ~ r2_hidden(X0,u1_struct_0(sK2))
      | ~ r2_hidden(X1,u1_struct_0(sK2))
      | ~ r1_orders_2(sK2,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ l1_orders_2(sK2) ) ),
    inference(resolution,[],[f94,f61])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2))
      | X0 = X1
      | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK2))
      | ~ r2_hidden(X0,u1_struct_0(sK2))
      | ~ r2_hidden(X1,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f93,f51])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(sK2))
      | X0 = X1
      | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK2))
      | ~ r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2))
      | ~ r2_hidden(X1,u1_struct_0(sK2))
      | ~ l1_orders_2(sK2) ) ),
    inference(subsumption_resolution,[],[f92,f50])).

fof(f50,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(sK2))
      | X0 = X1
      | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK2))
      | ~ r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2))
      | ~ r2_hidden(X1,u1_struct_0(sK2))
      | ~ v5_orders_2(sK2)
      | ~ l1_orders_2(sK2) ) ),
    inference(resolution,[],[f91,f87])).

fof(f87,plain,(
    v1_relat_1(u1_orders_2(sK2)) ),
    inference(subsumption_resolution,[],[f84,f76])).

fof(f76,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f84,plain,
    ( v1_relat_1(u1_orders_2(sK2))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) ),
    inference(resolution,[],[f83,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f83,plain,(
    m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) ),
    inference(resolution,[],[f58,f51])).

fof(f58,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(u1_orders_2(X1))
      | ~ r2_hidden(X2,u1_struct_0(X1))
      | X0 = X2
      | ~ r2_hidden(k4_tarski(X2,X0),u1_orders_2(X1))
      | ~ r2_hidden(k4_tarski(X0,X2),u1_orders_2(X1))
      | ~ r2_hidden(X0,u1_struct_0(X1))
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f90,f59])).

fof(f59,plain,(
    ! [X0] :
      ( r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( ( v5_orders_2(X0)
          | ~ r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
        & ( r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))
          | ~ v5_orders_2(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v5_orders_2(X0)
      <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v5_orders_2(X0)
      <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_orders_2)).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r4_relat_2(X2,X3)
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X3)
      | X0 = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(k4_tarski(X1,X0),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f89,f72])).

fof(f72,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f24,f33,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2,X3] :
          ( X2 = X3
          | ~ r2_hidden(k4_tarski(X3,X2),X0)
          | ~ r2_hidden(k4_tarski(X2,X3),X0)
          | ~ r2_hidden(X3,X1)
          | ~ r2_hidden(X2,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> sP0(X0,X1) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( X2 = X3
              | ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( X2 = X3
              | ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X3,X2),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) )
             => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_2)).

% (28415)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% (28418)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% (28405)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% (28407)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% (28413)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% (28410)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% (28419)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% (28414)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% (28401)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% (28400)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% (28409)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (28404)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% (28406)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% (28411)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% (28412)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% (28401)Refutation not found, incomplete strategy% (28401)------------------------------
% (28401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (28401)Termination reason: Refutation not found, incomplete strategy

% (28401)Memory used [KB]: 10746
% (28401)Time elapsed: 0.123 s
% (28401)------------------------------
% (28401)------------------------------
fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X2)
      | ~ r2_hidden(k4_tarski(X1,X0),X2)
      | ~ r2_hidden(X0,X3)
      | ~ r2_hidden(X1,X3)
      | X0 = X1
      | ~ r4_relat_2(X2,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(resolution,[],[f66,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ r4_relat_2(X0,X1)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r4_relat_2(X0,X1)
            | ~ sP0(X0,X1) )
          & ( sP0(X0,X1)
            | ~ r4_relat_2(X0,X1) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f66,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ sP0(X0,X1)
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | X4 = X5 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( sK5(X0,X1) != sK6(X0,X1)
          & r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
          & r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
          & r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X1) ) )
      & ( ! [X4,X5] :
            ( X4 = X5
            | ~ r2_hidden(k4_tarski(X5,X4),X0)
            | ~ r2_hidden(k4_tarski(X4,X5),X0)
            | ~ r2_hidden(X5,X1)
            | ~ r2_hidden(X4,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f43,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X2 != X3
          & r2_hidden(k4_tarski(X3,X2),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( sK5(X0,X1) != sK6(X0,X1)
        & r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
        & r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
        & r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2,X3] :
            ( X2 != X3
            & r2_hidden(k4_tarski(X3,X2),X0)
            & r2_hidden(k4_tarski(X2,X3),X0)
            & r2_hidden(X3,X1)
            & r2_hidden(X2,X1) ) )
      & ( ! [X4,X5] :
            ( X4 = X5
            | ~ r2_hidden(k4_tarski(X5,X4),X0)
            | ~ r2_hidden(k4_tarski(X4,X5),X0)
            | ~ r2_hidden(X5,X1)
            | ~ r2_hidden(X4,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2,X3] :
            ( X2 != X3
            & r2_hidden(k4_tarski(X3,X2),X0)
            & r2_hidden(k4_tarski(X2,X3),X0)
            & r2_hidden(X3,X1)
            & r2_hidden(X2,X1) ) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f53,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f191,plain,(
    ~ m1_subset_1(sK4,k1_xboole_0) ),
    inference(resolution,[],[f189,f55])).

fof(f189,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK2,X0,sK3)
      | ~ m1_subset_1(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f184,f122])).

fof(f122,plain,(
    m1_subset_1(sK3,k1_xboole_0) ),
    inference(backward_demodulation,[],[f52,f121])).

fof(f184,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_xboole_0)
      | ~ r1_orders_2(sK2,X2,X3) ) ),
    inference(forward_demodulation,[],[f183,f121])).

fof(f183,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_xboole_0)
      | ~ r1_orders_2(sK2,X2,X3)
      | ~ m1_subset_1(X2,u1_struct_0(sK2)) ) ),
    inference(forward_demodulation,[],[f182,f121])).

fof(f182,plain,(
    ! [X2,X3] :
      ( ~ r1_orders_2(sK2,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | ~ m1_subset_1(X2,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f181,f51])).

fof(f181,plain,(
    ! [X2,X3] :
      ( ~ r1_orders_2(sK2,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ l1_orders_2(sK2) ) ),
    inference(subsumption_resolution,[],[f179,f131])).

fof(f131,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f120,f121])).

fof(f120,plain,(
    ! [X1] : ~ r2_hidden(X1,u1_struct_0(sK2)) ),
    inference(resolution,[],[f118,f74])).

fof(f74,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK7(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f47,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f179,plain,(
    ! [X2,X3] :
      ( r2_hidden(k4_tarski(X2,X3),k1_xboole_0)
      | ~ r1_orders_2(sK2,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ l1_orders_2(sK2) ) ),
    inference(superposition,[],[f61,f163])).

fof(f163,plain,(
    k1_xboole_0 = u1_orders_2(sK2) ),
    inference(resolution,[],[f159,f73])).

fof(f159,plain,(
    v1_xboole_0(u1_orders_2(sK2)) ),
    inference(subsumption_resolution,[],[f154,f57])).

fof(f57,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f154,plain,
    ( ~ r1_xboole_0(u1_orders_2(sK2),k1_xboole_0)
    | v1_xboole_0(u1_orders_2(sK2)) ),
    inference(backward_demodulation,[],[f127,f150])).

fof(f150,plain,(
    ! [X4] : k1_xboole_0 = k2_zfmisc_1(X4,k1_xboole_0) ),
    inference(resolution,[],[f130,f73])).

fof(f130,plain,(
    ! [X0] : v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f119,f121])).

fof(f119,plain,(
    ! [X0] : v1_xboole_0(k2_zfmisc_1(X0,u1_struct_0(sK2))) ),
    inference(resolution,[],[f118,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(f127,plain,
    ( ~ r1_xboole_0(u1_orders_2(sK2),k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | v1_xboole_0(u1_orders_2(sK2)) ),
    inference(backward_demodulation,[],[f88,f121])).

fof(f88,plain,
    ( ~ r1_xboole_0(u1_orders_2(sK2),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))
    | v1_xboole_0(u1_orders_2(sK2)) ),
    inference(resolution,[],[f85,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_xboole_0(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f85,plain,(
    r1_tarski(u1_orders_2(sK2),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) ),
    inference(resolution,[],[f83,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:35:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 1.27/0.54  % (28403)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.27/0.54  % (28399)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.27/0.54  % (28417)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.27/0.54  % (28398)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.27/0.54  % (28397)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.27/0.54  % (28402)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.27/0.54  % (28402)Refutation not found, incomplete strategy% (28402)------------------------------
% 1.27/0.54  % (28402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (28402)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.54  
% 1.27/0.54  % (28402)Memory used [KB]: 1663
% 1.27/0.54  % (28402)Time elapsed: 0.102 s
% 1.27/0.54  % (28402)------------------------------
% 1.27/0.54  % (28402)------------------------------
% 1.27/0.54  % (28398)Refutation found. Thanks to Tanya!
% 1.27/0.54  % SZS status Theorem for theBenchmark
% 1.27/0.54  % SZS output start Proof for theBenchmark
% 1.27/0.54  fof(f192,plain,(
% 1.27/0.54    $false),
% 1.27/0.54    inference(subsumption_resolution,[],[f191,f123])).
% 1.27/0.54  fof(f123,plain,(
% 1.27/0.54    m1_subset_1(sK4,k1_xboole_0)),
% 1.27/0.54    inference(backward_demodulation,[],[f53,f121])).
% 1.27/0.54  fof(f121,plain,(
% 1.27/0.54    k1_xboole_0 = u1_struct_0(sK2)),
% 1.27/0.54    inference(resolution,[],[f118,f73])).
% 1.27/0.54  fof(f73,plain,(
% 1.27/0.54    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.27/0.54    inference(cnf_transformation,[],[f25])).
% 1.27/0.54  fof(f25,plain,(
% 1.27/0.54    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.27/0.54    inference(ennf_transformation,[],[f2])).
% 1.27/0.54  fof(f2,axiom,(
% 1.27/0.54    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.27/0.54  fof(f118,plain,(
% 1.27/0.54    v1_xboole_0(u1_struct_0(sK2))),
% 1.27/0.54    inference(subsumption_resolution,[],[f117,f55])).
% 1.27/0.54  fof(f55,plain,(
% 1.27/0.54    r1_orders_2(sK2,sK4,sK3)),
% 1.27/0.54    inference(cnf_transformation,[],[f38])).
% 1.27/0.54  fof(f38,plain,(
% 1.27/0.54    ((sK3 != sK4 & r1_orders_2(sK2,sK4,sK3) & r1_orders_2(sK2,sK3,sK4) & m1_subset_1(sK4,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_orders_2(sK2) & v5_orders_2(sK2)),
% 1.27/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f18,f37,f36,f35])).
% 1.27/0.54  fof(f35,plain,(
% 1.27/0.54    ? [X0] : (? [X1] : (? [X2] : (X1 != X2 & r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0)) => (? [X1] : (? [X2] : (X1 != X2 & r1_orders_2(sK2,X2,X1) & r1_orders_2(sK2,X1,X2) & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_orders_2(sK2) & v5_orders_2(sK2))),
% 1.27/0.54    introduced(choice_axiom,[])).
% 1.27/0.54  fof(f36,plain,(
% 1.27/0.54    ? [X1] : (? [X2] : (X1 != X2 & r1_orders_2(sK2,X2,X1) & r1_orders_2(sK2,X1,X2) & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,u1_struct_0(sK2))) => (? [X2] : (sK3 != X2 & r1_orders_2(sK2,X2,sK3) & r1_orders_2(sK2,sK3,X2) & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK2)))),
% 1.27/0.54    introduced(choice_axiom,[])).
% 1.27/0.54  fof(f37,plain,(
% 1.27/0.54    ? [X2] : (sK3 != X2 & r1_orders_2(sK2,X2,sK3) & r1_orders_2(sK2,sK3,X2) & m1_subset_1(X2,u1_struct_0(sK2))) => (sK3 != sK4 & r1_orders_2(sK2,sK4,sK3) & r1_orders_2(sK2,sK3,sK4) & m1_subset_1(sK4,u1_struct_0(sK2)))),
% 1.27/0.54    introduced(choice_axiom,[])).
% 1.27/0.54  fof(f18,plain,(
% 1.27/0.54    ? [X0] : (? [X1] : (? [X2] : (X1 != X2 & r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0))),
% 1.27/0.54    inference(flattening,[],[f17])).
% 1.27/0.54  fof(f17,plain,(
% 1.27/0.54    ? [X0] : (? [X1] : (? [X2] : ((X1 != X2 & (r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0)))),
% 1.27/0.54    inference(ennf_transformation,[],[f15])).
% 1.27/0.54  fof(f15,negated_conjecture,(
% 1.27/0.54    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2)) => X1 = X2))))),
% 1.27/0.54    inference(negated_conjecture,[],[f14])).
% 1.27/0.54  fof(f14,conjecture,(
% 1.27/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2)) => X1 = X2))))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_orders_2)).
% 1.27/0.54  fof(f117,plain,(
% 1.27/0.54    v1_xboole_0(u1_struct_0(sK2)) | ~r1_orders_2(sK2,sK4,sK3)),
% 1.27/0.54    inference(subsumption_resolution,[],[f116,f56])).
% 1.27/0.54  fof(f56,plain,(
% 1.27/0.54    sK3 != sK4),
% 1.27/0.54    inference(cnf_transformation,[],[f38])).
% 1.27/0.54  fof(f116,plain,(
% 1.27/0.54    sK3 = sK4 | v1_xboole_0(u1_struct_0(sK2)) | ~r1_orders_2(sK2,sK4,sK3)),
% 1.27/0.54    inference(subsumption_resolution,[],[f115,f53])).
% 1.27/0.54  fof(f115,plain,(
% 1.27/0.54    ~m1_subset_1(sK4,u1_struct_0(sK2)) | sK3 = sK4 | v1_xboole_0(u1_struct_0(sK2)) | ~r1_orders_2(sK2,sK4,sK3)),
% 1.27/0.54    inference(resolution,[],[f114,f54])).
% 1.27/0.54  fof(f54,plain,(
% 1.27/0.54    r1_orders_2(sK2,sK3,sK4)),
% 1.27/0.54    inference(cnf_transformation,[],[f38])).
% 1.27/0.54  fof(f114,plain,(
% 1.27/0.54    ( ! [X0] : (~r1_orders_2(sK2,sK3,X0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | sK3 = X0 | v1_xboole_0(u1_struct_0(sK2)) | ~r1_orders_2(sK2,X0,sK3)) )),
% 1.27/0.54    inference(subsumption_resolution,[],[f113,f51])).
% 1.27/0.54  fof(f51,plain,(
% 1.27/0.54    l1_orders_2(sK2)),
% 1.27/0.54    inference(cnf_transformation,[],[f38])).
% 1.27/0.54  fof(f113,plain,(
% 1.27/0.54    ( ! [X0] : (~r1_orders_2(sK2,sK3,X0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | sK3 = X0 | v1_xboole_0(u1_struct_0(sK2)) | ~r1_orders_2(sK2,X0,sK3) | ~l1_orders_2(sK2)) )),
% 1.27/0.54    inference(subsumption_resolution,[],[f112,f52])).
% 1.27/0.54  fof(f52,plain,(
% 1.27/0.54    m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.27/0.54    inference(cnf_transformation,[],[f38])).
% 1.27/0.54  fof(f112,plain,(
% 1.27/0.54    ( ! [X0] : (~r1_orders_2(sK2,sK3,X0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | sK3 = X0 | v1_xboole_0(u1_struct_0(sK2)) | ~r1_orders_2(sK2,X0,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~l1_orders_2(sK2)) )),
% 1.27/0.54    inference(duplicate_literal_removal,[],[f111])).
% 1.27/0.54  fof(f111,plain,(
% 1.27/0.54    ( ! [X0] : (~r1_orders_2(sK2,sK3,X0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | sK3 = X0 | v1_xboole_0(u1_struct_0(sK2)) | ~r1_orders_2(sK2,X0,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~l1_orders_2(sK2)) )),
% 1.27/0.54    inference(resolution,[],[f108,f61])).
% 1.27/0.54  fof(f61,plain,(
% 1.27/0.54    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f40])).
% 1.27/0.54  fof(f40,plain,(
% 1.27/0.54    ! [X0] : (! [X1] : (! [X2] : (((r1_orders_2(X0,X1,X2) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) & (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.27/0.54    inference(nnf_transformation,[],[f21])).
% 1.27/0.54  fof(f21,plain,(
% 1.27/0.54    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.27/0.54    inference(ennf_transformation,[],[f12])).
% 1.27/0.54  fof(f12,axiom,(
% 1.27/0.54    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).
% 1.27/0.54  fof(f108,plain,(
% 1.27/0.54    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK3),u1_orders_2(sK2)) | ~r1_orders_2(sK2,sK3,X0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | sK3 = X0 | v1_xboole_0(u1_struct_0(sK2))) )),
% 1.27/0.54    inference(subsumption_resolution,[],[f107,f79])).
% 1.27/0.54  fof(f79,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f30])).
% 1.27/0.54  fof(f30,plain,(
% 1.27/0.54    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.27/0.54    inference(flattening,[],[f29])).
% 1.27/0.54  fof(f29,plain,(
% 1.27/0.54    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.27/0.54    inference(ennf_transformation,[],[f6])).
% 1.27/0.54  fof(f6,axiom,(
% 1.27/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.27/0.54  fof(f107,plain,(
% 1.27/0.54    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK2)) | ~r2_hidden(k4_tarski(X0,sK3),u1_orders_2(sK2)) | ~r1_orders_2(sK2,sK3,X0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | sK3 = X0 | v1_xboole_0(u1_struct_0(sK2))) )),
% 1.27/0.54    inference(resolution,[],[f105,f81])).
% 1.27/0.54  fof(f81,plain,(
% 1.27/0.54    r2_hidden(sK3,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2))),
% 1.27/0.54    inference(resolution,[],[f79,f52])).
% 1.27/0.54  fof(f105,plain,(
% 1.27/0.54    ( ! [X0] : (~r2_hidden(sK3,u1_struct_0(sK2)) | ~r2_hidden(X0,u1_struct_0(sK2)) | ~r2_hidden(k4_tarski(X0,sK3),u1_orders_2(sK2)) | ~r1_orders_2(sK2,sK3,X0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | sK3 = X0) )),
% 1.27/0.54    inference(resolution,[],[f98,f52])).
% 1.27/0.54  fof(f98,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK2)) | ~r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK2)) | ~r2_hidden(X0,u1_struct_0(sK2)) | ~r2_hidden(X1,u1_struct_0(sK2)) | ~r1_orders_2(sK2,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | X0 = X1) )),
% 1.27/0.54    inference(subsumption_resolution,[],[f95,f51])).
% 1.27/0.54  fof(f95,plain,(
% 1.27/0.54    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK2)) | ~r2_hidden(X0,u1_struct_0(sK2)) | ~r2_hidden(X1,u1_struct_0(sK2)) | ~r1_orders_2(sK2,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~l1_orders_2(sK2)) )),
% 1.27/0.54    inference(resolution,[],[f94,f61])).
% 1.27/0.54  fof(f94,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2)) | X0 = X1 | ~r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK2)) | ~r2_hidden(X0,u1_struct_0(sK2)) | ~r2_hidden(X1,u1_struct_0(sK2))) )),
% 1.27/0.54    inference(subsumption_resolution,[],[f93,f51])).
% 1.27/0.54  fof(f93,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~r2_hidden(X0,u1_struct_0(sK2)) | X0 = X1 | ~r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK2)) | ~r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2)) | ~r2_hidden(X1,u1_struct_0(sK2)) | ~l1_orders_2(sK2)) )),
% 1.27/0.54    inference(subsumption_resolution,[],[f92,f50])).
% 1.27/0.54  fof(f50,plain,(
% 1.27/0.54    v5_orders_2(sK2)),
% 1.27/0.54    inference(cnf_transformation,[],[f38])).
% 1.27/0.54  fof(f92,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~r2_hidden(X0,u1_struct_0(sK2)) | X0 = X1 | ~r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK2)) | ~r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK2)) | ~r2_hidden(X1,u1_struct_0(sK2)) | ~v5_orders_2(sK2) | ~l1_orders_2(sK2)) )),
% 1.27/0.54    inference(resolution,[],[f91,f87])).
% 1.27/0.54  fof(f87,plain,(
% 1.27/0.54    v1_relat_1(u1_orders_2(sK2))),
% 1.27/0.54    inference(subsumption_resolution,[],[f84,f76])).
% 1.27/0.54  fof(f76,plain,(
% 1.27/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.27/0.54    inference(cnf_transformation,[],[f9])).
% 1.27/0.54  fof(f9,axiom,(
% 1.27/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.27/0.54  fof(f84,plain,(
% 1.27/0.54    v1_relat_1(u1_orders_2(sK2)) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))),
% 1.27/0.54    inference(resolution,[],[f83,f63])).
% 1.27/0.54  fof(f63,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f22])).
% 1.27/0.54  fof(f22,plain,(
% 1.27/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.27/0.54    inference(ennf_transformation,[],[f8])).
% 1.27/0.54  fof(f8,axiom,(
% 1.27/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.27/0.54  fof(f83,plain,(
% 1.27/0.54    m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))),
% 1.27/0.54    inference(resolution,[],[f58,f51])).
% 1.27/0.54  fof(f58,plain,(
% 1.27/0.54    ( ! [X0] : (~l1_orders_2(X0) | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))) )),
% 1.27/0.54    inference(cnf_transformation,[],[f19])).
% 1.27/0.54  fof(f19,plain,(
% 1.27/0.54    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.27/0.54    inference(ennf_transformation,[],[f13])).
% 1.27/0.54  fof(f13,axiom,(
% 1.27/0.54    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).
% 1.27/0.54  fof(f91,plain,(
% 1.27/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(u1_orders_2(X1)) | ~r2_hidden(X2,u1_struct_0(X1)) | X0 = X2 | ~r2_hidden(k4_tarski(X2,X0),u1_orders_2(X1)) | ~r2_hidden(k4_tarski(X0,X2),u1_orders_2(X1)) | ~r2_hidden(X0,u1_struct_0(X1)) | ~v5_orders_2(X1) | ~l1_orders_2(X1)) )),
% 1.27/0.54    inference(resolution,[],[f90,f59])).
% 1.27/0.54  fof(f59,plain,(
% 1.27/0.54    ( ! [X0] : (r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~v5_orders_2(X0) | ~l1_orders_2(X0)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f39])).
% 1.27/0.54  fof(f39,plain,(
% 1.27/0.54    ! [X0] : (((v5_orders_2(X0) | ~r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))) & (r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~v5_orders_2(X0))) | ~l1_orders_2(X0))),
% 1.27/0.54    inference(nnf_transformation,[],[f20])).
% 1.27/0.54  fof(f20,plain,(
% 1.27/0.54    ! [X0] : ((v5_orders_2(X0) <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.27/0.54    inference(ennf_transformation,[],[f11])).
% 1.27/0.54  fof(f11,axiom,(
% 1.27/0.54    ! [X0] : (l1_orders_2(X0) => (v5_orders_2(X0) <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_orders_2)).
% 1.27/0.54  fof(f90,plain,(
% 1.27/0.54    ( ! [X2,X0,X3,X1] : (~r4_relat_2(X2,X3) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X3) | X0 = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(k4_tarski(X1,X0),X2) | ~v1_relat_1(X2)) )),
% 1.27/0.54    inference(resolution,[],[f89,f72])).
% 1.27/0.54  fof(f72,plain,(
% 1.27/0.54    ( ! [X0] : (sP1(X0) | ~v1_relat_1(X0)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f34])).
% 1.27/0.54  fof(f34,plain,(
% 1.27/0.54    ! [X0] : (sP1(X0) | ~v1_relat_1(X0))),
% 1.27/0.54    inference(definition_folding,[],[f24,f33,f32])).
% 1.27/0.54  fof(f32,plain,(
% 1.27/0.54    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2,X3] : (X2 = X3 | ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)))),
% 1.27/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.27/0.54  fof(f33,plain,(
% 1.27/0.54    ! [X0] : (! [X1] : (r4_relat_2(X0,X1) <=> sP0(X0,X1)) | ~sP1(X0))),
% 1.27/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.27/0.54  fof(f24,plain,(
% 1.27/0.54    ! [X0] : (! [X1] : (r4_relat_2(X0,X1) <=> ! [X2,X3] : (X2 = X3 | ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1))) | ~v1_relat_1(X0))),
% 1.27/0.54    inference(flattening,[],[f23])).
% 1.27/0.54  fof(f23,plain,(
% 1.27/0.54    ! [X0] : (! [X1] : (r4_relat_2(X0,X1) <=> ! [X2,X3] : (X2 = X3 | (~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)))) | ~v1_relat_1(X0))),
% 1.27/0.54    inference(ennf_transformation,[],[f10])).
% 1.27/0.54  fof(f10,axiom,(
% 1.27/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r4_relat_2(X0,X1) <=> ! [X2,X3] : ((r2_hidden(k4_tarski(X3,X2),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => X2 = X3)))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_2)).
% 1.38/0.55  % (28415)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.38/0.55  % (28418)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.38/0.55  % (28405)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.38/0.55  % (28407)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.38/0.55  % (28413)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.38/0.55  % (28410)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.38/0.55  % (28419)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.38/0.55  % (28414)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.38/0.55  % (28401)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.38/0.56  % (28400)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.38/0.56  % (28409)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.38/0.56  % (28404)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.38/0.56  % (28406)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.38/0.56  % (28411)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.38/0.56  % (28412)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.38/0.57  % (28401)Refutation not found, incomplete strategy% (28401)------------------------------
% 1.38/0.57  % (28401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.57  % (28401)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.57  
% 1.38/0.57  % (28401)Memory used [KB]: 10746
% 1.38/0.57  % (28401)Time elapsed: 0.123 s
% 1.38/0.57  % (28401)------------------------------
% 1.38/0.57  % (28401)------------------------------
% 1.38/0.57  fof(f89,plain,(
% 1.38/0.57    ( ! [X2,X0,X3,X1] : (~sP1(X2) | ~r2_hidden(k4_tarski(X1,X0),X2) | ~r2_hidden(X0,X3) | ~r2_hidden(X1,X3) | X0 = X1 | ~r4_relat_2(X2,X3) | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 1.38/0.57    inference(resolution,[],[f66,f64])).
% 1.38/0.57  fof(f64,plain,(
% 1.38/0.57    ( ! [X0,X1] : (sP0(X0,X1) | ~r4_relat_2(X0,X1) | ~sP1(X0)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f41])).
% 1.38/0.57  fof(f41,plain,(
% 1.38/0.57    ! [X0] : (! [X1] : ((r4_relat_2(X0,X1) | ~sP0(X0,X1)) & (sP0(X0,X1) | ~r4_relat_2(X0,X1))) | ~sP1(X0))),
% 1.38/0.57    inference(nnf_transformation,[],[f33])).
% 1.38/0.57  fof(f66,plain,(
% 1.38/0.57    ( ! [X4,X0,X5,X1] : (~sP0(X0,X1) | ~r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | X4 = X5) )),
% 1.38/0.57    inference(cnf_transformation,[],[f45])).
% 1.38/0.57  fof(f45,plain,(
% 1.38/0.57    ! [X0,X1] : ((sP0(X0,X1) | (sK5(X0,X1) != sK6(X0,X1) & r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) & r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) & r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK5(X0,X1),X1))) & (! [X4,X5] : (X4 = X5 | ~r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) | ~sP0(X0,X1)))),
% 1.38/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f43,f44])).
% 1.38/0.57  fof(f44,plain,(
% 1.38/0.57    ! [X1,X0] : (? [X2,X3] : (X2 != X3 & r2_hidden(k4_tarski(X3,X2),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => (sK5(X0,X1) != sK6(X0,X1) & r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) & r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) & r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK5(X0,X1),X1)))),
% 1.38/0.57    introduced(choice_axiom,[])).
% 1.38/0.57  fof(f43,plain,(
% 1.38/0.57    ! [X0,X1] : ((sP0(X0,X1) | ? [X2,X3] : (X2 != X3 & r2_hidden(k4_tarski(X3,X2),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1))) & (! [X4,X5] : (X4 = X5 | ~r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) | ~sP0(X0,X1)))),
% 1.38/0.57    inference(rectify,[],[f42])).
% 1.38/0.57  fof(f42,plain,(
% 1.38/0.57    ! [X0,X1] : ((sP0(X0,X1) | ? [X2,X3] : (X2 != X3 & r2_hidden(k4_tarski(X3,X2),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1))) & (! [X2,X3] : (X2 = X3 | ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)) | ~sP0(X0,X1)))),
% 1.38/0.57    inference(nnf_transformation,[],[f32])).
% 1.38/0.57  fof(f53,plain,(
% 1.38/0.57    m1_subset_1(sK4,u1_struct_0(sK2))),
% 1.38/0.57    inference(cnf_transformation,[],[f38])).
% 1.38/0.57  fof(f191,plain,(
% 1.38/0.57    ~m1_subset_1(sK4,k1_xboole_0)),
% 1.38/0.57    inference(resolution,[],[f189,f55])).
% 1.38/0.57  fof(f189,plain,(
% 1.38/0.57    ( ! [X0] : (~r1_orders_2(sK2,X0,sK3) | ~m1_subset_1(X0,k1_xboole_0)) )),
% 1.38/0.57    inference(resolution,[],[f184,f122])).
% 1.38/0.57  fof(f122,plain,(
% 1.38/0.57    m1_subset_1(sK3,k1_xboole_0)),
% 1.38/0.57    inference(backward_demodulation,[],[f52,f121])).
% 1.38/0.57  fof(f184,plain,(
% 1.38/0.57    ( ! [X2,X3] : (~m1_subset_1(X3,k1_xboole_0) | ~m1_subset_1(X2,k1_xboole_0) | ~r1_orders_2(sK2,X2,X3)) )),
% 1.38/0.57    inference(forward_demodulation,[],[f183,f121])).
% 1.38/0.57  fof(f183,plain,(
% 1.38/0.57    ( ! [X2,X3] : (~m1_subset_1(X3,k1_xboole_0) | ~r1_orders_2(sK2,X2,X3) | ~m1_subset_1(X2,u1_struct_0(sK2))) )),
% 1.38/0.57    inference(forward_demodulation,[],[f182,f121])).
% 1.38/0.57  fof(f182,plain,(
% 1.38/0.57    ( ! [X2,X3] : (~r1_orders_2(sK2,X2,X3) | ~m1_subset_1(X3,u1_struct_0(sK2)) | ~m1_subset_1(X2,u1_struct_0(sK2))) )),
% 1.38/0.57    inference(subsumption_resolution,[],[f181,f51])).
% 1.38/0.57  fof(f181,plain,(
% 1.38/0.57    ( ! [X2,X3] : (~r1_orders_2(sK2,X2,X3) | ~m1_subset_1(X3,u1_struct_0(sK2)) | ~m1_subset_1(X2,u1_struct_0(sK2)) | ~l1_orders_2(sK2)) )),
% 1.38/0.57    inference(subsumption_resolution,[],[f179,f131])).
% 1.38/0.57  fof(f131,plain,(
% 1.38/0.57    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 1.38/0.57    inference(backward_demodulation,[],[f120,f121])).
% 1.38/0.57  fof(f120,plain,(
% 1.38/0.57    ( ! [X1] : (~r2_hidden(X1,u1_struct_0(sK2))) )),
% 1.38/0.57    inference(resolution,[],[f118,f74])).
% 1.38/0.57  fof(f74,plain,(
% 1.38/0.57    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f49])).
% 1.38/0.57  fof(f49,plain,(
% 1.38/0.57    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK7(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.38/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f47,f48])).
% 1.38/0.57  fof(f48,plain,(
% 1.38/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK7(X0),X0))),
% 1.38/0.57    introduced(choice_axiom,[])).
% 1.38/0.57  fof(f47,plain,(
% 1.38/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.38/0.57    inference(rectify,[],[f46])).
% 1.38/0.57  fof(f46,plain,(
% 1.38/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.38/0.57    inference(nnf_transformation,[],[f1])).
% 1.38/0.57  fof(f1,axiom,(
% 1.38/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.38/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.38/0.57  fof(f179,plain,(
% 1.38/0.57    ( ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),k1_xboole_0) | ~r1_orders_2(sK2,X2,X3) | ~m1_subset_1(X3,u1_struct_0(sK2)) | ~m1_subset_1(X2,u1_struct_0(sK2)) | ~l1_orders_2(sK2)) )),
% 1.38/0.57    inference(superposition,[],[f61,f163])).
% 1.38/0.57  fof(f163,plain,(
% 1.38/0.57    k1_xboole_0 = u1_orders_2(sK2)),
% 1.38/0.57    inference(resolution,[],[f159,f73])).
% 1.38/0.57  fof(f159,plain,(
% 1.38/0.57    v1_xboole_0(u1_orders_2(sK2))),
% 1.38/0.57    inference(subsumption_resolution,[],[f154,f57])).
% 1.38/0.57  fof(f57,plain,(
% 1.38/0.57    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f3])).
% 1.38/0.57  fof(f3,axiom,(
% 1.38/0.57    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.38/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.38/0.57  fof(f154,plain,(
% 1.38/0.57    ~r1_xboole_0(u1_orders_2(sK2),k1_xboole_0) | v1_xboole_0(u1_orders_2(sK2))),
% 1.38/0.57    inference(backward_demodulation,[],[f127,f150])).
% 1.38/0.57  fof(f150,plain,(
% 1.38/0.57    ( ! [X4] : (k1_xboole_0 = k2_zfmisc_1(X4,k1_xboole_0)) )),
% 1.38/0.57    inference(resolution,[],[f130,f73])).
% 1.38/0.57  fof(f130,plain,(
% 1.38/0.57    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0))) )),
% 1.38/0.57    inference(backward_demodulation,[],[f119,f121])).
% 1.38/0.57  fof(f119,plain,(
% 1.38/0.57    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(X0,u1_struct_0(sK2)))) )),
% 1.38/0.57    inference(resolution,[],[f118,f78])).
% 1.38/0.57  fof(f78,plain,(
% 1.38/0.57    ( ! [X0,X1] : (~v1_xboole_0(X1) | v1_xboole_0(k2_zfmisc_1(X0,X1))) )),
% 1.38/0.57    inference(cnf_transformation,[],[f28])).
% 1.38/0.57  fof(f28,plain,(
% 1.38/0.57    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 1.38/0.57    inference(ennf_transformation,[],[f5])).
% 1.38/0.57  fof(f5,axiom,(
% 1.38/0.57    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 1.38/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).
% 1.38/0.57  fof(f127,plain,(
% 1.38/0.57    ~r1_xboole_0(u1_orders_2(sK2),k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) | v1_xboole_0(u1_orders_2(sK2))),
% 1.38/0.57    inference(backward_demodulation,[],[f88,f121])).
% 1.38/0.57  fof(f88,plain,(
% 1.38/0.57    ~r1_xboole_0(u1_orders_2(sK2),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) | v1_xboole_0(u1_orders_2(sK2))),
% 1.38/0.57    inference(resolution,[],[f85,f77])).
% 1.38/0.57  fof(f77,plain,(
% 1.38/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0) | v1_xboole_0(X1)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f27])).
% 1.38/0.57  fof(f27,plain,(
% 1.38/0.57    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 1.38/0.57    inference(flattening,[],[f26])).
% 1.38/0.57  fof(f26,plain,(
% 1.38/0.57    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 1.38/0.57    inference(ennf_transformation,[],[f4])).
% 1.38/0.57  fof(f4,axiom,(
% 1.38/0.57    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 1.38/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 1.38/0.57  fof(f85,plain,(
% 1.38/0.57    r1_tarski(u1_orders_2(sK2),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))),
% 1.38/0.57    inference(resolution,[],[f83,f80])).
% 1.38/0.57  fof(f80,plain,(
% 1.38/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f31])).
% 1.38/0.57  fof(f31,plain,(
% 1.38/0.57    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 1.38/0.57    inference(ennf_transformation,[],[f16])).
% 1.38/0.57  fof(f16,plain,(
% 1.38/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 1.38/0.57    inference(unused_predicate_definition_removal,[],[f7])).
% 1.38/0.57  fof(f7,axiom,(
% 1.38/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.38/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.38/0.57  % SZS output end Proof for theBenchmark
% 1.38/0.57  % (28398)------------------------------
% 1.38/0.57  % (28398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.57  % (28398)Termination reason: Refutation
% 1.38/0.57  
% 1.38/0.57  % (28398)Memory used [KB]: 6268
% 1.38/0.57  % (28398)Time elapsed: 0.107 s
% 1.38/0.57  % (28398)------------------------------
% 1.38/0.57  % (28398)------------------------------
% 1.38/0.57  % (28396)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.38/0.57  % (28394)Success in time 0.198 s
%------------------------------------------------------------------------------
