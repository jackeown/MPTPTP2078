%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1557+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:05 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 202 expanded)
%              Number of leaves         :    8 (  38 expanded)
%              Depth                    :   24
%              Number of atoms          :  238 ( 752 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f197,plain,(
    $false ),
    inference(subsumption_resolution,[],[f196,f27])).

fof(f27,plain,(
    ~ r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
          & r2_yellow_0(X0,X2)
          & r2_yellow_0(X0,X1)
          & r1_tarski(X1,X2) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
          & r2_yellow_0(X0,X2)
          & r2_yellow_0(X0,X1)
          & r1_tarski(X1,X2) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1,X2] :
            ( ( r2_yellow_0(X0,X2)
              & r2_yellow_0(X0,X1)
              & r1_tarski(X1,X2) )
           => r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( ( r2_yellow_0(X0,X2)
            & r2_yellow_0(X0,X1)
            & r1_tarski(X1,X2) )
         => r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_yellow_0)).

fof(f196,plain,(
    r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f195,f28])).

fof(f28,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

% (32194)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f195,plain,
    ( ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f194,f48])).

fof(f48,plain,(
    ! [X0] : m1_subset_1(k2_yellow_0(sK0,X0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f38,f28])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_0)).

fof(f194,plain,
    ( ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f185,f25])).

fof(f25,plain,(
    r2_yellow_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f185,plain,
    ( ~ r2_yellow_0(sK0,sK1)
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1)) ),
    inference(resolution,[],[f167,f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_lattice3(X0,X1,X3)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X3,k2_yellow_0(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f44,f38])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X3)
      | r1_orders_2(X0,X3,k2_yellow_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X3)
      | r1_orders_2(X0,X3,X2)
      | k2_yellow_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k2_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2) ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k2_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2) ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_yellow_0(X0,X1)
           => ( k2_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r1_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X3,X2) ) )
                & r1_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_yellow_0)).

fof(f167,plain,(
    r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f166,f28])).

fof(f166,plain,
    ( r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK2))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f165,f48])).

fof(f165,plain,
    ( r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(duplicate_literal_removal,[],[f164])).

fof(f164,plain,
    ( r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK2)) ),
    inference(resolution,[],[f159,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).

fof(f159,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,k2_yellow_0(sK0,sK2),sK4(sK0,sK1,k2_yellow_0(sK0,X0)))
      | r1_lattice3(sK0,sK1,k2_yellow_0(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f158,f48])).

fof(f158,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
      | r1_orders_2(sK0,k2_yellow_0(sK0,sK2),sK4(sK0,sK1,k2_yellow_0(sK0,X0)))
      | r1_lattice3(sK0,sK1,k2_yellow_0(sK0,X0)) ) ),
    inference(resolution,[],[f114,f53])).

fof(f53,plain,(
    r1_lattice3(sK0,sK2,k2_yellow_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f51,f28])).

fof(f51,plain,
    ( ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,sK2,k2_yellow_0(sK0,sK2)) ),
    inference(resolution,[],[f46,f26])).

fof(f26,plain,(
    r2_yellow_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,k2_yellow_0(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f43,f38])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X1,k2_yellow_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X1,X2)
      | k2_yellow_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f114,plain,(
    ! [X4,X5] :
      ( ~ r1_lattice3(sK0,sK2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r1_orders_2(sK0,X5,sK4(sK0,sK1,k2_yellow_0(sK0,X4)))
      | r1_lattice3(sK0,sK1,k2_yellow_0(sK0,X4)) ) ),
    inference(duplicate_literal_removal,[],[f113])).

fof(f113,plain,(
    ! [X4,X5] :
      ( r1_lattice3(sK0,sK1,k2_yellow_0(sK0,X4))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r1_lattice3(sK0,sK1,k2_yellow_0(sK0,X4))
      | r1_orders_2(sK0,X5,sK4(sK0,sK1,k2_yellow_0(sK0,X4)))
      | ~ r1_lattice3(sK0,sK2,X5) ) ),
    inference(resolution,[],[f105,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK4(sK0,X0,k2_yellow_0(sK0,X1)),X3)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_lattice3(sK0,X0,k2_yellow_0(sK0,X1))
      | r1_orders_2(sK0,X2,sK4(sK0,X0,k2_yellow_0(sK0,X1)))
      | ~ r1_lattice3(sK0,X3,X2) ) ),
    inference(subsumption_resolution,[],[f79,f28])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(sK0,X0,k2_yellow_0(sK0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ r2_hidden(sK4(sK0,X0,k2_yellow_0(sK0,X1)),X3)
      | r1_orders_2(sK0,X2,sK4(sK0,X0,k2_yellow_0(sK0,X1)))
      | ~ r1_lattice3(sK0,X3,X2) ) ),
    inference(resolution,[],[f59,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X2,X3)
      | ~ r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f59,plain,(
    ! [X4,X3] :
      ( m1_subset_1(sK4(sK0,X3,k2_yellow_0(sK0,X4)),u1_struct_0(sK0))
      | r1_lattice3(sK0,X3,k2_yellow_0(sK0,X4)) ) ),
    inference(subsumption_resolution,[],[f55,f28])).

fof(f55,plain,(
    ! [X4,X3] :
      ( ~ l1_orders_2(sK0)
      | m1_subset_1(sK4(sK0,X3,k2_yellow_0(sK0,X4)),u1_struct_0(sK0))
      | r1_lattice3(sK0,X3,k2_yellow_0(sK0,X4)) ) ),
    inference(resolution,[],[f48,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f105,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK0,sK1,k2_yellow_0(sK0,X0)),sK2)
      | r1_lattice3(sK0,sK1,k2_yellow_0(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f104,f87])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK2)
      | r1_lattice3(sK0,sK1,k2_yellow_0(sK0,X0)) ) ),
    inference(resolution,[],[f78,f47])).

fof(f47,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK2)) ),
    inference(resolution,[],[f40,f24])).

fof(f24,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f78,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(X5))
      | r1_lattice3(sK0,X3,k2_yellow_0(sK0,X4))
      | ~ v1_xboole_0(X5) ) ),
    inference(resolution,[],[f60,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f60,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK4(sK0,X5,k2_yellow_0(sK0,X6)),X5)
      | r1_lattice3(sK0,X5,k2_yellow_0(sK0,X6)) ) ),
    inference(subsumption_resolution,[],[f56,f28])).

fof(f56,plain,(
    ! [X6,X5] :
      ( ~ l1_orders_2(sK0)
      | r2_hidden(sK4(sK0,X5,k2_yellow_0(sK0,X6)),X5)
      | r1_lattice3(sK0,X5,k2_yellow_0(sK0,X6)) ) ),
    inference(resolution,[],[f48,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f104,plain,(
    ! [X0] :
      ( r1_lattice3(sK0,sK1,k2_yellow_0(sK0,X0))
      | v1_xboole_0(sK2)
      | r2_hidden(sK4(sK0,sK1,k2_yellow_0(sK0,X0)),sK2) ) ),
    inference(resolution,[],[f88,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f88,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(sK0,sK1,k2_yellow_0(sK0,X0)),sK2)
      | r1_lattice3(sK0,sK1,k2_yellow_0(sK0,X0)) ) ),
    inference(resolution,[],[f77,f47])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X2))
      | r1_lattice3(sK0,X0,k2_yellow_0(sK0,X1))
      | m1_subset_1(sK4(sK0,X0,k2_yellow_0(sK0,X1)),X2) ) ),
    inference(resolution,[],[f60,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

%------------------------------------------------------------------------------
