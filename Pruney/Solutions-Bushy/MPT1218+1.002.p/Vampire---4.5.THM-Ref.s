%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1218+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:30 EST 2020

% Result     : Theorem 4.39s
% Output     : Refutation 4.61s
% Verified   : 
% Statistics : Number of formulae       :  137 (1652 expanded)
%              Number of leaves         :   18 ( 324 expanded)
%              Depth                    :   30
%              Number of atoms          :  570 (9057 expanded)
%              Number of equality atoms :   30 ( 797 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3081,plain,(
    $false ),
    inference(global_subsumption,[],[f286,f362,f3076])).

fof(f3076,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f3075,f2900])).

fof(f2900,plain,(
    ! [X4] :
      ( r2_hidden(sK8(u1_struct_0(sK0),sK1,X4),sK1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK1 = X4 ) ),
    inference(global_subsumption,[],[f2342])).

fof(f2342,plain,(
    ! [X28] :
      ( r2_hidden(sK8(u1_struct_0(sK0),sK1,X28),sK1)
      | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK1 = X28 ) ),
    inference(resolution,[],[f2310,f308])).

fof(f308,plain,(
    ! [X8] :
      ( m1_subset_1(sK8(u1_struct_0(sK0),sK1,X8),u1_struct_0(sK0))
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK1 = X8 ) ),
    inference(resolution,[],[f67,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(sK8(X0,X1,X2),X0)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).

fof(f67,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_struct_0(X0) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v19_lattices(X1,X0)
          & v18_lattices(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_struct_0(X0) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v19_lattices(X1,X0)
          & v18_lattices(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v19_lattices(X1,X0)
              & v18_lattices(X1,X0)
              & ~ v1_xboole_0(X1) )
           => k2_struct_0(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v19_lattices(X1,X0)
            & v18_lattices(X1,X0)
            & ~ v1_xboole_0(X1) )
         => k2_struct_0(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_lattices)).

fof(f2310,plain,(
    ! [X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(sK0))
      | r2_hidden(X9,sK1) ) ),
    inference(global_subsumption,[],[f2304])).

fof(f2304,plain,(
    ! [X2] :
      ( r2_hidden(X2,sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f2230,f2299])).

fof(f2299,plain,(
    ! [X2] :
      ( ~ r2_hidden(k4_lattices(sK0,sK7(sK1),X2),sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r2_hidden(X2,sK1) ) ),
    inference(duplicate_literal_removal,[],[f2291])).

fof(f2291,plain,(
    ! [X2] :
      ( ~ r2_hidden(k4_lattices(sK0,sK7(sK1),X2),sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r2_hidden(X2,sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f2272,f1486])).

fof(f1486,plain,(
    ! [X0] :
      ( r3_lattices(sK0,k4_lattices(sK0,sK7(sK1),X0),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f69,f147,f209,f525,f1481])).

fof(f1481,plain,(
    ! [X0] :
      ( r3_lattices(sK0,k4_lattices(sK0,sK7(sK1),X0),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ v6_lattices(sK0)
      | ~ l1_lattices(sK0)
      | ~ m1_subset_1(sK7(sK1),u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f1478])).

fof(f1478,plain,(
    ! [X0] :
      ( r3_lattices(sK0,k4_lattices(sK0,sK7(sK1),X0),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ v6_lattices(sK0)
      | ~ l1_lattices(sK0)
      | ~ m1_subset_1(sK7(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f1291,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(f1291,plain,(
    ! [X0] :
      ( r3_lattices(sK0,k4_lattices(sK0,X0,sK7(sK1)),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f69,f71,f147,f148,f149,f555,f1290])).

fof(f1290,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ v6_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(k4_lattices(sK0,X0,sK7(sK1)),u1_struct_0(sK0))
      | r3_lattices(sK0,k4_lattices(sK0,X0,sK7(sK1)),X0) ) ),
    inference(duplicate_literal_removal,[],[f1285])).

fof(f1285,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ v6_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(k4_lattices(sK0,X0,sK7(sK1)),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r3_lattices(sK0,k4_lattices(sK0,X0,sK7(sK1)),X0) ) ),
    inference(resolution,[],[f549,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattices(X0,X1,X2)
      | r3_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f549,plain,(
    ! [X8] :
      ( r1_lattices(sK0,k4_lattices(sK0,X8,sK7(sK1)),X8)
      | ~ m1_subset_1(X8,u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f69,f71,f147,f148,f532])).

fof(f532,plain,(
    ! [X8] :
      ( v2_struct_0(sK0)
      | ~ v6_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | r1_lattices(sK0,k4_lattices(sK0,X8,sK7(sK1)),X8) ) ),
    inference(resolution,[],[f525,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattices(X0,k4_lattices(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => r1_lattices(X0,k4_lattices(X0,X1,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_lattices)).

fof(f555,plain,(
    ! [X14] :
      ( m1_subset_1(k4_lattices(sK0,X14,sK7(sK1)),u1_struct_0(sK0))
      | ~ m1_subset_1(X14,u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f69,f147,f209,f538])).

fof(f538,plain,(
    ! [X14] :
      ( v2_struct_0(sK0)
      | ~ v6_lattices(sK0)
      | ~ l1_lattices(sK0)
      | ~ m1_subset_1(X14,u1_struct_0(sK0))
      | m1_subset_1(k4_lattices(sK0,X14,sK7(sK1)),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f525,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_lattices)).

fof(f149,plain,(
    v9_lattices(sK0) ),
    inference(global_subsumption,[],[f71,f70,f124])).

fof(f124,plain,
    ( ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v9_lattices(sK0) ),
    inference(resolution,[],[f69,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(f70,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f148,plain,(
    v8_lattices(sK0) ),
    inference(global_subsumption,[],[f71,f70,f123])).

fof(f123,plain,
    ( ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v8_lattices(sK0) ),
    inference(resolution,[],[f69,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f71,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f525,plain,(
    m1_subset_1(sK7(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f333,f67])).

fof(f333,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
      | m1_subset_1(sK7(sK1),X0) ) ),
    inference(resolution,[],[f331,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f331,plain,(
    r2_hidden(sK7(sK1),sK1) ),
    inference(resolution,[],[f121,f101])).

fof(f101,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f121,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f64,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f64,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f209,plain,(
    l1_lattices(sK0) ),
    inference(resolution,[],[f71,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f147,plain,(
    v6_lattices(sK0) ),
    inference(global_subsumption,[],[f71,f70,f122])).

fof(f122,plain,
    ( ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v6_lattices(sK0) ),
    inference(resolution,[],[f69,f78])).

fof(f78,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f69,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f2272,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK0,X0,X1)
      | ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X1,sK1) ) ),
    inference(global_subsumption,[],[f310,f282])).

fof(f282,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X1,sK1)
      | ~ r3_lattices(sK0,X0,X1)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(global_subsumption,[],[f67,f69,f70,f71,f281])).

fof(f281,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X0,X1)
      | ~ r2_hidden(X0,sK1)
      | r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f66,f94])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r3_lattices(X0,X2,X3)
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X3,X1)
      | ~ v19_lattices(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v19_lattices(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ r3_lattices(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v19_lattices(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ r3_lattices(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v19_lattices(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r2_hidden(X2,X1)
                        & r3_lattices(X0,X2,X3) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d23_lattices)).

fof(f66,plain,(
    v19_lattices(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f310,plain,(
    ! [X10] :
      ( m1_subset_1(X10,u1_struct_0(sK0))
      | ~ r2_hidden(X10,sK1) ) ),
    inference(resolution,[],[f67,f115])).

fof(f2230,plain,(
    ! [X3] :
      ( r2_hidden(k4_lattices(sK0,sK7(sK1),X3),sK1)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f331,f525,f556,f2220])).

fof(f2220,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK7(sK1),sK1)
      | ~ m1_subset_1(sK7(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(k4_lattices(sK0,sK7(sK1),X3),u1_struct_0(sK0))
      | r2_hidden(k4_lattices(sK0,sK7(sK1),X3),sK1)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f270,f1981])).

fof(f1981,plain,(
    ! [X0] :
      ( r3_lattices(sK0,k4_lattices(sK0,sK7(sK1),X0),sK7(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f525,f556,f1975])).

fof(f1975,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK7(sK1),u1_struct_0(sK0))
      | r3_lattices(sK0,k4_lattices(sK0,sK7(sK1),X0),sK7(sK1))
      | ~ m1_subset_1(k4_lattices(sK0,sK7(sK1),X0),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f550,f167])).

fof(f167,plain,(
    ! [X21,X20] :
      ( ~ r1_lattices(sK0,X20,X21)
      | ~ m1_subset_1(X21,u1_struct_0(sK0))
      | r3_lattices(sK0,X20,X21)
      | ~ m1_subset_1(X20,u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f71,f147,f148,f149,f143])).

fof(f143,plain,(
    ! [X21,X20] :
      ( ~ v6_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X20,u1_struct_0(sK0))
      | ~ m1_subset_1(X21,u1_struct_0(sK0))
      | ~ r1_lattices(sK0,X20,X21)
      | r3_lattices(sK0,X20,X21) ) ),
    inference(resolution,[],[f69,f110])).

fof(f550,plain,(
    ! [X9] :
      ( r1_lattices(sK0,k4_lattices(sK0,sK7(sK1),X9),sK7(sK1))
      | ~ m1_subset_1(X9,u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f69,f71,f147,f148,f533])).

fof(f533,plain,(
    ! [X9] :
      ( v2_struct_0(sK0)
      | ~ v6_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | r1_lattices(sK0,k4_lattices(sK0,sK7(sK1),X9),sK7(sK1)) ) ),
    inference(resolution,[],[f525,f100])).

fof(f270,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK0,X0,X1)
      | ~ r2_hidden(X1,sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,sK1) ) ),
    inference(global_subsumption,[],[f67,f69,f70,f71,f269])).

fof(f269,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X0,X1)
      | ~ r2_hidden(X1,sK1)
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f65,f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r3_lattices(X0,X2,X3)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X2,X1)
      | ~ v18_lattices(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v18_lattices(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X2,X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r3_lattices(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v18_lattices(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X2,X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r3_lattices(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v18_lattices(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r2_hidden(X3,X1)
                        & r3_lattices(X0,X2,X3) )
                     => r2_hidden(X2,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d22_lattices)).

fof(f65,plain,(
    v18_lattices(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f556,plain,(
    ! [X15] :
      ( m1_subset_1(k4_lattices(sK0,sK7(sK1),X15),u1_struct_0(sK0))
      | ~ m1_subset_1(X15,u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f69,f147,f209,f539])).

fof(f539,plain,(
    ! [X15] :
      ( v2_struct_0(sK0)
      | ~ v6_lattices(sK0)
      | ~ l1_lattices(sK0)
      | ~ m1_subset_1(X15,u1_struct_0(sK0))
      | m1_subset_1(k4_lattices(sK0,sK7(sK1),X15),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f525,f112])).

fof(f3075,plain,(
    ~ r2_hidden(sK8(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1) ),
    inference(global_subsumption,[],[f286,f362,f3068])).

fof(f3068,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = u1_struct_0(sK0)
    | ~ r2_hidden(sK8(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1) ),
    inference(resolution,[],[f2984,f1564])).

fof(f1564,plain,(
    ! [X36] :
      ( r2_hidden(X36,u1_struct_0(sK0))
      | ~ r2_hidden(X36,sK1) ) ),
    inference(global_subsumption,[],[f311,f338,f412])).

fof(f412,plain,(
    ! [X36] :
      ( ~ r2_hidden(X36,sK1)
      | v1_xboole_0(u1_struct_0(sK0))
      | r2_hidden(X36,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f310,f103])).

fof(f338,plain,(
    ~ sP10(sK1) ),
    inference(resolution,[],[f331,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP10(X1) ) ),
    inference(general_splitting,[],[f116,f119_D])).

fof(f119,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP10(X1) ) ),
    inference(cnf_transformation,[],[f119_D])).

fof(f119_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP10(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP10])])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f311,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | sP10(sK1) ),
    inference(resolution,[],[f67,f119])).

fof(f2984,plain,(
    ! [X6] :
      ( ~ r2_hidden(sK8(u1_struct_0(sK0),sK1,X6),X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK1 = X6 ) ),
    inference(global_subsumption,[],[f2921])).

fof(f2921,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK8(u1_struct_0(sK0),sK1,X0),X0)
      | sK1 = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(global_subsumption,[],[f67,f2920])).

fof(f2920,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK1 = X0
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK8(u1_struct_0(sK0),sK1,X0),X0) ) ),
    inference(duplicate_literal_removal,[],[f2911])).

fof(f2911,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK1 = X0
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK8(u1_struct_0(sK0),sK1,X0),X0)
      | sK1 = X0 ) ),
    inference(resolution,[],[f2900,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r2_hidden(sK8(X0,X1,X2),X2)
      | ~ r2_hidden(sK8(X0,X1,X2),X1)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f362,plain,(
    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f283,f284])).

fof(f284,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f275,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f275,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f209,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ l1_lattices(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_lattices(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_lattices(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_lattices)).

fof(f283,plain,(
    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f275,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f286,plain,(
    sK1 != u1_struct_0(sK0) ),
    inference(global_subsumption,[],[f275,f285])).

fof(f285,plain,
    ( sK1 != u1_struct_0(sK0)
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f68,f82])).

fof(f68,plain,(
    sK1 != k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

%------------------------------------------------------------------------------
