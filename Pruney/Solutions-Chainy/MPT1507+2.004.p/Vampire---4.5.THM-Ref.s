%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 146 expanded)
%              Number of leaves         :    3 (  25 expanded)
%              Depth                    :   18
%              Number of atoms          :  246 ( 971 expanded)
%              Number of equality atoms :   34 ( 121 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f221,plain,(
    $false ),
    inference(subsumption_resolution,[],[f220,f13])).

fof(f13,plain,(
    sK1 != k15_lattice3(sK0,sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k15_lattice3(X0,X2) != X1
              & r4_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k15_lattice3(X0,X2) != X1
              & r4_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( r4_lattice3(X0,X1,X2)
                  & r2_hidden(X1,X2) )
               => k15_lattice3(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
             => k15_lattice3(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_lattice3)).

fof(f220,plain,(
    sK1 = k15_lattice3(sK0,sK2) ),
    inference(subsumption_resolution,[],[f213,f12])).

fof(f12,plain,(
    r4_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f213,plain,
    ( ~ r4_lattice3(sK0,sK1,sK2)
    | sK1 = k15_lattice3(sK0,sK2) ),
    inference(resolution,[],[f212,f122])).

fof(f122,plain,(
    r4_lattice3(sK0,sK3(sK0,sK2,sK1),sK2) ),
    inference(subsumption_resolution,[],[f121,f13])).

fof(f121,plain,
    ( r4_lattice3(sK0,sK3(sK0,sK2,sK1),sK2)
    | sK1 = k15_lattice3(sK0,sK2) ),
    inference(subsumption_resolution,[],[f114,f14])).

fof(f14,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f114,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r4_lattice3(sK0,sK3(sK0,sK2,sK1),sK2)
    | sK1 = k15_lattice3(sK0,sK2) ),
    inference(resolution,[],[f54,f12])).

fof(f54,plain,(
    ! [X2,X3] :
      ( ~ r4_lattice3(sK0,X2,X3)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r4_lattice3(sK0,sK3(sK0,X3,X2),X3)
      | k15_lattice3(sK0,X3) = X2 ) ),
    inference(subsumption_resolution,[],[f53,f18])).

fof(f18,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X2,X3] :
      ( ~ l3_lattices(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X2,X3)
      | r4_lattice3(sK0,sK3(sK0,X3,X2),X3)
      | k15_lattice3(sK0,X3) = X2 ) ),
    inference(subsumption_resolution,[],[f52,f16])).

fof(f16,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X2,X3] :
      ( ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X2,X3)
      | r4_lattice3(sK0,sK3(sK0,X3,X2),X3)
      | k15_lattice3(sK0,X3) = X2 ) ),
    inference(subsumption_resolution,[],[f45,f15])).

fof(f15,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X2,X3] :
      ( v2_struct_0(sK0)
      | ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X2,X3)
      | r4_lattice3(sK0,sK3(sK0,X3,X2),X3)
      | k15_lattice3(sK0,X3) = X2 ) ),
    inference(resolution,[],[f17,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X2,X1)
      | r4_lattice3(X0,sK3(X0,X1,X2),X1)
      | k15_lattice3(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k15_lattice3(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k15_lattice3(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( m1_subset_1(X2,u1_struct_0(X0))
           => ( k15_lattice3(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r4_lattice3(X0,X3,X1)
                     => r1_lattices(X0,X2,X3) ) )
                & r4_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).

fof(f17,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f212,plain,(
    ! [X4] :
      ( ~ r4_lattice3(sK0,sK3(sK0,X4,sK1),sK2)
      | ~ r4_lattice3(sK0,sK1,X4)
      | sK1 = k15_lattice3(sK0,X4) ) ),
    inference(subsumption_resolution,[],[f211,f14])).

fof(f211,plain,(
    ! [X4] :
      ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | sK1 = k15_lattice3(sK0,X4)
      | ~ r4_lattice3(sK0,sK1,X4)
      | ~ r4_lattice3(sK0,sK3(sK0,X4,sK1),sK2) ) ),
    inference(resolution,[],[f157,f11])).

fof(f11,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f157,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X2,X4)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k15_lattice3(sK0,X3) = X2
      | ~ r4_lattice3(sK0,X2,X3)
      | ~ r4_lattice3(sK0,sK3(sK0,X3,X2),X4) ) ),
    inference(subsumption_resolution,[],[f156,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r4_lattice3(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_subset_1(sK3(sK0,X1,X0),u1_struct_0(sK0))
      | k15_lattice3(sK0,X1) = X0 ) ),
    inference(subsumption_resolution,[],[f50,f18])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X0,X1)
      | m1_subset_1(sK3(sK0,X1,X0),u1_struct_0(sK0))
      | k15_lattice3(sK0,X1) = X0 ) ),
    inference(subsumption_resolution,[],[f49,f16])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X0,X1)
      | m1_subset_1(sK3(sK0,X1,X0),u1_struct_0(sK0))
      | k15_lattice3(sK0,X1) = X0 ) ),
    inference(subsumption_resolution,[],[f44,f15])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X0,X1)
      | m1_subset_1(sK3(sK0,X1,X0),u1_struct_0(sK0))
      | k15_lattice3(sK0,X1) = X0 ) ),
    inference(resolution,[],[f17,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X2,X1)
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | k15_lattice3(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f156,plain,(
    ! [X4,X2,X3] :
      ( ~ r4_lattice3(sK0,X2,X3)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k15_lattice3(sK0,X3) = X2
      | ~ m1_subset_1(sK3(sK0,X3,X2),u1_struct_0(sK0))
      | ~ r2_hidden(X2,X4)
      | ~ r4_lattice3(sK0,sK3(sK0,X3,X2),X4) ) ),
    inference(subsumption_resolution,[],[f155,f18])).

fof(f155,plain,(
    ! [X4,X2,X3] :
      ( ~ r4_lattice3(sK0,X2,X3)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k15_lattice3(sK0,X3) = X2
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(sK3(sK0,X3,X2),u1_struct_0(sK0))
      | ~ r2_hidden(X2,X4)
      | ~ r4_lattice3(sK0,sK3(sK0,X3,X2),X4) ) ),
    inference(subsumption_resolution,[],[f154,f15])).

fof(f154,plain,(
    ! [X4,X2,X3] :
      ( ~ r4_lattice3(sK0,X2,X3)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k15_lattice3(sK0,X3) = X2
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(sK3(sK0,X3,X2),u1_struct_0(sK0))
      | ~ r2_hidden(X2,X4)
      | ~ r4_lattice3(sK0,sK3(sK0,X3,X2),X4) ) ),
    inference(duplicate_literal_removal,[],[f153])).

fof(f153,plain,(
    ! [X4,X2,X3] :
      ( ~ r4_lattice3(sK0,X2,X3)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k15_lattice3(sK0,X3) = X2
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(sK3(sK0,X3,X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,X4)
      | ~ r4_lattice3(sK0,sK3(sK0,X3,X2),X4) ) ),
    inference(resolution,[],[f57,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X3,X2)
      | r1_lattices(X0,X3,X1)
      | ~ r4_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).

fof(f57,plain,(
    ! [X4,X5] :
      ( ~ r1_lattices(sK0,X4,sK3(sK0,X5,X4))
      | ~ r4_lattice3(sK0,X4,X5)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | k15_lattice3(sK0,X5) = X4 ) ),
    inference(subsumption_resolution,[],[f56,f18])).

fof(f56,plain,(
    ! [X4,X5] :
      ( ~ l3_lattices(sK0)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X4,X5)
      | ~ r1_lattices(sK0,X4,sK3(sK0,X5,X4))
      | k15_lattice3(sK0,X5) = X4 ) ),
    inference(subsumption_resolution,[],[f55,f16])).

fof(f55,plain,(
    ! [X4,X5] :
      ( ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X4,X5)
      | ~ r1_lattices(sK0,X4,sK3(sK0,X5,X4))
      | k15_lattice3(sK0,X5) = X4 ) ),
    inference(subsumption_resolution,[],[f46,f15])).

fof(f46,plain,(
    ! [X4,X5] :
      ( v2_struct_0(sK0)
      | ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X4,X5)
      | ~ r1_lattices(sK0,X4,sK3(sK0,X5,X4))
      | k15_lattice3(sK0,X5) = X4 ) ),
    inference(resolution,[],[f17,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X2,X1)
      | ~ r1_lattices(X0,X2,sK3(X0,X1,X2))
      | k15_lattice3(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:54:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.40  % (31115)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.42  % (31115)Refutation not found, incomplete strategy% (31115)------------------------------
% 0.20/0.42  % (31115)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (31115)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.42  
% 0.20/0.42  % (31115)Memory used [KB]: 10490
% 0.20/0.42  % (31115)Time elapsed: 0.028 s
% 0.20/0.42  % (31115)------------------------------
% 0.20/0.42  % (31115)------------------------------
% 0.20/0.42  % (31127)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.43  % (31127)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f221,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(subsumption_resolution,[],[f220,f13])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    sK1 != k15_lattice3(sK0,sK2)),
% 0.20/0.43    inference(cnf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : (? [X2] : (k15_lattice3(X0,X2) != X1 & r4_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.20/0.43    inference(flattening,[],[f5])).
% 0.20/0.43  fof(f5,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : (? [X2] : (k15_lattice3(X0,X2) != X1 & (r4_lattice3(X0,X1,X2) & r2_hidden(X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,negated_conjecture,(
% 0.20/0.43    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r4_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k15_lattice3(X0,X2) = X1)))),
% 0.20/0.43    inference(negated_conjecture,[],[f3])).
% 0.20/0.43  fof(f3,conjecture,(
% 0.20/0.43    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r4_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k15_lattice3(X0,X2) = X1)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_lattice3)).
% 0.20/0.43  fof(f220,plain,(
% 0.20/0.43    sK1 = k15_lattice3(sK0,sK2)),
% 0.20/0.43    inference(subsumption_resolution,[],[f213,f12])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    r4_lattice3(sK0,sK1,sK2)),
% 0.20/0.43    inference(cnf_transformation,[],[f6])).
% 0.20/0.43  fof(f213,plain,(
% 0.20/0.43    ~r4_lattice3(sK0,sK1,sK2) | sK1 = k15_lattice3(sK0,sK2)),
% 0.20/0.43    inference(resolution,[],[f212,f122])).
% 0.20/0.43  fof(f122,plain,(
% 0.20/0.43    r4_lattice3(sK0,sK3(sK0,sK2,sK1),sK2)),
% 0.20/0.43    inference(subsumption_resolution,[],[f121,f13])).
% 0.20/0.43  fof(f121,plain,(
% 0.20/0.43    r4_lattice3(sK0,sK3(sK0,sK2,sK1),sK2) | sK1 = k15_lattice3(sK0,sK2)),
% 0.20/0.43    inference(subsumption_resolution,[],[f114,f14])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.43    inference(cnf_transformation,[],[f6])).
% 0.20/0.43  fof(f114,plain,(
% 0.20/0.43    ~m1_subset_1(sK1,u1_struct_0(sK0)) | r4_lattice3(sK0,sK3(sK0,sK2,sK1),sK2) | sK1 = k15_lattice3(sK0,sK2)),
% 0.20/0.43    inference(resolution,[],[f54,f12])).
% 0.20/0.43  fof(f54,plain,(
% 0.20/0.43    ( ! [X2,X3] : (~r4_lattice3(sK0,X2,X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r4_lattice3(sK0,sK3(sK0,X3,X2),X3) | k15_lattice3(sK0,X3) = X2) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f53,f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    l3_lattices(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f6])).
% 0.20/0.43  fof(f53,plain,(
% 0.20/0.43    ( ! [X2,X3] : (~l3_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X2,X3) | r4_lattice3(sK0,sK3(sK0,X3,X2),X3) | k15_lattice3(sK0,X3) = X2) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f52,f16])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    v10_lattices(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f6])).
% 0.20/0.43  fof(f52,plain,(
% 0.20/0.43    ( ! [X2,X3] : (~v10_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X2,X3) | r4_lattice3(sK0,sK3(sK0,X3,X2),X3) | k15_lattice3(sK0,X3) = X2) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f45,f15])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ~v2_struct_0(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f6])).
% 0.20/0.43  fof(f45,plain,(
% 0.20/0.43    ( ! [X2,X3] : (v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X2,X3) | r4_lattice3(sK0,sK3(sK0,X3,X2),X3) | k15_lattice3(sK0,X3) = X2) )),
% 0.20/0.43    inference(resolution,[],[f17,f20])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r4_lattice3(X0,X2,X1) | r4_lattice3(X0,sK3(X0,X1,X2),X1) | k15_lattice3(X0,X1) = X2) )),
% 0.20/0.43    inference(cnf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,plain,(
% 0.20/0.43    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.43    inference(flattening,[],[f7])).
% 0.20/0.43  fof(f7,plain,(
% 0.20/0.43    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    v4_lattice3(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f6])).
% 0.20/0.43  fof(f212,plain,(
% 0.20/0.43    ( ! [X4] : (~r4_lattice3(sK0,sK3(sK0,X4,sK1),sK2) | ~r4_lattice3(sK0,sK1,X4) | sK1 = k15_lattice3(sK0,X4)) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f211,f14])).
% 0.20/0.43  fof(f211,plain,(
% 0.20/0.43    ( ! [X4] : (~m1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = k15_lattice3(sK0,X4) | ~r4_lattice3(sK0,sK1,X4) | ~r4_lattice3(sK0,sK3(sK0,X4,sK1),sK2)) )),
% 0.20/0.43    inference(resolution,[],[f157,f11])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    r2_hidden(sK1,sK2)),
% 0.20/0.43    inference(cnf_transformation,[],[f6])).
% 0.20/0.43  fof(f157,plain,(
% 0.20/0.43    ( ! [X4,X2,X3] : (~r2_hidden(X2,X4) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k15_lattice3(sK0,X3) = X2 | ~r4_lattice3(sK0,X2,X3) | ~r4_lattice3(sK0,sK3(sK0,X3,X2),X4)) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f156,f51])).
% 0.20/0.43  fof(f51,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r4_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,X1,X0),u1_struct_0(sK0)) | k15_lattice3(sK0,X1) = X0) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f50,f18])).
% 0.20/0.43  fof(f50,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~l3_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X0,X1) | m1_subset_1(sK3(sK0,X1,X0),u1_struct_0(sK0)) | k15_lattice3(sK0,X1) = X0) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f49,f16])).
% 0.20/0.43  fof(f49,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v10_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X0,X1) | m1_subset_1(sK3(sK0,X1,X0),u1_struct_0(sK0)) | k15_lattice3(sK0,X1) = X0) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f44,f15])).
% 0.20/0.43  fof(f44,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X0,X1) | m1_subset_1(sK3(sK0,X1,X0),u1_struct_0(sK0)) | k15_lattice3(sK0,X1) = X0) )),
% 0.20/0.43    inference(resolution,[],[f17,f19])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r4_lattice3(X0,X2,X1) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | k15_lattice3(X0,X1) = X2) )),
% 0.20/0.43    inference(cnf_transformation,[],[f8])).
% 0.20/0.43  fof(f156,plain,(
% 0.20/0.43    ( ! [X4,X2,X3] : (~r4_lattice3(sK0,X2,X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k15_lattice3(sK0,X3) = X2 | ~m1_subset_1(sK3(sK0,X3,X2),u1_struct_0(sK0)) | ~r2_hidden(X2,X4) | ~r4_lattice3(sK0,sK3(sK0,X3,X2),X4)) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f155,f18])).
% 0.20/0.43  fof(f155,plain,(
% 0.20/0.43    ( ! [X4,X2,X3] : (~r4_lattice3(sK0,X2,X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k15_lattice3(sK0,X3) = X2 | ~l3_lattices(sK0) | ~m1_subset_1(sK3(sK0,X3,X2),u1_struct_0(sK0)) | ~r2_hidden(X2,X4) | ~r4_lattice3(sK0,sK3(sK0,X3,X2),X4)) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f154,f15])).
% 0.20/0.43  fof(f154,plain,(
% 0.20/0.43    ( ! [X4,X2,X3] : (~r4_lattice3(sK0,X2,X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k15_lattice3(sK0,X3) = X2 | v2_struct_0(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK3(sK0,X3,X2),u1_struct_0(sK0)) | ~r2_hidden(X2,X4) | ~r4_lattice3(sK0,sK3(sK0,X3,X2),X4)) )),
% 0.20/0.43    inference(duplicate_literal_removal,[],[f153])).
% 0.20/0.43  fof(f153,plain,(
% 0.20/0.43    ( ! [X4,X2,X3] : (~r4_lattice3(sK0,X2,X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k15_lattice3(sK0,X3) = X2 | v2_struct_0(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK3(sK0,X3,X2),u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,X4) | ~r4_lattice3(sK0,sK3(sK0,X3,X2),X4)) )),
% 0.20/0.43    inference(resolution,[],[f57,f24])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X3,X2) | r1_lattices(X0,X3,X1) | ~r4_lattice3(X0,X1,X2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.43    inference(flattening,[],[f9])).
% 0.20/0.43  fof(f9,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).
% 0.20/0.43  fof(f57,plain,(
% 0.20/0.43    ( ! [X4,X5] : (~r1_lattices(sK0,X4,sK3(sK0,X5,X4)) | ~r4_lattice3(sK0,X4,X5) | ~m1_subset_1(X4,u1_struct_0(sK0)) | k15_lattice3(sK0,X5) = X4) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f56,f18])).
% 0.20/0.43  fof(f56,plain,(
% 0.20/0.43    ( ! [X4,X5] : (~l3_lattices(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X4,X5) | ~r1_lattices(sK0,X4,sK3(sK0,X5,X4)) | k15_lattice3(sK0,X5) = X4) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f55,f16])).
% 0.20/0.43  fof(f55,plain,(
% 0.20/0.43    ( ! [X4,X5] : (~v10_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X4,X5) | ~r1_lattices(sK0,X4,sK3(sK0,X5,X4)) | k15_lattice3(sK0,X5) = X4) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f46,f15])).
% 0.20/0.43  fof(f46,plain,(
% 0.20/0.43    ( ! [X4,X5] : (v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X4,X5) | ~r1_lattices(sK0,X4,sK3(sK0,X5,X4)) | k15_lattice3(sK0,X5) = X4) )),
% 0.20/0.43    inference(resolution,[],[f17,f21])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r4_lattice3(X0,X2,X1) | ~r1_lattices(X0,X2,sK3(X0,X1,X2)) | k15_lattice3(X0,X1) = X2) )),
% 0.20/0.43    inference(cnf_transformation,[],[f8])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (31127)------------------------------
% 0.20/0.43  % (31127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (31127)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (31127)Memory used [KB]: 1663
% 0.20/0.43  % (31127)Time elapsed: 0.042 s
% 0.20/0.43  % (31127)------------------------------
% 0.20/0.43  % (31127)------------------------------
% 0.20/0.43  % (31113)Success in time 0.066 s
%------------------------------------------------------------------------------
