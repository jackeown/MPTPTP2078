%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:22 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 341 expanded)
%              Number of leaves         :   30 ( 110 expanded)
%              Depth                    :   17
%              Number of atoms          :  478 (1512 expanded)
%              Number of equality atoms :   65 ( 242 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1629,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f406,f410,f1605,f1628])).

fof(f1628,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f1618])).

fof(f1618,plain,
    ( $false
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f63,f158])).

fof(f158,plain,
    ( ! [X2] : ~ v1_xboole_0(X2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl5_1
  <=> ! [X2] : ~ v1_xboole_0(X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f63,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f1605,plain,
    ( spl5_1
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f1604,f404,f157])).

fof(f404,plain,
    ( spl5_4
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f1604,plain,
    ( ! [X5] : ~ v1_xboole_0(X5)
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f1603,f1174])).

fof(f1174,plain,(
    ! [X0] :
      ( sK1 != k4_xboole_0(sK1,k1_tarski(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f1173,f140])).

fof(f140,plain,(
    ! [X1] :
      ( k1_xboole_0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f133,f117])).

fof(f117,plain,(
    ! [X2,X3] :
      ( r1_tarski(X2,X3)
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f86,f71])).

fof(f71,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f44,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f86,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f52,f53])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f133,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f84,f64])).

fof(f64,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1173,plain,(
    sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f1172,f55])).

fof(f55,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    & ~ v1_xboole_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f41,f40])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X1] :
        ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        & ~ v1_xboole_0(X1) )
   => ( sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
           => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).

fof(f1172,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1171,f56])).

fof(f56,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f1171,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1170,f57])).

fof(f57,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f1170,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1169,f94])).

fof(f94,plain,(
    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f59,f67])).

fof(f67,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).

fof(f59,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f1169,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1168,f93])).

fof(f93,plain,(
    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f60,f67])).

fof(f60,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f1168,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1164,f92])).

fof(f92,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(definition_unfolding,[],[f61,f67])).

fof(f61,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f42])).

fof(f1164,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f62,f420])).

fof(f420,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k4_xboole_0(X1,k1_tarski(k1_xboole_0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f419])).

fof(f419,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k4_xboole_0(X1,k1_tarski(k1_xboole_0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f90,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f70,f67,f67,f67,f67])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow19)).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f62,plain,(
    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f42])).

fof(f1603,plain,
    ( ! [X5] :
        ( ~ v1_xboole_0(X5)
        | sK1 = k4_xboole_0(sK1,k1_tarski(X5)) )
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f1589,f73])).

fof(f73,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f1589,plain,
    ( ! [X5] :
        ( ~ v1_xboole_0(X5)
        | sK1 = k4_xboole_0(sK1,k1_tarski(X5))
        | ~ r1_tarski(k4_xboole_0(sK1,k1_tarski(X5)),sK1) )
    | ~ spl5_4 ),
    inference(resolution,[],[f1523,f84])).

fof(f1523,plain,
    ( ! [X6] :
        ( r1_tarski(sK1,k4_xboole_0(sK1,k1_tarski(X6)))
        | ~ v1_xboole_0(X6) )
    | ~ spl5_4 ),
    inference(resolution,[],[f1517,f356])).

fof(f356,plain,(
    ! [X21,X20] :
      ( ~ v1_xboole_0(k4_xboole_0(X20,X21))
      | r1_tarski(X20,X21) ) ),
    inference(superposition,[],[f260,f294])).

fof(f294,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X1,X0) = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f292,f140])).

fof(f292,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f285,f104])).

fof(f104,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f96,f65])).

fof(f65,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f96,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f66,f75])).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f66,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f285,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f91,f249])).

fof(f249,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f99,f65])).

fof(f99,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f74,f76,f76])).

fof(f76,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f91,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f77,f76])).

fof(f77,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f260,plain,(
    ! [X4,X3] : r1_tarski(k4_xboole_0(X4,k4_xboole_0(X4,X3)),X3) ),
    inference(superposition,[],[f73,f99])).

fof(f1517,plain,
    ( ! [X0] :
        ( v1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tarski(X0))))
        | ~ v1_xboole_0(X0) )
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f1499,f99])).

fof(f1499,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | v1_xboole_0(k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),sK1))) )
    | ~ spl5_4 ),
    inference(resolution,[],[f1321,f260])).

fof(f1321,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(k4_xboole_0(k1_tarski(X2),X3),sK1)
        | ~ v1_xboole_0(X2)
        | v1_xboole_0(k4_xboole_0(k1_tarski(X2),X3)) )
    | ~ spl5_4 ),
    inference(resolution,[],[f1294,f73])).

fof(f1294,plain,
    ( ! [X2,X1] :
        ( ~ r1_tarski(X2,k1_tarski(X1))
        | ~ r1_tarski(X2,sK1)
        | ~ v1_xboole_0(X1)
        | v1_xboole_0(X2) )
    | ~ spl5_4 ),
    inference(resolution,[],[f1289,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_xboole_0(X0,X1)
          & r1_tarski(X2,X1)
          & r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).

fof(f1289,plain,
    ( ! [X6] :
        ( r1_xboole_0(k1_tarski(X6),sK1)
        | ~ v1_xboole_0(X6) )
    | ~ spl5_4 ),
    inference(duplicate_literal_removal,[],[f1288])).

fof(f1288,plain,
    ( ! [X6] :
        ( ~ v1_xboole_0(X6)
        | r1_xboole_0(k1_tarski(X6),sK1)
        | r1_xboole_0(k1_tarski(X6),sK1) )
    | ~ spl5_4 ),
    inference(superposition,[],[f414,f114])).

fof(f114,plain,(
    ! [X2,X1] :
      ( sK3(k1_tarski(X1),X2) = X1
      | r1_xboole_0(k1_tarski(X1),X2) ) ),
    inference(resolution,[],[f112,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_tarski(X1))
      | X0 = X1 ) ),
    inference(resolution,[],[f81,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f414,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(sK3(X2,sK1))
        | r1_xboole_0(X2,sK1) )
    | ~ spl5_4 ),
    inference(resolution,[],[f405,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f405,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ v1_xboole_0(X0) )
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f404])).

fof(f410,plain,(
    ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f409])).

fof(f409,plain,
    ( $false
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f408,f55])).

fof(f408,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f407,f56])).

fof(f407,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(resolution,[],[f402,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f402,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f400])).

fof(f400,plain,
    ( spl5_3
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f406,plain,
    ( spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f398,f404,f400])).

fof(f398,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(k2_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f397,f95])).

fof(f95,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    inference(definition_unfolding,[],[f58,f67])).

fof(f58,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f42])).

fof(f397,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ v1_xboole_0(X0)
      | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
      | v1_xboole_0(k2_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f396,f94])).

fof(f396,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ v1_xboole_0(X0)
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
      | v1_xboole_0(k2_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f395,f93])).

fof(f395,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ v1_xboole_0(X0)
      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
      | v1_xboole_0(k2_struct_0(sK0)) ) ),
    inference(resolution,[],[f342,f92])).

fof(f342,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
      | ~ r2_hidden(X2,X1)
      | ~ v1_xboole_0(X2)
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f97,f71])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f68,f67,f67,f67,f67])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ v1_xboole_0(X2)
              | ~ r2_hidden(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          | ~ v13_waybel_0(X1,k3_yellow_1(X0))
          | ~ v2_waybel_0(X1,k3_yellow_1(X0))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ v1_xboole_0(X2)
              | ~ r2_hidden(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          | ~ v13_waybel_0(X1,k3_yellow_1(X0))
          | ~ v2_waybel_0(X1,k3_yellow_1(X0))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
            & v13_waybel_0(X1,k3_yellow_1(X0))
            & v2_waybel_0(X1,k3_yellow_1(X0))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ~ ( v1_xboole_0(X2)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:58:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (4031)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (4039)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (4049)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (4054)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.50  % (4042)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.50  % (4049)Refutation not found, incomplete strategy% (4049)------------------------------
% 0.21/0.50  % (4049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (4034)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (4049)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (4049)Memory used [KB]: 10746
% 0.21/0.51  % (4049)Time elapsed: 0.059 s
% 0.21/0.51  % (4049)------------------------------
% 0.21/0.51  % (4049)------------------------------
% 0.21/0.51  % (4028)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (4030)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (4033)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (4027)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (4029)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (4029)Refutation not found, incomplete strategy% (4029)------------------------------
% 0.21/0.52  % (4029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (4029)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (4029)Memory used [KB]: 10746
% 0.21/0.52  % (4029)Time elapsed: 0.114 s
% 0.21/0.52  % (4029)------------------------------
% 0.21/0.52  % (4029)------------------------------
% 0.21/0.52  % (4055)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (4032)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (4041)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (4047)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (4048)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (4043)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (4052)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (4035)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.33/0.54  % (4040)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.33/0.54  % (4046)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.33/0.54  % (4037)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.33/0.54  % (4056)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.33/0.54  % (4045)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.33/0.54  % (4050)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.33/0.54  % (4053)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.33/0.55  % (4037)Refutation not found, incomplete strategy% (4037)------------------------------
% 1.33/0.55  % (4037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  % (4044)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.33/0.55  % (4038)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.33/0.55  % (4037)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.55  
% 1.33/0.55  % (4037)Memory used [KB]: 10746
% 1.33/0.55  % (4037)Time elapsed: 0.145 s
% 1.33/0.55  % (4037)------------------------------
% 1.33/0.55  % (4037)------------------------------
% 1.51/0.55  % (4036)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.51/0.56  % (4051)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.51/0.57  % (4054)Refutation found. Thanks to Tanya!
% 1.51/0.57  % SZS status Theorem for theBenchmark
% 1.51/0.57  % SZS output start Proof for theBenchmark
% 1.51/0.57  fof(f1629,plain,(
% 1.51/0.57    $false),
% 1.51/0.57    inference(avatar_sat_refutation,[],[f406,f410,f1605,f1628])).
% 1.51/0.57  fof(f1628,plain,(
% 1.51/0.57    ~spl5_1),
% 1.51/0.57    inference(avatar_contradiction_clause,[],[f1618])).
% 1.51/0.57  fof(f1618,plain,(
% 1.51/0.57    $false | ~spl5_1),
% 1.51/0.57    inference(subsumption_resolution,[],[f63,f158])).
% 1.51/0.57  fof(f158,plain,(
% 1.51/0.57    ( ! [X2] : (~v1_xboole_0(X2)) ) | ~spl5_1),
% 1.51/0.57    inference(avatar_component_clause,[],[f157])).
% 1.51/0.57  fof(f157,plain,(
% 1.51/0.57    spl5_1 <=> ! [X2] : ~v1_xboole_0(X2)),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.51/0.57  fof(f63,plain,(
% 1.51/0.57    v1_xboole_0(k1_xboole_0)),
% 1.51/0.57    inference(cnf_transformation,[],[f4])).
% 1.51/0.57  fof(f4,axiom,(
% 1.51/0.57    v1_xboole_0(k1_xboole_0)),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.51/0.57  fof(f1605,plain,(
% 1.51/0.57    spl5_1 | ~spl5_4),
% 1.51/0.57    inference(avatar_split_clause,[],[f1604,f404,f157])).
% 1.51/0.57  fof(f404,plain,(
% 1.51/0.57    spl5_4 <=> ! [X0] : (~r2_hidden(X0,sK1) | ~v1_xboole_0(X0))),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.51/0.57  fof(f1604,plain,(
% 1.51/0.57    ( ! [X5] : (~v1_xboole_0(X5)) ) | ~spl5_4),
% 1.51/0.57    inference(subsumption_resolution,[],[f1603,f1174])).
% 1.51/0.57  fof(f1174,plain,(
% 1.51/0.57    ( ! [X0] : (sK1 != k4_xboole_0(sK1,k1_tarski(X0)) | ~v1_xboole_0(X0)) )),
% 1.51/0.57    inference(superposition,[],[f1173,f140])).
% 1.51/0.57  fof(f140,plain,(
% 1.51/0.57    ( ! [X1] : (k1_xboole_0 = X1 | ~v1_xboole_0(X1)) )),
% 1.51/0.57    inference(resolution,[],[f133,f117])).
% 1.51/0.57  fof(f117,plain,(
% 1.51/0.57    ( ! [X2,X3] : (r1_tarski(X2,X3) | ~v1_xboole_0(X2)) )),
% 1.51/0.57    inference(resolution,[],[f86,f71])).
% 1.51/0.57  fof(f71,plain,(
% 1.51/0.57    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f46])).
% 1.51/0.57  fof(f46,plain,(
% 1.51/0.57    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.51/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f44,f45])).
% 1.51/0.57  fof(f45,plain,(
% 1.51/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 1.51/0.57    introduced(choice_axiom,[])).
% 1.51/0.57  fof(f44,plain,(
% 1.51/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.51/0.57    inference(rectify,[],[f43])).
% 1.51/0.57  fof(f43,plain,(
% 1.51/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.51/0.57    inference(nnf_transformation,[],[f2])).
% 1.51/0.57  fof(f2,axiom,(
% 1.51/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.51/0.57  fof(f86,plain,(
% 1.51/0.57    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f54])).
% 1.51/0.57  fof(f54,plain,(
% 1.51/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.51/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f52,f53])).
% 1.51/0.57  fof(f53,plain,(
% 1.51/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.51/0.57    introduced(choice_axiom,[])).
% 1.51/0.57  fof(f52,plain,(
% 1.51/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.51/0.57    inference(rectify,[],[f51])).
% 1.51/0.57  fof(f51,plain,(
% 1.51/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.51/0.57    inference(nnf_transformation,[],[f35])).
% 1.51/0.57  fof(f35,plain,(
% 1.51/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.51/0.57    inference(ennf_transformation,[],[f3])).
% 1.51/0.57  fof(f3,axiom,(
% 1.51/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.51/0.57  fof(f133,plain,(
% 1.51/0.57    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.51/0.57    inference(resolution,[],[f84,f64])).
% 1.51/0.57  fof(f64,plain,(
% 1.51/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f9])).
% 1.51/0.57  fof(f9,axiom,(
% 1.51/0.57    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.51/0.57  fof(f84,plain,(
% 1.51/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f50])).
% 1.51/0.57  fof(f50,plain,(
% 1.51/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.51/0.57    inference(flattening,[],[f49])).
% 1.51/0.57  fof(f49,plain,(
% 1.51/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.51/0.57    inference(nnf_transformation,[],[f6])).
% 1.51/0.57  fof(f6,axiom,(
% 1.51/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.51/0.57  fof(f1173,plain,(
% 1.51/0.57    sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0))),
% 1.51/0.57    inference(subsumption_resolution,[],[f1172,f55])).
% 1.51/0.57  fof(f55,plain,(
% 1.51/0.57    ~v2_struct_0(sK0)),
% 1.51/0.57    inference(cnf_transformation,[],[f42])).
% 1.51/0.57  fof(f42,plain,(
% 1.51/0.57    (sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 1.51/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f41,f40])).
% 1.51/0.57  fof(f40,plain,(
% 1.51/0.57    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 1.51/0.57    introduced(choice_axiom,[])).
% 1.51/0.57  fof(f41,plain,(
% 1.51/0.57    ? [X1] : (k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) => (sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1))),
% 1.51/0.57    introduced(choice_axiom,[])).
% 1.51/0.57  fof(f26,plain,(
% 1.51/0.57    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 1.51/0.57    inference(flattening,[],[f25])).
% 1.51/0.57  fof(f25,plain,(
% 1.51/0.57    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 1.51/0.57    inference(ennf_transformation,[],[f23])).
% 1.51/0.57  fof(f23,negated_conjecture,(
% 1.51/0.57    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 1.51/0.57    inference(negated_conjecture,[],[f22])).
% 1.51/0.57  fof(f22,conjecture,(
% 1.51/0.57    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).
% 1.51/0.57  fof(f1172,plain,(
% 1.51/0.57    sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | v2_struct_0(sK0)),
% 1.51/0.57    inference(subsumption_resolution,[],[f1171,f56])).
% 1.51/0.57  fof(f56,plain,(
% 1.51/0.57    l1_struct_0(sK0)),
% 1.51/0.57    inference(cnf_transformation,[],[f42])).
% 1.51/0.57  fof(f1171,plain,(
% 1.51/0.57    sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 1.51/0.57    inference(subsumption_resolution,[],[f1170,f57])).
% 1.51/0.57  fof(f57,plain,(
% 1.51/0.57    ~v1_xboole_0(sK1)),
% 1.51/0.57    inference(cnf_transformation,[],[f42])).
% 1.51/0.57  fof(f1170,plain,(
% 1.51/0.57    sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 1.51/0.57    inference(subsumption_resolution,[],[f1169,f94])).
% 1.51/0.57  fof(f94,plain,(
% 1.51/0.57    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 1.51/0.57    inference(definition_unfolding,[],[f59,f67])).
% 1.51/0.57  fof(f67,plain,(
% 1.51/0.57    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 1.51/0.57    inference(cnf_transformation,[],[f19])).
% 1.51/0.57  fof(f19,axiom,(
% 1.51/0.57    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).
% 1.51/0.57  fof(f59,plain,(
% 1.51/0.57    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 1.51/0.57    inference(cnf_transformation,[],[f42])).
% 1.51/0.57  fof(f1169,plain,(
% 1.51/0.57    sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 1.51/0.57    inference(subsumption_resolution,[],[f1168,f93])).
% 1.51/0.57  fof(f93,plain,(
% 1.51/0.57    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 1.51/0.57    inference(definition_unfolding,[],[f60,f67])).
% 1.51/0.57  fof(f60,plain,(
% 1.51/0.57    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 1.51/0.57    inference(cnf_transformation,[],[f42])).
% 1.51/0.57  fof(f1168,plain,(
% 1.51/0.57    sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 1.51/0.57    inference(subsumption_resolution,[],[f1164,f92])).
% 1.51/0.57  fof(f92,plain,(
% 1.51/0.57    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 1.51/0.57    inference(definition_unfolding,[],[f61,f67])).
% 1.51/0.57  fof(f61,plain,(
% 1.51/0.57    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 1.51/0.57    inference(cnf_transformation,[],[f42])).
% 1.51/0.57  fof(f1164,plain,(
% 1.51/0.57    sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 1.51/0.57    inference(superposition,[],[f62,f420])).
% 1.51/0.57  fof(f420,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k4_xboole_0(X1,k1_tarski(k1_xboole_0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.51/0.57    inference(duplicate_literal_removal,[],[f419])).
% 1.51/0.57  fof(f419,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k4_xboole_0(X1,k1_tarski(k1_xboole_0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.51/0.57    inference(superposition,[],[f90,f98])).
% 1.51/0.57  fof(f98,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.51/0.57    inference(definition_unfolding,[],[f70,f67,f67,f67,f67])).
% 1.51/0.57  fof(f70,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f32])).
% 1.51/0.57  fof(f32,plain,(
% 1.51/0.57    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.51/0.57    inference(flattening,[],[f31])).
% 1.51/0.57  fof(f31,plain,(
% 1.51/0.57    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.51/0.57    inference(ennf_transformation,[],[f20])).
% 1.51/0.57  fof(f20,axiom,(
% 1.51/0.57    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X1)) => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow19)).
% 1.51/0.57  fof(f90,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.51/0.57    inference(cnf_transformation,[],[f39])).
% 1.51/0.57  fof(f39,plain,(
% 1.51/0.57    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.51/0.57    inference(ennf_transformation,[],[f17])).
% 1.51/0.57  fof(f17,axiom,(
% 1.51/0.57    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.51/0.57  fof(f62,plain,(
% 1.51/0.57    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 1.51/0.57    inference(cnf_transformation,[],[f42])).
% 1.51/0.57  fof(f1603,plain,(
% 1.51/0.57    ( ! [X5] : (~v1_xboole_0(X5) | sK1 = k4_xboole_0(sK1,k1_tarski(X5))) ) | ~spl5_4),
% 1.51/0.57    inference(subsumption_resolution,[],[f1589,f73])).
% 1.51/0.57  fof(f73,plain,(
% 1.51/0.57    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f10])).
% 1.51/0.57  fof(f10,axiom,(
% 1.51/0.57    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.51/0.57  fof(f1589,plain,(
% 1.51/0.57    ( ! [X5] : (~v1_xboole_0(X5) | sK1 = k4_xboole_0(sK1,k1_tarski(X5)) | ~r1_tarski(k4_xboole_0(sK1,k1_tarski(X5)),sK1)) ) | ~spl5_4),
% 1.51/0.57    inference(resolution,[],[f1523,f84])).
% 1.51/0.57  fof(f1523,plain,(
% 1.51/0.57    ( ! [X6] : (r1_tarski(sK1,k4_xboole_0(sK1,k1_tarski(X6))) | ~v1_xboole_0(X6)) ) | ~spl5_4),
% 1.51/0.57    inference(resolution,[],[f1517,f356])).
% 1.51/0.57  fof(f356,plain,(
% 1.51/0.57    ( ! [X21,X20] : (~v1_xboole_0(k4_xboole_0(X20,X21)) | r1_tarski(X20,X21)) )),
% 1.51/0.57    inference(superposition,[],[f260,f294])).
% 1.51/0.57  fof(f294,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k4_xboole_0(X1,X0) = X1 | ~v1_xboole_0(X0)) )),
% 1.51/0.57    inference(superposition,[],[f292,f140])).
% 1.51/0.57  fof(f292,plain,(
% 1.51/0.57    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = X2) )),
% 1.51/0.57    inference(forward_demodulation,[],[f285,f104])).
% 1.51/0.57  fof(f104,plain,(
% 1.51/0.57    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.51/0.57    inference(forward_demodulation,[],[f96,f65])).
% 1.51/0.57  fof(f65,plain,(
% 1.51/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f12])).
% 1.51/0.57  fof(f12,axiom,(
% 1.51/0.57    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 1.51/0.57  fof(f96,plain,(
% 1.51/0.57    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 1.51/0.57    inference(definition_unfolding,[],[f66,f75])).
% 1.51/0.57  fof(f75,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.51/0.57    inference(cnf_transformation,[],[f14])).
% 1.51/0.57  fof(f14,axiom,(
% 1.51/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.51/0.57  fof(f66,plain,(
% 1.51/0.57    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.51/0.57    inference(cnf_transformation,[],[f8])).
% 1.51/0.57  fof(f8,axiom,(
% 1.51/0.57    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.51/0.57  fof(f285,plain,(
% 1.51/0.57    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k1_xboole_0)) )),
% 1.51/0.57    inference(superposition,[],[f91,f249])).
% 1.51/0.57  fof(f249,plain,(
% 1.51/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.51/0.57    inference(superposition,[],[f99,f65])).
% 1.51/0.57  fof(f99,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.51/0.57    inference(definition_unfolding,[],[f74,f76,f76])).
% 1.51/0.57  fof(f76,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.51/0.57    inference(cnf_transformation,[],[f11])).
% 1.51/0.57  fof(f11,axiom,(
% 1.51/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.51/0.57  fof(f74,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f1])).
% 1.51/0.57  fof(f1,axiom,(
% 1.51/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.51/0.57  fof(f91,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.51/0.57    inference(definition_unfolding,[],[f77,f76])).
% 1.51/0.57  fof(f77,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.51/0.57    inference(cnf_transformation,[],[f7])).
% 1.51/0.57  fof(f7,axiom,(
% 1.51/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.51/0.57  fof(f260,plain,(
% 1.51/0.57    ( ! [X4,X3] : (r1_tarski(k4_xboole_0(X4,k4_xboole_0(X4,X3)),X3)) )),
% 1.51/0.57    inference(superposition,[],[f73,f99])).
% 1.51/0.57  fof(f1517,plain,(
% 1.51/0.57    ( ! [X0] : (v1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tarski(X0)))) | ~v1_xboole_0(X0)) ) | ~spl5_4),
% 1.51/0.57    inference(forward_demodulation,[],[f1499,f99])).
% 1.51/0.57  fof(f1499,plain,(
% 1.51/0.57    ( ! [X0] : (~v1_xboole_0(X0) | v1_xboole_0(k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),sK1)))) ) | ~spl5_4),
% 1.51/0.57    inference(resolution,[],[f1321,f260])).
% 1.51/0.57  fof(f1321,plain,(
% 1.51/0.57    ( ! [X2,X3] : (~r1_tarski(k4_xboole_0(k1_tarski(X2),X3),sK1) | ~v1_xboole_0(X2) | v1_xboole_0(k4_xboole_0(k1_tarski(X2),X3))) ) | ~spl5_4),
% 1.51/0.57    inference(resolution,[],[f1294,f73])).
% 1.51/0.57  fof(f1294,plain,(
% 1.51/0.57    ( ! [X2,X1] : (~r1_tarski(X2,k1_tarski(X1)) | ~r1_tarski(X2,sK1) | ~v1_xboole_0(X1) | v1_xboole_0(X2)) ) | ~spl5_4),
% 1.51/0.57    inference(resolution,[],[f1289,f89])).
% 1.51/0.57  fof(f89,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0) | v1_xboole_0(X2)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f38])).
% 1.51/0.57  fof(f38,plain,(
% 1.51/0.57    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0) | v1_xboole_0(X2))),
% 1.51/0.57    inference(flattening,[],[f37])).
% 1.51/0.57  fof(f37,plain,(
% 1.51/0.57    ! [X0,X1,X2] : ((~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0)) | v1_xboole_0(X2))),
% 1.51/0.57    inference(ennf_transformation,[],[f13])).
% 1.51/0.57  fof(f13,axiom,(
% 1.51/0.57    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ~(r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).
% 1.51/0.57  fof(f1289,plain,(
% 1.51/0.57    ( ! [X6] : (r1_xboole_0(k1_tarski(X6),sK1) | ~v1_xboole_0(X6)) ) | ~spl5_4),
% 1.51/0.57    inference(duplicate_literal_removal,[],[f1288])).
% 1.51/0.57  fof(f1288,plain,(
% 1.51/0.57    ( ! [X6] : (~v1_xboole_0(X6) | r1_xboole_0(k1_tarski(X6),sK1) | r1_xboole_0(k1_tarski(X6),sK1)) ) | ~spl5_4),
% 1.51/0.57    inference(superposition,[],[f414,f114])).
% 1.51/0.57  fof(f114,plain,(
% 1.51/0.57    ( ! [X2,X1] : (sK3(k1_tarski(X1),X2) = X1 | r1_xboole_0(k1_tarski(X1),X2)) )),
% 1.51/0.57    inference(resolution,[],[f112,f78])).
% 1.51/0.57  fof(f78,plain,(
% 1.51/0.57    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f48])).
% 1.51/0.57  fof(f48,plain,(
% 1.51/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.51/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f47])).
% 1.51/0.57  fof(f47,plain,(
% 1.51/0.57    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.51/0.57    introduced(choice_axiom,[])).
% 1.51/0.57  fof(f33,plain,(
% 1.51/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.51/0.57    inference(ennf_transformation,[],[f24])).
% 1.51/0.57  fof(f24,plain,(
% 1.51/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.51/0.57    inference(rectify,[],[f5])).
% 1.51/0.57  fof(f5,axiom,(
% 1.51/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.51/0.57  fof(f112,plain,(
% 1.51/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k1_tarski(X1)) | X0 = X1) )),
% 1.51/0.57    inference(resolution,[],[f81,f88])).
% 1.51/0.57  fof(f88,plain,(
% 1.51/0.57    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f36])).
% 1.51/0.57  fof(f36,plain,(
% 1.51/0.57    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 1.51/0.57    inference(ennf_transformation,[],[f15])).
% 1.51/0.57  fof(f15,axiom,(
% 1.51/0.57    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 1.51/0.57  fof(f81,plain,(
% 1.51/0.57    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 1.51/0.57    inference(cnf_transformation,[],[f34])).
% 1.51/0.57  fof(f34,plain,(
% 1.51/0.57    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 1.51/0.57    inference(ennf_transformation,[],[f16])).
% 1.51/0.57  fof(f16,axiom,(
% 1.51/0.57    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 1.51/0.57  fof(f414,plain,(
% 1.51/0.57    ( ! [X2] : (~v1_xboole_0(sK3(X2,sK1)) | r1_xboole_0(X2,sK1)) ) | ~spl5_4),
% 1.51/0.57    inference(resolution,[],[f405,f79])).
% 1.51/0.57  fof(f79,plain,(
% 1.51/0.57    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f48])).
% 1.51/0.57  fof(f405,plain,(
% 1.51/0.57    ( ! [X0] : (~r2_hidden(X0,sK1) | ~v1_xboole_0(X0)) ) | ~spl5_4),
% 1.51/0.57    inference(avatar_component_clause,[],[f404])).
% 1.51/0.57  fof(f410,plain,(
% 1.51/0.57    ~spl5_3),
% 1.51/0.57    inference(avatar_contradiction_clause,[],[f409])).
% 1.51/0.57  fof(f409,plain,(
% 1.51/0.57    $false | ~spl5_3),
% 1.51/0.57    inference(subsumption_resolution,[],[f408,f55])).
% 1.51/0.57  fof(f408,plain,(
% 1.51/0.57    v2_struct_0(sK0) | ~spl5_3),
% 1.51/0.57    inference(subsumption_resolution,[],[f407,f56])).
% 1.51/0.57  fof(f407,plain,(
% 1.51/0.57    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl5_3),
% 1.51/0.57    inference(resolution,[],[f402,f69])).
% 1.51/0.57  fof(f69,plain,(
% 1.51/0.57    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f30])).
% 1.51/0.57  fof(f30,plain,(
% 1.51/0.57    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.51/0.57    inference(flattening,[],[f29])).
% 1.51/0.57  fof(f29,plain,(
% 1.51/0.57    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.51/0.57    inference(ennf_transformation,[],[f18])).
% 1.51/0.57  fof(f18,axiom,(
% 1.51/0.57    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).
% 1.51/0.57  fof(f402,plain,(
% 1.51/0.57    v1_xboole_0(k2_struct_0(sK0)) | ~spl5_3),
% 1.51/0.57    inference(avatar_component_clause,[],[f400])).
% 1.51/0.57  fof(f400,plain,(
% 1.51/0.57    spl5_3 <=> v1_xboole_0(k2_struct_0(sK0))),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.51/0.57  fof(f406,plain,(
% 1.51/0.57    spl5_3 | spl5_4),
% 1.51/0.57    inference(avatar_split_clause,[],[f398,f404,f400])).
% 1.51/0.57  fof(f398,plain,(
% 1.51/0.57    ( ! [X0] : (~r2_hidden(X0,sK1) | ~v1_xboole_0(X0) | v1_xboole_0(k2_struct_0(sK0))) )),
% 1.51/0.57    inference(subsumption_resolution,[],[f397,f95])).
% 1.51/0.57  fof(f95,plain,(
% 1.51/0.57    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))),
% 1.51/0.57    inference(definition_unfolding,[],[f58,f67])).
% 1.51/0.57  fof(f58,plain,(
% 1.51/0.57    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 1.51/0.57    inference(cnf_transformation,[],[f42])).
% 1.51/0.57  fof(f397,plain,(
% 1.51/0.57    ( ! [X0] : (~r2_hidden(X0,sK1) | ~v1_xboole_0(X0) | ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | v1_xboole_0(k2_struct_0(sK0))) )),
% 1.51/0.57    inference(subsumption_resolution,[],[f396,f94])).
% 1.51/0.57  fof(f396,plain,(
% 1.51/0.57    ( ! [X0] : (~r2_hidden(X0,sK1) | ~v1_xboole_0(X0) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | v1_xboole_0(k2_struct_0(sK0))) )),
% 1.51/0.57    inference(subsumption_resolution,[],[f395,f93])).
% 1.51/0.57  fof(f395,plain,(
% 1.51/0.57    ( ! [X0] : (~r2_hidden(X0,sK1) | ~v1_xboole_0(X0) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | v1_xboole_0(k2_struct_0(sK0))) )),
% 1.51/0.57    inference(resolution,[],[f342,f92])).
% 1.51/0.57  fof(f342,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | ~r2_hidden(X2,X1) | ~v1_xboole_0(X2) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | v1_xboole_0(X0)) )),
% 1.51/0.57    inference(subsumption_resolution,[],[f97,f71])).
% 1.51/0.57  fof(f97,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.51/0.57    inference(definition_unfolding,[],[f68,f67,f67,f67,f67])).
% 1.51/0.57  fof(f68,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f28])).
% 1.51/0.57  fof(f28,plain,(
% 1.51/0.57    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.51/0.57    inference(flattening,[],[f27])).
% 1.51/0.57  fof(f27,plain,(
% 1.51/0.57    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.51/0.57    inference(ennf_transformation,[],[f21])).
% 1.51/0.57  fof(f21,axiom,(
% 1.51/0.57    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).
% 1.51/0.57  % SZS output end Proof for theBenchmark
% 1.51/0.57  % (4054)------------------------------
% 1.51/0.57  % (4054)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.57  % (4054)Termination reason: Refutation
% 1.51/0.57  
% 1.51/0.57  % (4054)Memory used [KB]: 6780
% 1.51/0.57  % (4054)Time elapsed: 0.175 s
% 1.51/0.57  % (4054)------------------------------
% 1.51/0.57  % (4054)------------------------------
% 1.51/0.57  % (4023)Success in time 0.213 s
%------------------------------------------------------------------------------
