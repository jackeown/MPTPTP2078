%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  248 (6462 expanded)
%              Number of leaves         :   24 (2264 expanded)
%              Depth                    :   66
%              Number of atoms          : 1271 (42086 expanded)
%              Number of equality atoms :  203 (2231 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f651,plain,(
    $false ),
    inference(subsumption_resolution,[],[f650,f71])).

fof(f71,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK2)
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f48,f47,f46])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
                & m1_subset_1(X2,u1_struct_0(X1)) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tmap_1(X1,k8_tmap_1(sK0,X1),k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X1),X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tmap_1(X1,k8_tmap_1(sK0,X1),k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X1),X2)
            & m1_subset_1(X2,u1_struct_0(X1)) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),X2)
          & m1_subset_1(X2,u1_struct_0(sK1)) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X2] :
        ( ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),X2)
        & m1_subset_1(X2,u1_struct_0(sK1)) )
   => ( ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK2)
      & m1_subset_1(sK2,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_tmap_1)).

fof(f650,plain,(
    ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(resolution,[],[f635,f72])).

fof(f72,plain,(
    ~ r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f635,plain,(
    ! [X0] :
      ( r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(superposition,[],[f292,f632])).

fof(f632,plain,(
    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f631,f71])).

fof(f631,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(resolution,[],[f591,f72])).

fof(f591,plain,(
    ! [X1] :
      ( r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f590,f69])).

fof(f69,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f590,plain,(
    ! [X1] :
      ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),X1) ) ),
    inference(subsumption_resolution,[],[f589,f70])).

fof(f70,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f589,plain,(
    ! [X1] :
      ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK1)
      | r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),X1) ) ),
    inference(subsumption_resolution,[],[f588,f117])).

fof(f117,plain,(
    l1_pre_topc(sK1) ),
    inference(resolution,[],[f116,f70])).

fof(f116,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f76,f68])).

fof(f68,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f588,plain,(
    ! [X1] :
      ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
      | ~ l1_pre_topc(sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK1)
      | r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),X1) ) ),
    inference(resolution,[],[f586,f277])).

fof(f277,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(sK1,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X1),X0) ) ),
    inference(subsumption_resolution,[],[f276,f66])).

fof(f66,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f276,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r1_tsep_1(sK1,X1)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X1),X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f275,f67])).

fof(f67,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f275,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r1_tsep_1(sK1,X1)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X1),X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f274,f68])).

fof(f274,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r1_tsep_1(sK1,X1)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X1),X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f273,f69])).

fof(f273,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r1_tsep_1(sK1,X1)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X1),X0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f89,f70])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | ~ r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | ~ r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X2))
                   => r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_tmap_1)).

fof(f586,plain,(
    ! [X0] :
      ( r1_tsep_1(X0,sK1)
      | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f585,f75])).

fof(f75,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f585,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
      | r1_tsep_1(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f584,f117])).

fof(f584,plain,(
    ! [X0] :
      ( r1_tsep_1(X0,sK1)
      | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
      | ~ l1_struct_0(X0)
      | ~ l1_pre_topc(sK1) ) ),
    inference(resolution,[],[f575,f75])).

fof(f575,plain,(
    ! [X2] :
      ( ~ l1_struct_0(sK1)
      | r1_tsep_1(X2,sK1)
      | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
      | ~ l1_struct_0(X2) ) ),
    inference(resolution,[],[f570,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f570,plain,(
    ! [X1] :
      ( r1_xboole_0(X1,u1_struct_0(sK1))
      | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f567,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f63])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
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

fof(f567,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,u1_struct_0(sK1))
      | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f564,f90])).

fof(f90,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK5(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f60,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
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

fof(f564,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(duplicate_literal_removal,[],[f559])).

fof(f559,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(resolution,[],[f555,f338])).

fof(f338,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(duplicate_literal_removal,[],[f337])).

fof(f337,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(superposition,[],[f331,f314])).

fof(f314,plain,
    ( u1_struct_0(sK1) = sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f313,f68])).

fof(f313,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | u1_struct_0(sK1) = sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f312,f70])).

fof(f312,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | u1_struct_0(sK1) = sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f311,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f311,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | u1_struct_0(sK1) = sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f310,f70])).

fof(f310,plain,
    ( u1_struct_0(sK1) = sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f309,f66])).

fof(f309,plain,
    ( u1_struct_0(sK1) = sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f308,f67])).

fof(f308,plain,
    ( u1_struct_0(sK1) = sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f307,f68])).

fof(f307,plain,
    ( u1_struct_0(sK1) = sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f306,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f101,f77])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_funct_1(k7_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(f306,plain,
    ( ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | u1_struct_0(sK1) = sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f304,f156])).

fof(f156,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f155,f66])).

fof(f155,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f154,f67])).

fof(f154,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f153,f68])).

fof(f153,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f103,f127])).

fof(f127,plain,(
    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f126,f66])).

fof(f126,plain,
    ( v2_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f125,f67])).

fof(f125,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f124,f68])).

fof(f124,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(resolution,[],[f123,f70])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))) ) ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f86,f77])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f103,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f304,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | u1_struct_0(sK1) = sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f303,f151])).

fof(f151,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f150,f66])).

fof(f150,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f149,f67])).

fof(f149,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f148,f68])).

fof(f148,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f102,f127])).

fof(f102,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f303,plain,(
    ! [X0] :
      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | u1_struct_0(sK1) = sK4(sK0,sK1,X0)
      | ~ v1_funct_1(X0)
      | k9_tmap_1(sK0,sK1) = X0 ) ),
    inference(forward_demodulation,[],[f302,f170])).

fof(f170,plain,(
    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) ),
    inference(superposition,[],[f127,f169])).

fof(f169,plain,(
    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f168,f68])).

fof(f168,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f167,f67])).

fof(f167,plain,
    ( ~ v2_pre_topc(sK0)
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f166,f66])).

fof(f166,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f165,f70])).

fof(f165,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f164,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).

fof(f164,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f163,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f163,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | v2_struct_0(X0)
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f114,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | v2_struct_0(X0)
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(global_subsumption,[],[f77,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( k6_tmap_1(X0,u1_struct_0(X1)) = X2
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( k6_tmap_1(X0,X4) = X2
      | u1_struct_0(X1) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ( k6_tmap_1(X0,sK3(X0,X1,X2)) != X2
                    & u1_struct_0(X1) = sK3(X0,X1,X2)
                    & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f52,f53])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK3(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK3(X0,X1,X2)
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( k6_tmap_1(X0,X3) = X2
                      | u1_struct_0(X1) != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & v1_pre_topc(X2) )
             => ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => k6_tmap_1(X0,X3) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_tmap_1)).

fof(f302,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | u1_struct_0(sK1) = sK4(sK0,sK1,X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
      | ~ v1_funct_1(X0)
      | k9_tmap_1(sK0,sK1) = X0 ) ),
    inference(forward_demodulation,[],[f301,f170])).

fof(f301,plain,(
    ! [X0] :
      ( u1_struct_0(sK1) = sK4(sK0,sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
      | ~ v1_funct_1(X0)
      | k9_tmap_1(sK0,sK1) = X0 ) ),
    inference(subsumption_resolution,[],[f300,f66])).

fof(f300,plain,(
    ! [X0] :
      ( u1_struct_0(sK1) = sK4(sK0,sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
      | ~ v1_funct_1(X0)
      | k9_tmap_1(sK0,sK1) = X0
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f299,f67])).

fof(f299,plain,(
    ! [X0] :
      ( u1_struct_0(sK1) = sK4(sK0,sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
      | ~ v1_funct_1(X0)
      | k9_tmap_1(sK0,sK1) = X0
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f298,f68])).

fof(f298,plain,(
    ! [X0] :
      ( u1_struct_0(sK1) = sK4(sK0,sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
      | ~ v1_funct_1(X0)
      | k9_tmap_1(sK0,sK1) = X0
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f84,f70])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | u1_struct_0(X1) = sK4(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k9_tmap_1(X0,X1) = X2
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK4(X0,X1,X2))),X2,k7_tmap_1(X0,sK4(X0,X1,X2)))
                    & u1_struct_0(X1) = sK4(X0,X1,X2)
                    & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4))
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f56,f57])).

fof(f57,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK4(X0,X1,X2))),X2,k7_tmap_1(X0,sK4(X0,X1,X2)))
        & u1_struct_0(X1) = sK4(X0,X1,X2)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4))
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      | u1_struct_0(X1) != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

% (24151)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
                & v1_funct_1(X2) )
             => ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_tmap_1)).

fof(f331,plain,
    ( m1_subset_1(sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f330,f68])).

fof(f330,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | m1_subset_1(sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f329,f70])).

fof(f329,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | m1_subset_1(sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f328,f77])).

fof(f328,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | m1_subset_1(sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f327,f70])).

fof(f327,plain,
    ( m1_subset_1(sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f326,f66])).

fof(f326,plain,
    ( m1_subset_1(sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f325,f67])).

fof(f325,plain,
    ( m1_subset_1(sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f324,f68])).

fof(f324,plain,
    ( m1_subset_1(sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f323,f121])).

fof(f323,plain,
    ( ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | m1_subset_1(sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f321,f156])).

fof(f321,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | m1_subset_1(sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f320,f151])).

fof(f320,plain,(
    ! [X0] :
      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_funct_1(X0)
      | k9_tmap_1(sK0,sK1) = X0 ) ),
    inference(forward_demodulation,[],[f319,f170])).

fof(f319,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      | m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
      | ~ v1_funct_1(X0)
      | k9_tmap_1(sK0,sK1) = X0 ) ),
    inference(forward_demodulation,[],[f318,f170])).

fof(f318,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
      | ~ v1_funct_1(X0)
      | k9_tmap_1(sK0,sK1) = X0 ) ),
    inference(subsumption_resolution,[],[f317,f66])).

fof(f317,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
      | ~ v1_funct_1(X0)
      | k9_tmap_1(sK0,sK1) = X0
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f316,f67])).

fof(f316,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
      | ~ v1_funct_1(X0)
      | k9_tmap_1(sK0,sK1) = X0
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f315,f68])).

fof(f315,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
      | ~ v1_funct_1(X0)
      | k9_tmap_1(sK0,sK1) = X0
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f83,f70])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k9_tmap_1(X0,X1) = X2
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f555,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f533,f91])).

fof(f91,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f533,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f532,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f532,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f531,f66])).

fof(f531,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f530,f67])).

fof(f530,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f529,f68])).

fof(f529,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f528,f70])).

fof(f528,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f527,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

% (24161)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_tmap_1)).

fof(f527,plain,
    ( ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f526,f381])).

fof(f381,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(duplicate_literal_removal,[],[f380])).

fof(f380,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(superposition,[],[f377,f314])).

fof(f377,plain,
    ( v1_funct_2(k7_tmap_1(sK0,sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))),u1_struct_0(sK0),u1_struct_0(sK0))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f376,f331])).

fof(f376,plain,
    ( v1_funct_2(k7_tmap_1(sK0,sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f375,f66])).

fof(f375,plain,
    ( v1_funct_2(k7_tmap_1(sK0,sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f374,f67])).

fof(f374,plain,
    ( v1_funct_2(k7_tmap_1(sK0,sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f357,f68])).

fof(f357,plain,
    ( v1_funct_2(k7_tmap_1(sK0,sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(superposition,[],[f102,f341])).

fof(f341,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f340,f66])).

fof(f340,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f339,f67])).

fof(f339,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f335,f68])).

fof(f335,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f331,f86])).

fof(f526,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f525,f389])).

fof(f389,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(duplicate_literal_removal,[],[f388])).

fof(f388,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(superposition,[],[f373,f314])).

fof(f373,plain,
    ( m1_subset_1(k7_tmap_1(sK0,sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f372,f331])).

fof(f372,plain,
    ( m1_subset_1(k7_tmap_1(sK0,sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f371,f66])).

fof(f371,plain,
    ( m1_subset_1(k7_tmap_1(sK0,sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f370,f67])).

fof(f370,plain,
    ( m1_subset_1(k7_tmap_1(sK0,sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f356,f68])).

fof(f356,plain,
    ( m1_subset_1(k7_tmap_1(sK0,sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(superposition,[],[f103,f341])).

fof(f525,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f524,f352])).

fof(f352,plain,
    ( v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f351,f66])).

fof(f351,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f350,f67])).

fof(f350,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f349,f68])).

fof(f349,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f338,f101])).

fof(f524,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f523,f208])).

fof(f208,plain,(
    v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f207,f66])).

fof(f207,plain,
    ( v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f206,f67])).

fof(f206,plain,
    ( v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f205,f68])).

fof(f205,plain,
    ( v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f189,f70])).

fof(f189,plain,
    ( v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f99,f170])).

fof(f99,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f523,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f522,f204])).

fof(f204,plain,(
    m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f203,f66])).

fof(f203,plain,
    ( m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f202,f67])).

fof(f202,plain,
    ( m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f201,f68])).

fof(f201,plain,
    ( m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f188,f70])).

fof(f188,plain,
    ( m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f100,f170])).

fof(f100,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f522,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f521])).

fof(f521,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f520,f105])).

fof(f105,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
      | X4 = X5
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
          | X4 != X5 )
        & ( X4 = X5
          | ~ r1_funct_2(X0,X1,X2,X3,X4,X5) ) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f44])).

% (24152)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

fof(f520,plain,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f519,f170])).

fof(f519,plain,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f518,f127])).

fof(f518,plain,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f517,f67])).

fof(f517,plain,
    ( ~ v2_pre_topc(sK0)
    | r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f516,f66])).

fof(f516,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f515,f68])).

fof(f515,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) ),
    inference(resolution,[],[f514,f70])).

fof(f514,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) ) ),
    inference(subsumption_resolution,[],[f513,f98])).

fof(f513,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_funct_1(k9_tmap_1(X0,X1))
      | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) ) ),
    inference(subsumption_resolution,[],[f512,f99])).

fof(f512,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ v1_funct_1(k9_tmap_1(X0,X1))
      | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) ) ),
    inference(subsumption_resolution,[],[f115,f100])).

fof(f115,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ v1_funct_1(k9_tmap_1(X0,X1))
      | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) ) ),
    inference(global_subsumption,[],[f77,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),X2,k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k9_tmap_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4))
      | u1_struct_0(X1) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k9_tmap_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f292,plain,(
    ! [X0] :
      ( r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(forward_demodulation,[],[f291,f169])).

fof(f291,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | r1_tmap_1(sK1,k6_tmap_1(sK0,u1_struct_0(sK1)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),X0) ) ),
    inference(subsumption_resolution,[],[f290,f66])).

fof(f290,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | r1_tmap_1(sK1,k6_tmap_1(sK0,u1_struct_0(sK1)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f289,f67])).

fof(f289,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | r1_tmap_1(sK1,k6_tmap_1(sK0,u1_struct_0(sK1)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f288,f68])).

fof(f288,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | r1_tmap_1(sK1,k6_tmap_1(sK0,u1_struct_0(sK1)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f287,f69])).

fof(f287,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | r1_tmap_1(sK1,k6_tmap_1(sK0,u1_struct_0(sK1)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),X0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f286,f70])).

fof(f286,plain,(
    ! [X2,X0,X3] :
      ( ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | r1_tmap_1(X2,k6_tmap_1(X0,u1_struct_0(X2)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X3)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f111,f77])).

fof(f111,plain,(
    ! [X2,X0,X3] :
      ( r1_tmap_1(X2,k6_tmap_1(X0,u1_struct_0(X2)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | u1_struct_0(X2) != X1
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( u1_struct_0(X2) = X1
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X2))
                   => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_tmap_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:09:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (24168)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.46  % (24160)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.46  % (24160)Refutation not found, incomplete strategy% (24160)------------------------------
% 0.20/0.46  % (24160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (24160)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (24160)Memory used [KB]: 6268
% 0.20/0.46  % (24160)Time elapsed: 0.055 s
% 0.20/0.46  % (24160)------------------------------
% 0.20/0.46  % (24160)------------------------------
% 0.20/0.49  % (24168)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f651,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(subsumption_resolution,[],[f650,f71])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    m1_subset_1(sK2,u1_struct_0(sK1))),
% 0.20/0.49    inference(cnf_transformation,[],[f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ((~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK2) & m1_subset_1(sK2,u1_struct_0(sK1))) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f48,f47,f46])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(sK0,X1),k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(sK0,X1),k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),X2) & m1_subset_1(X2,u1_struct_0(sK1))) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ? [X2] : (~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),X2) & m1_subset_1(X2,u1_struct_0(sK1))) => (~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK2) & m1_subset_1(sK2,u1_struct_0(sK1)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2))))),
% 0.20/0.49    inference(negated_conjecture,[],[f17])).
% 0.20/0.49  fof(f17,conjecture,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_tmap_1)).
% 0.20/0.49  fof(f650,plain,(
% 0.20/0.49    ~m1_subset_1(sK2,u1_struct_0(sK1))),
% 0.20/0.49    inference(resolution,[],[f635,f72])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    ~r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f49])).
% 0.20/0.49  fof(f635,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK1))) )),
% 0.20/0.49    inference(superposition,[],[f292,f632])).
% 0.20/0.49  fof(f632,plain,(
% 0.20/0.49    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))),
% 0.20/0.49    inference(subsumption_resolution,[],[f631,f71])).
% 0.20/0.49  fof(f631,plain,(
% 0.20/0.49    ~m1_subset_1(sK2,u1_struct_0(sK1)) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))),
% 0.20/0.49    inference(resolution,[],[f591,f72])).
% 0.20/0.49  fof(f591,plain,(
% 0.20/0.49    ( ! [X1] : (r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),X1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f590,f69])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    ~v2_struct_0(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f49])).
% 0.20/0.49  fof(f590,plain,(
% 0.20/0.49    ( ! [X1] : (k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | v2_struct_0(sK1) | r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),X1)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f589,f70])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    m1_pre_topc(sK1,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f49])).
% 0.20/0.49  fof(f589,plain,(
% 0.20/0.49    ( ! [X1] : (k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),X1)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f588,f117])).
% 0.20/0.49  fof(f117,plain,(
% 0.20/0.49    l1_pre_topc(sK1)),
% 0.20/0.49    inference(resolution,[],[f116,f70])).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) )),
% 0.20/0.49    inference(resolution,[],[f76,f68])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    l1_pre_topc(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f49])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.49  fof(f588,plain,(
% 0.20/0.49    ( ! [X1] : (k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),X1)) )),
% 0.20/0.49    inference(resolution,[],[f586,f277])).
% 0.20/0.49  fof(f277,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tsep_1(sK1,X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | r1_tmap_1(X1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X1),X0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f276,f66])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    ~v2_struct_0(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f49])).
% 0.20/0.49  fof(f276,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~r1_tsep_1(sK1,X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | r1_tmap_1(X1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X1),X0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f275,f67])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    v2_pre_topc(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f49])).
% 0.20/0.49  fof(f275,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~r1_tsep_1(sK1,X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | r1_tmap_1(X1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X1),X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f274,f68])).
% 0.20/0.49  fof(f274,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~r1_tsep_1(sK1,X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | r1_tmap_1(X1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X1),X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f273,f69])).
% 0.20/0.49  fof(f273,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~r1_tsep_1(sK1,X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | r1_tmap_1(X1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X1),X0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(resolution,[],[f89,f70])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (~m1_pre_topc(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | ~r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | ~r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_tmap_1)).
% 0.20/0.49  fof(f586,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tsep_1(X0,sK1) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(resolution,[],[f585,f75])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.49  fof(f585,plain,(
% 0.20/0.49    ( ! [X0] : (~l1_struct_0(X0) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | r1_tsep_1(X0,sK1)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f584,f117])).
% 0.20/0.49  fof(f584,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tsep_1(X0,sK1) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~l1_struct_0(X0) | ~l1_pre_topc(sK1)) )),
% 0.20/0.49    inference(resolution,[],[f575,f75])).
% 0.20/0.49  fof(f575,plain,(
% 0.20/0.49    ( ! [X2] : (~l1_struct_0(sK1) | r1_tsep_1(X2,sK1) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~l1_struct_0(X2)) )),
% 0.20/0.49    inference(resolution,[],[f570,f74])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f50])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).
% 0.20/0.49  fof(f570,plain,(
% 0.20/0.49    ( ! [X1] : (r1_xboole_0(X1,u1_struct_0(sK1)) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))) )),
% 0.20/0.49    inference(resolution,[],[f567,f93])).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f64])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f63])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.49    inference(rectify,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.49  fof(f567,plain,(
% 0.20/0.49    ( ! [X2] : (~r2_hidden(X2,u1_struct_0(sK1)) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))) )),
% 0.20/0.49    inference(resolution,[],[f564,f90])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f62])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK5(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f60,f61])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.49    inference(rectify,[],[f59])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.49    inference(nnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.49  fof(f564,plain,(
% 0.20/0.49    v1_xboole_0(u1_struct_0(sK1)) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f559])).
% 0.20/0.49  fof(f559,plain,(
% 0.20/0.49    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1)) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))),
% 0.20/0.49    inference(resolution,[],[f555,f338])).
% 0.20/0.49  fof(f338,plain,(
% 0.20/0.49    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f337])).
% 0.20/0.49  fof(f337,plain,(
% 0.20/0.49    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))),
% 0.20/0.49    inference(superposition,[],[f331,f314])).
% 0.20/0.49  fof(f314,plain,(
% 0.20/0.49    u1_struct_0(sK1) = sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))),
% 0.20/0.49    inference(subsumption_resolution,[],[f313,f68])).
% 0.20/0.49  fof(f313,plain,(
% 0.20/0.49    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | u1_struct_0(sK1) = sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))) | ~l1_pre_topc(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f312,f70])).
% 0.20/0.49  fof(f312,plain,(
% 0.20/0.49    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | u1_struct_0(sK1) = sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.20/0.49    inference(resolution,[],[f311,f77])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.20/0.49  fof(f311,plain,(
% 0.20/0.49    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | u1_struct_0(sK1) = sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))),
% 0.20/0.49    inference(subsumption_resolution,[],[f310,f70])).
% 0.20/0.49  fof(f310,plain,(
% 0.20/0.49    u1_struct_0(sK1) = sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(sK1,sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f309,f66])).
% 0.20/0.49  fof(f309,plain,(
% 0.20/0.49    u1_struct_0(sK1) = sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~m1_pre_topc(sK1,sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f308,f67])).
% 0.20/0.49  fof(f308,plain,(
% 0.20/0.49    u1_struct_0(sK1) = sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(sK1,sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f307,f68])).
% 0.20/0.49  fof(f307,plain,(
% 0.20/0.49    u1_struct_0(sK1) = sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(sK1,sK0)),
% 0.20/0.49    inference(resolution,[],[f306,f121])).
% 0.20/0.49  fof(f121,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,u1_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f120])).
% 0.20/0.49  fof(f120,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,u1_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(resolution,[],[f101,f77])).
% 0.20/0.49  fof(f101,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_funct_1(k7_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).
% 0.20/0.49  fof(f306,plain,(
% 0.20/0.49    ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | u1_struct_0(sK1) = sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    inference(subsumption_resolution,[],[f304,f156])).
% 0.20/0.49  fof(f156,plain,(
% 0.20/0.49    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    inference(subsumption_resolution,[],[f155,f66])).
% 0.20/0.49  fof(f155,plain,(
% 0.20/0.49    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f154,f67])).
% 0.20/0.49  fof(f154,plain,(
% 0.20/0.49    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f153,f68])).
% 0.20/0.49  fof(f153,plain,(
% 0.20/0.49    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.49    inference(superposition,[],[f103,f127])).
% 0.20/0.49  fof(f127,plain,(
% 0.20/0.49    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))),
% 0.20/0.49    inference(subsumption_resolution,[],[f126,f66])).
% 0.20/0.49  fof(f126,plain,(
% 0.20/0.49    v2_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))),
% 0.20/0.49    inference(subsumption_resolution,[],[f125,f67])).
% 0.20/0.49  fof(f125,plain,(
% 0.20/0.49    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))),
% 0.20/0.49    inference(subsumption_resolution,[],[f124,f68])).
% 0.20/0.49  fof(f124,plain,(
% 0.20/0.49    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))),
% 0.20/0.49    inference(resolution,[],[f123,f70])).
% 0.20/0.49  fof(f123,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1)))) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f122])).
% 0.20/0.49  fof(f122,plain,(
% 0.20/0.49    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(resolution,[],[f86,f77])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f42])).
% 0.20/0.49  fof(f304,plain,(
% 0.20/0.49    ~m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | u1_struct_0(sK1) = sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    inference(resolution,[],[f303,f151])).
% 0.20/0.49  fof(f151,plain,(
% 0.20/0.49    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    inference(subsumption_resolution,[],[f150,f66])).
% 0.20/0.49  fof(f150,plain,(
% 0.20/0.49    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f149,f67])).
% 0.20/0.49  fof(f149,plain,(
% 0.20/0.49    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f148,f68])).
% 0.20/0.49  fof(f148,plain,(
% 0.20/0.49    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.49    inference(superposition,[],[f102,f127])).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f42])).
% 0.20/0.49  fof(f303,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | u1_struct_0(sK1) = sK4(sK0,sK1,X0) | ~v1_funct_1(X0) | k9_tmap_1(sK0,sK1) = X0) )),
% 0.20/0.49    inference(forward_demodulation,[],[f302,f170])).
% 0.20/0.49  fof(f170,plain,(
% 0.20/0.49    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))),
% 0.20/0.49    inference(superposition,[],[f127,f169])).
% 0.20/0.49  fof(f169,plain,(
% 0.20/0.49    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))),
% 0.20/0.49    inference(subsumption_resolution,[],[f168,f68])).
% 0.20/0.49  fof(f168,plain,(
% 0.20/0.49    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~l1_pre_topc(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f167,f67])).
% 0.20/0.49  fof(f167,plain,(
% 0.20/0.49    ~v2_pre_topc(sK0) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~l1_pre_topc(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f166,f66])).
% 0.20/0.49  fof(f166,plain,(
% 0.20/0.49    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~l1_pre_topc(sK0)),
% 0.20/0.49    inference(resolution,[],[f165,f70])).
% 0.20/0.49  fof(f165,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f164,f97])).
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).
% 0.20/0.49  fof(f164,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f163,f96])).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f38])).
% 0.20/0.49  fof(f163,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | v2_struct_0(X0) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f114,f95])).
% 0.20/0.49  fof(f95,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f38])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(X0) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | v2_struct_0(X0) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(global_subsumption,[],[f77,f108])).
% 0.20/0.49  fof(f108,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f107])).
% 0.20/0.49  fof(f107,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k6_tmap_1(X0,u1_struct_0(X1)) = X2 | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f78])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X1] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f54])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | (k6_tmap_1(X0,sK3(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK3(X0,X1,X2) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f52,f53])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ! [X2,X1,X0] : (? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k6_tmap_1(X0,sK3(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK3(X0,X1,X2) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(rectify,[],[f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_tmap_1)).
% 0.20/0.49  fof(f302,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | u1_struct_0(sK1) = sK4(sK0,sK1,X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(X0) | k9_tmap_1(sK0,sK1) = X0) )),
% 0.20/0.49    inference(forward_demodulation,[],[f301,f170])).
% 0.20/0.49  fof(f301,plain,(
% 0.20/0.49    ( ! [X0] : (u1_struct_0(sK1) = sK4(sK0,sK1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(X0) | k9_tmap_1(sK0,sK1) = X0) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f300,f66])).
% 0.20/0.49  fof(f300,plain,(
% 0.20/0.49    ( ! [X0] : (u1_struct_0(sK1) = sK4(sK0,sK1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(X0) | k9_tmap_1(sK0,sK1) = X0 | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f299,f67])).
% 0.20/0.49  fof(f299,plain,(
% 0.20/0.49    ( ! [X0] : (u1_struct_0(sK1) = sK4(sK0,sK1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(X0) | k9_tmap_1(sK0,sK1) = X0 | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f298,f68])).
% 0.20/0.49  fof(f298,plain,(
% 0.20/0.49    ( ! [X0] : (u1_struct_0(sK1) = sK4(sK0,sK1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(X0) | k9_tmap_1(sK0,sK1) = X0 | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(resolution,[],[f84,f70])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | u1_struct_0(X1) = sK4(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | k9_tmap_1(X0,X1) = X2 | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f58])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK4(X0,X1,X2))),X2,k7_tmap_1(X0,sK4(X0,X1,X2))) & u1_struct_0(X1) = sK4(X0,X1,X2) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f56,f57])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ! [X2,X1,X0] : (? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK4(X0,X1,X2))),X2,k7_tmap_1(X0,sK4(X0,X1,X2))) & u1_struct_0(X1) = sK4(X0,X1,X2) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(rectify,[],[f55])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f29])).
% 0.20/0.49  % (24151)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : ((r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(X2)) => (k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_tmap_1)).
% 0.20/0.49  fof(f331,plain,(
% 0.20/0.49    m1_subset_1(sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))),
% 0.20/0.49    inference(subsumption_resolution,[],[f330,f68])).
% 0.20/0.49  fof(f330,plain,(
% 0.20/0.49    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | m1_subset_1(sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f329,f70])).
% 0.20/0.49  fof(f329,plain,(
% 0.20/0.49    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | m1_subset_1(sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.20/0.49    inference(resolution,[],[f328,f77])).
% 0.20/0.49  fof(f328,plain,(
% 0.20/0.49    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | m1_subset_1(sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    inference(subsumption_resolution,[],[f327,f70])).
% 0.20/0.49  fof(f327,plain,(
% 0.20/0.49    m1_subset_1(sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(sK1,sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f326,f66])).
% 0.20/0.49  fof(f326,plain,(
% 0.20/0.49    m1_subset_1(sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~m1_pre_topc(sK1,sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f325,f67])).
% 0.20/0.49  fof(f325,plain,(
% 0.20/0.49    m1_subset_1(sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(sK1,sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f324,f68])).
% 0.20/0.49  fof(f324,plain,(
% 0.20/0.49    m1_subset_1(sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(sK1,sK0)),
% 0.20/0.49    inference(resolution,[],[f323,f121])).
% 0.20/0.49  fof(f323,plain,(
% 0.20/0.49    ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | m1_subset_1(sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    inference(subsumption_resolution,[],[f321,f156])).
% 0.20/0.49  fof(f321,plain,(
% 0.20/0.49    ~m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | m1_subset_1(sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    inference(resolution,[],[f320,f151])).
% 0.20/0.49  fof(f320,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_funct_1(X0) | k9_tmap_1(sK0,sK1) = X0) )),
% 0.20/0.49    inference(forward_demodulation,[],[f319,f170])).
% 0.20/0.49  fof(f319,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(X0) | k9_tmap_1(sK0,sK1) = X0) )),
% 0.20/0.49    inference(forward_demodulation,[],[f318,f170])).
% 0.20/0.49  fof(f318,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(X0) | k9_tmap_1(sK0,sK1) = X0) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f317,f66])).
% 0.20/0.49  fof(f317,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(X0) | k9_tmap_1(sK0,sK1) = X0 | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f316,f67])).
% 0.20/0.49  fof(f316,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(X0) | k9_tmap_1(sK0,sK1) = X0 | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f315,f68])).
% 0.20/0.49  fof(f315,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(sK4(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(X0) | k9_tmap_1(sK0,sK1) = X0 | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(resolution,[],[f83,f70])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | k9_tmap_1(X0,X1) = X2 | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f58])).
% 0.20/0.49  fof(f555,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | v1_xboole_0(X0)) )),
% 0.20/0.49    inference(resolution,[],[f533,f91])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    ( ! [X0] : (r2_hidden(sK5(X0),X0) | v1_xboole_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f62])).
% 0.20/0.49  fof(f533,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))) )),
% 0.20/0.49    inference(resolution,[],[f532,f104])).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.49  fof(f532,plain,(
% 0.20/0.49    v1_xboole_0(u1_struct_0(sK0)) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))),
% 0.20/0.49    inference(subsumption_resolution,[],[f531,f66])).
% 0.20/0.49  fof(f531,plain,(
% 0.20/0.49    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f530,f67])).
% 0.20/0.49  fof(f530,plain,(
% 0.20/0.49    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f529,f68])).
% 0.20/0.49  fof(f529,plain,(
% 0.20/0.49    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f528,f70])).
% 0.20/0.49  fof(f528,plain,(
% 0.20/0.49    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK0)) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.49    inference(resolution,[],[f527,f98])).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f12])).
% 0.20/0.49  % (24161)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  fof(f12,axiom,(
% 0.20/0.49    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_tmap_1)).
% 0.20/0.49  fof(f527,plain,(
% 0.20/0.49    ~v1_funct_1(k9_tmap_1(sK0,sK1)) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.49    inference(subsumption_resolution,[],[f526,f381])).
% 0.20/0.49  fof(f381,plain,(
% 0.20/0.49    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0)) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f380])).
% 0.20/0.49  fof(f380,plain,(
% 0.20/0.49    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0)) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))),
% 0.20/0.49    inference(superposition,[],[f377,f314])).
% 0.20/0.49  fof(f377,plain,(
% 0.20/0.49    v1_funct_2(k7_tmap_1(sK0,sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))),u1_struct_0(sK0),u1_struct_0(sK0)) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))),
% 0.20/0.49    inference(subsumption_resolution,[],[f376,f331])).
% 0.20/0.49  fof(f376,plain,(
% 0.20/0.49    v1_funct_2(k7_tmap_1(sK0,sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))),
% 0.20/0.49    inference(subsumption_resolution,[],[f375,f66])).
% 0.20/0.49  fof(f375,plain,(
% 0.20/0.49    v1_funct_2(k7_tmap_1(sK0,sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))),
% 0.20/0.49    inference(subsumption_resolution,[],[f374,f67])).
% 0.20/0.49  fof(f374,plain,(
% 0.20/0.49    v1_funct_2(k7_tmap_1(sK0,sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))),
% 0.20/0.49    inference(subsumption_resolution,[],[f357,f68])).
% 0.20/0.49  fof(f357,plain,(
% 0.20/0.49    v1_funct_2(k7_tmap_1(sK0,sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))),
% 0.20/0.49    inference(superposition,[],[f102,f341])).
% 0.20/0.49  fof(f341,plain,(
% 0.20/0.49    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))))) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))),
% 0.20/0.49    inference(subsumption_resolution,[],[f340,f66])).
% 0.20/0.49  fof(f340,plain,(
% 0.20/0.49    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))))) | v2_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f339,f67])).
% 0.20/0.49  fof(f339,plain,(
% 0.20/0.49    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f335,f68])).
% 0.20/0.49  fof(f335,plain,(
% 0.20/0.49    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.49    inference(resolution,[],[f331,f86])).
% 0.20/0.49  fof(f526,plain,(
% 0.20/0.49    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k9_tmap_1(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.49    inference(subsumption_resolution,[],[f525,f389])).
% 0.20/0.49  fof(f389,plain,(
% 0.20/0.49    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f388])).
% 0.20/0.49  fof(f388,plain,(
% 0.20/0.49    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))),
% 0.20/0.49    inference(superposition,[],[f373,f314])).
% 0.20/0.49  fof(f373,plain,(
% 0.20/0.49    m1_subset_1(k7_tmap_1(sK0,sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))),
% 0.20/0.49    inference(subsumption_resolution,[],[f372,f331])).
% 0.20/0.49  fof(f372,plain,(
% 0.20/0.49    m1_subset_1(k7_tmap_1(sK0,sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~m1_subset_1(sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))),
% 0.20/0.49    inference(subsumption_resolution,[],[f371,f66])).
% 0.20/0.49  fof(f371,plain,(
% 0.20/0.49    m1_subset_1(k7_tmap_1(sK0,sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~m1_subset_1(sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))),
% 0.20/0.49    inference(subsumption_resolution,[],[f370,f67])).
% 0.20/0.49  fof(f370,plain,(
% 0.20/0.49    m1_subset_1(k7_tmap_1(sK0,sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~m1_subset_1(sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))),
% 0.20/0.49    inference(subsumption_resolution,[],[f356,f68])).
% 0.20/0.49  fof(f356,plain,(
% 0.20/0.49    m1_subset_1(k7_tmap_1(sK0,sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~m1_subset_1(sK4(sK0,sK1,k7_tmap_1(sK0,u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))),
% 0.20/0.49    inference(superposition,[],[f103,f341])).
% 0.20/0.49  fof(f525,plain,(
% 0.20/0.49    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k9_tmap_1(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.49    inference(subsumption_resolution,[],[f524,f352])).
% 0.20/0.49  fof(f352,plain,(
% 0.20/0.49    v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))),
% 0.20/0.49    inference(subsumption_resolution,[],[f351,f66])).
% 0.20/0.49  fof(f351,plain,(
% 0.20/0.49    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | v2_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f350,f67])).
% 0.20/0.49  fof(f350,plain,(
% 0.20/0.49    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f349,f68])).
% 0.20/0.49  fof(f349,plain,(
% 0.20/0.49    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.49    inference(resolution,[],[f338,f101])).
% 0.20/0.49  fof(f524,plain,(
% 0.20/0.49    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | ~v1_funct_1(k9_tmap_1(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.49    inference(subsumption_resolution,[],[f523,f208])).
% 0.20/0.49  fof(f208,plain,(
% 0.20/0.49    v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))),
% 0.20/0.49    inference(subsumption_resolution,[],[f207,f66])).
% 0.20/0.49  fof(f207,plain,(
% 0.20/0.49    v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f206,f67])).
% 0.20/0.49  fof(f206,plain,(
% 0.20/0.49    v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f205,f68])).
% 0.20/0.49  fof(f205,plain,(
% 0.20/0.49    v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f189,f70])).
% 0.20/0.49  fof(f189,plain,(
% 0.20/0.49    v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.49    inference(superposition,[],[f99,f170])).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f40])).
% 0.20/0.49  fof(f523,plain,(
% 0.20/0.49    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k9_tmap_1(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.49    inference(subsumption_resolution,[],[f522,f204])).
% 0.20/0.49  fof(f204,plain,(
% 0.20/0.49    m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.20/0.49    inference(subsumption_resolution,[],[f203,f66])).
% 0.20/0.49  fof(f203,plain,(
% 0.20/0.49    m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | v2_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f202,f67])).
% 0.20/0.49  fof(f202,plain,(
% 0.20/0.49    m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f201,f68])).
% 0.20/0.49  fof(f201,plain,(
% 0.20/0.49    m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f188,f70])).
% 0.20/0.49  fof(f188,plain,(
% 0.20/0.49    m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.49    inference(superposition,[],[f100,f170])).
% 0.20/0.49  fof(f100,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f40])).
% 0.20/0.49  fof(f522,plain,(
% 0.20/0.49    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k9_tmap_1(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f521])).
% 0.20/0.49  fof(f521,plain,(
% 0.20/0.49    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k9_tmap_1(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.49    inference(resolution,[],[f520,f105])).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 = X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f65])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 0.20/0.49    inference(nnf_transformation,[],[f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 0.20/0.49    inference(flattening,[],[f44])).
% 0.20/0.49  % (24152)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).
% 0.20/0.49  fof(f520,plain,(
% 0.20/0.49    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))),
% 0.20/0.49    inference(forward_demodulation,[],[f519,f170])).
% 0.20/0.49  fof(f519,plain,(
% 0.20/0.49    r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))),
% 0.20/0.49    inference(forward_demodulation,[],[f518,f127])).
% 0.20/0.49  fof(f518,plain,(
% 0.20/0.49    r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))),
% 0.20/0.49    inference(subsumption_resolution,[],[f517,f67])).
% 0.20/0.49  fof(f517,plain,(
% 0.20/0.49    ~v2_pre_topc(sK0) | r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))),
% 0.20/0.49    inference(subsumption_resolution,[],[f516,f66])).
% 0.20/0.49  fof(f516,plain,(
% 0.20/0.49    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))),
% 0.20/0.49    inference(subsumption_resolution,[],[f515,f68])).
% 0.20/0.49  fof(f515,plain,(
% 0.20/0.49    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))),
% 0.20/0.49    inference(resolution,[],[f514,f70])).
% 0.20/0.49  fof(f514,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f513,f98])).
% 0.20/0.49  fof(f513,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~v1_funct_1(k9_tmap_1(X0,X1)) | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f512,f99])).
% 0.20/0.49  fof(f512,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v2_pre_topc(X0) | ~v1_funct_1(k9_tmap_1(X0,X1)) | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f115,f100])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v2_pre_topc(X0) | ~v1_funct_1(k9_tmap_1(X0,X1)) | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))) )),
% 0.20/0.49    inference(global_subsumption,[],[f77,f110])).
% 0.20/0.49  fof(f110,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f109])).
% 0.20/0.49  fof(f109,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),X2,k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f82])).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f58])).
% 0.20/0.49  fof(f292,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tmap_1(sK1,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK1))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f291,f169])).
% 0.20/0.49  fof(f291,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | r1_tmap_1(sK1,k6_tmap_1(sK0,u1_struct_0(sK1)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),X0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f290,f66])).
% 0.20/0.49  fof(f290,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | r1_tmap_1(sK1,k6_tmap_1(sK0,u1_struct_0(sK1)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),X0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f289,f67])).
% 0.20/0.49  fof(f289,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | r1_tmap_1(sK1,k6_tmap_1(sK0,u1_struct_0(sK1)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f288,f68])).
% 0.20/0.49  fof(f288,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | r1_tmap_1(sK1,k6_tmap_1(sK0,u1_struct_0(sK1)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f287,f69])).
% 0.20/0.49  fof(f287,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | r1_tmap_1(sK1,k6_tmap_1(sK0,u1_struct_0(sK1)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),X0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(resolution,[],[f286,f70])).
% 0.20/0.49  fof(f286,plain,(
% 0.20/0.49    ( ! [X2,X0,X3] : (~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,u1_struct_0(X2)) | r1_tmap_1(X2,k6_tmap_1(X0,u1_struct_0(X2)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X3) | v2_struct_0(X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f111,f77])).
% 0.20/0.49  fof(f111,plain,(
% 0.20/0.49    ( ! [X2,X0,X3] : (r1_tmap_1(X2,k6_tmap_1(X0,u1_struct_0(X2)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f88])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2)) | u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | u1_struct_0(X2) != X1) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (u1_struct_0(X2) = X1 => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_tmap_1)).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (24168)------------------------------
% 0.20/0.49  % (24168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (24168)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (24168)Memory used [KB]: 6652
% 0.20/0.49  % (24168)Time elapsed: 0.084 s
% 0.20/0.49  % (24168)------------------------------
% 0.20/0.49  % (24168)------------------------------
% 0.20/0.50  % (24146)Success in time 0.142 s
%------------------------------------------------------------------------------
