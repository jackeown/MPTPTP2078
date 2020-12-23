%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1354+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:48 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   81 (1036 expanded)
%              Number of leaves         :   10 ( 224 expanded)
%              Depth                    :   21
%              Number of atoms          :  238 (3273 expanded)
%              Number of equality atoms :    4 (  21 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f368,plain,(
    $false ),
    inference(global_subsumption,[],[f343,f364])).

fof(f364,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK4(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f27,f342,f352,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f352,plain,(
    ~ r2_hidden(k3_subset_1(u1_struct_0(sK0),sK4(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))),u1_pre_topc(sK0)) ),
    inference(unit_resulting_resolution,[],[f53,f70,f324,f311,f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ r2_hidden(k3_subset_1(X0,X3),X1)
      | r2_hidden(X3,k7_setfam_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ r2_hidden(k3_subset_1(X0,X3),X1)
      | r2_hidden(X3,X2)
      | k7_setfam_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).

fof(f311,plain,(
    ~ r2_hidden(sK4(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))),k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(unit_resulting_resolution,[],[f308,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f308,plain,(
    ~ r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(unit_resulting_resolution,[],[f293,f25])).

fof(f25,plain,
    ( ~ r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_2(X1,X0)
          <~> r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v2_tops_2(X1,X0)
            <=> r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tops_2)).

fof(f293,plain,(
    v2_tops_2(sK1,sK0) ),
    inference(global_subsumption,[],[f167,f291])).

fof(f291,plain,
    ( v4_pre_topc(sK2(sK0,sK1),sK0)
    | v2_tops_2(sK1,sK0) ),
    inference(resolution,[],[f290,f136])).

fof(f136,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | v2_tops_2(sK1,sK0) ),
    inference(global_subsumption,[],[f27,f124])).

fof(f124,plain,
    ( ~ l1_pre_topc(sK0)
    | r2_hidden(sK2(sK0,sK1),sK1)
    | v2_tops_2(sK1,sK0) ),
    inference(resolution,[],[f35,f26])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK2(X0,X1),X1)
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_2)).

fof(f290,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | v4_pre_topc(X1,sK0) ) ),
    inference(duplicate_literal_removal,[],[f286])).

fof(f286,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | v4_pre_topc(X1,sK0)
      | ~ r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f284,f61])).

fof(f61,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f47,f26])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f284,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,sK1)
      | v4_pre_topc(X0,sK0) ) ),
    inference(global_subsumption,[],[f27,f217,f283])).

fof(f283,plain,(
    ! [X0] :
      ( v2_tops_2(sK1,sK0)
      | ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | v4_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f266,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(f266,plain,(
    ! [X2] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X2),sK0)
      | v2_tops_2(sK1,sK0)
      | ~ r2_hidden(X2,sK1) ) ),
    inference(resolution,[],[f264,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_pre_topc(sK0))
      | v3_pre_topc(X0,sK0) ) ),
    inference(global_subsumption,[],[f27,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ r2_hidden(X0,u1_pre_topc(sK0))
      | v3_pre_topc(X0,sK0) ) ),
    inference(duplicate_literal_removal,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ r2_hidden(X0,u1_pre_topc(sK0))
      | v3_pre_topc(X0,sK0)
      | ~ r2_hidden(X0,u1_pre_topc(sK0)) ) ),
    inference(resolution,[],[f29,f63])).

fof(f63,plain,(
    ! [X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X3,u1_pre_topc(sK0)) ) ),
    inference(resolution,[],[f47,f53])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f264,plain,(
    ! [X1] :
      ( r2_hidden(k3_subset_1(u1_struct_0(sK0),X1),u1_pre_topc(sK0))
      | ~ r2_hidden(X1,sK1)
      | v2_tops_2(sK1,sK0) ) ),
    inference(resolution,[],[f255,f54])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(X0,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ r2_hidden(X0,sK1)
      | v2_tops_2(sK1,sK0) ) ),
    inference(resolution,[],[f44,f24])).

fof(f24,plain,
    ( r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f255,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | r2_hidden(k3_subset_1(u1_struct_0(sK0),X0),u1_pre_topc(sK0)) ) ),
    inference(global_subsumption,[],[f53,f78,f246])).

fof(f246,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(k3_subset_1(u1_struct_0(sK0),X0),u1_pre_topc(sK0))
      | ~ r2_hidden(X0,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) ) ),
    inference(resolution,[],[f48,f70])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | r2_hidden(k3_subset_1(X0,X3),X1)
      | ~ r2_hidden(X3,k7_setfam_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | r2_hidden(k3_subset_1(X0,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k7_setfam_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f78,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f70,f47])).

fof(f217,plain,(
    ! [X14] :
      ( ~ r2_hidden(X14,sK1)
      | v4_pre_topc(X14,sK0)
      | ~ v2_tops_2(sK1,sK0) ) ),
    inference(global_subsumption,[],[f27,f61,f202])).

fof(f202,plain,(
    ! [X14] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X14,sK1)
      | v4_pre_topc(X14,sK0)
      | ~ v2_tops_2(sK1,sK0) ) ),
    inference(resolution,[],[f33,f26])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,X1)
      | v4_pre_topc(X2,X0)
      | ~ v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f167,plain,
    ( ~ v4_pre_topc(sK2(sK0,sK1),sK0)
    | v2_tops_2(sK1,sK0) ),
    inference(global_subsumption,[],[f27,f154])).

fof(f154,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v4_pre_topc(sK2(sK0,sK1),sK0)
    | v2_tops_2(sK1,sK0) ),
    inference(resolution,[],[f36,f26])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(sK2(X0,X1),X0)
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f324,plain,(
    m1_subset_1(sK4(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f26,f312,f47])).

fof(f312,plain,(
    r2_hidden(sK4(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1) ),
    inference(unit_resulting_resolution,[],[f308,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f70,plain,(
    m1_subset_1(k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f53,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f53,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f27,f28])).

fof(f28,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f342,plain,(
    v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK4(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK0) ),
    inference(unit_resulting_resolution,[],[f27,f310,f324,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f310,plain,(
    v4_pre_topc(sK4(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0) ),
    inference(unit_resulting_resolution,[],[f293,f308,f218])).

fof(f218,plain,(
    ! [X0] :
      ( v4_pre_topc(sK4(sK1,X0),sK0)
      | ~ v2_tops_2(sK1,sK0)
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f217,f45])).

fof(f27,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f343,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK4(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f324,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

%------------------------------------------------------------------------------
