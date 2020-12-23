%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1327+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  116 (1068 expanded)
%              Number of leaves         :   11 ( 193 expanded)
%              Depth                    :   21
%              Number of atoms          :  408 (4121 expanded)
%              Number of equality atoms :   37 (  96 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f386,plain,(
    $false ),
    inference(subsumption_resolution,[],[f385,f369])).

fof(f369,plain,(
    v4_pre_topc(sK6(sK0,sK1,sK2,sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2))),sK0) ),
    inference(subsumption_resolution,[],[f363,f342])).

fof(f342,plain,(
    r2_hidden(sK6(sK0,sK1,sK2,sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2))),sK2) ),
    inference(subsumption_resolution,[],[f341,f34])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k1_tops_2(X0,X1,X2),k1_pre_topc(X0,X1))
              & v2_tops_2(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k1_tops_2(X0,X1,X2),k1_pre_topc(X0,X1))
              & v2_tops_2(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( v2_tops_2(X2,X0)
                 => v2_tops_2(k1_tops_2(X0,X1,X2),k1_pre_topc(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v2_tops_2(X2,X0)
               => v2_tops_2(k1_tops_2(X0,X1,X2),k1_pre_topc(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_2)).

fof(f341,plain,
    ( r2_hidden(sK6(sK0,sK1,sK2,sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2))),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f225,f176])).

fof(f176,plain,(
    r2_hidden(sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2)),k1_tops_2(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f175,f36])).

fof(f36,plain,(
    ~ v2_tops_2(k1_tops_2(sK0,sK1,sK2),k1_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f175,plain,
    ( r2_hidden(sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2)),k1_tops_2(sK0,sK1,sK2))
    | v2_tops_2(k1_tops_2(sK0,sK1,sK2),k1_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f160,f115])).

fof(f115,plain,(
    l1_pre_topc(k1_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f104,f38])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f104,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(k1_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f84,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f84,plain,(
    m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f83,f38])).

fof(f83,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) ),
    inference(resolution,[],[f62,f37])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f160,plain,
    ( ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | r2_hidden(sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2)),k1_tops_2(sK0,sK1,sK2))
    | v2_tops_2(k1_tops_2(sK0,sK1,sK2),k1_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f128,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK7(X0,X1),X1)
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f128,plain,(
    m1_subset_1(k1_tops_2(sK0,sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))) ),
    inference(resolution,[],[f98,f34])).

fof(f98,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | m1_subset_1(k1_tops_2(sK0,sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))) ) ),
    inference(subsumption_resolution,[],[f97,f38])).

fof(f97,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | m1_subset_1(k1_tops_2(sK0,sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))) ) ),
    inference(resolution,[],[f65,f37])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_2)).

fof(f225,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2)),k1_tops_2(sK0,sK1,X2))
      | r2_hidden(sK6(sK0,sK1,X2,sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2))),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f224,f38])).

fof(f224,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ l1_pre_topc(sK0)
      | r2_hidden(sK6(sK0,sK1,X2,sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2))),X2)
      | ~ r2_hidden(sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2)),k1_tops_2(sK0,sK1,X2)) ) ),
    inference(subsumption_resolution,[],[f213,f37])).

fof(f213,plain,(
    ! [X2] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ l1_pre_topc(sK0)
      | r2_hidden(sK6(sK0,sK1,X2,sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2))),X2)
      | ~ r2_hidden(sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2)),k1_tops_2(sK0,sK1,X2)) ) ),
    inference(resolution,[],[f174,f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK6(X0,X1,X2,X4),X2)
      | ~ r2_hidden(X4,k1_tops_2(X0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f71,f65])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | r2_hidden(sK6(X0,X1,X2,X4),X2)
      | ~ r2_hidden(X4,k1_tops_2(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | r2_hidden(sK6(X0,X1,X2,X4),X2)
      | ~ r2_hidden(X4,X3)
      | k1_tops_2(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tops_2(X0,X1,X2) = X3
                  <=> ! [X4] :
                        ( ( r2_hidden(X4,X3)
                        <=> ? [X5] :
                              ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                              & r2_hidden(X5,X2)
                              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
                 => ( k1_tops_2(X0,X1,X2) = X3
                  <=> ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
                       => ( r2_hidden(X4,X3)
                        <=> ? [X5] :
                              ( k9_subset_1(u1_struct_0(X0),X5,X1) = X4
                              & r2_hidden(X5,X2)
                              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_2)).

fof(f174,plain,(
    m1_subset_1(sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) ),
    inference(subsumption_resolution,[],[f173,f36])).

fof(f173,plain,
    ( m1_subset_1(sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | v2_tops_2(k1_tops_2(sK0,sK1,sK2),k1_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f159,f115])).

fof(f159,plain,
    ( ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | m1_subset_1(sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | v2_tops_2(k1_tops_2(sK0,sK1,sK2),k1_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f128,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f363,plain,
    ( ~ r2_hidden(sK6(sK0,sK1,sK2,sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2))),sK2)
    | v4_pre_topc(sK6(sK0,sK1,sK2,sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2))),sK0) ),
    inference(resolution,[],[f344,f96])).

fof(f96,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,sK2)
      | v4_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f95,f35])).

fof(f35,plain,(
    v2_tops_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f95,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,sK2)
      | v4_pre_topc(X0,sK0)
      | ~ v2_tops_2(sK2,sK0) ) ),
    inference(subsumption_resolution,[],[f94,f38])).

fof(f94,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,sK2)
      | v4_pre_topc(X0,sK0)
      | ~ v2_tops_2(sK2,sK0) ) ),
    inference(resolution,[],[f57,f34])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,X1)
      | v4_pre_topc(X2,X0)
      | ~ v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f344,plain,(
    m1_subset_1(sK6(sK0,sK1,sK2,sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f343,f34])).

fof(f343,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK2,sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f223,f176])).

fof(f223,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2)),k1_tops_2(sK0,sK1,X1))
      | m1_subset_1(sK6(sK0,sK1,X1,sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    inference(subsumption_resolution,[],[f222,f38])).

fof(f222,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ l1_pre_topc(sK0)
      | m1_subset_1(sK6(sK0,sK1,X1,sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2)),k1_tops_2(sK0,sK1,X1)) ) ),
    inference(subsumption_resolution,[],[f212,f37])).

fof(f212,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ l1_pre_topc(sK0)
      | m1_subset_1(sK6(sK0,sK1,X1,sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2)),k1_tops_2(sK0,sK1,X1)) ) ),
    inference(resolution,[],[f174,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK6(X0,X1,X2,X4),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X4,k1_tops_2(X0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f72,f65])).

fof(f72,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | m1_subset_1(sK6(X0,X1,X2,X4),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X4,k1_tops_2(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | m1_subset_1(sK6(X0,X1,X2,X4),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X4,X3)
      | k1_tops_2(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f385,plain,(
    ~ v4_pre_topc(sK6(sK0,sK1,sK2,sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2))),sK0) ),
    inference(subsumption_resolution,[],[f384,f344])).

fof(f384,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2,sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(sK6(sK0,sK1,sK2,sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2))),sK0) ),
    inference(subsumption_resolution,[],[f383,f178])).

fof(f178,plain,(
    ~ v4_pre_topc(sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2)),k1_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f177,f36])).

fof(f177,plain,
    ( ~ v4_pre_topc(sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2)),k1_pre_topc(sK0,sK1))
    | v2_tops_2(k1_tops_2(sK0,sK1,sK2),k1_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f161,f115])).

fof(f161,plain,
    ( ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ v4_pre_topc(sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2)),k1_pre_topc(sK0,sK1))
    | v2_tops_2(k1_tops_2(sK0,sK1,sK2),k1_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f128,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(sK7(X0,X1),X0)
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f383,plain,
    ( v4_pre_topc(sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2)),k1_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(sK6(sK0,sK1,sK2,sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2))),sK0) ),
    inference(subsumption_resolution,[],[f380,f174])).

fof(f380,plain,
    ( ~ m1_subset_1(sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | v4_pre_topc(sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2)),k1_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(sK6(sK0,sK1,sK2,sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2))),sK0) ),
    inference(superposition,[],[f260,f348])).

fof(f348,plain,(
    sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2)) = k3_xboole_0(sK6(sK0,sK1,sK2,sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2))),sK1) ),
    inference(subsumption_resolution,[],[f347,f34])).

fof(f347,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2)) = k3_xboole_0(sK6(sK0,sK1,sK2,sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2))),sK1) ),
    inference(resolution,[],[f221,f176])).

fof(f221,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2)),k1_tops_2(sK0,sK1,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2)) = k3_xboole_0(sK6(sK0,sK1,X0,sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2))),sK1) ) ),
    inference(forward_demodulation,[],[f220,f85])).

fof(f85,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1) ),
    inference(resolution,[],[f63,f37])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f220,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2)) = k9_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,X0,sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2))),sK1)
      | ~ r2_hidden(sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2)),k1_tops_2(sK0,sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f219,f38])).

fof(f219,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ l1_pre_topc(sK0)
      | sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2)) = k9_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,X0,sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2))),sK1)
      | ~ r2_hidden(sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2)),k1_tops_2(sK0,sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f211,f37])).

fof(f211,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ l1_pre_topc(sK0)
      | sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2)) = k9_subset_1(u1_struct_0(sK0),sK6(sK0,sK1,X0,sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2))),sK1)
      | ~ r2_hidden(sK7(k1_pre_topc(sK0,sK1),k1_tops_2(sK0,sK1,sK2)),k1_tops_2(sK0,sK1,X0)) ) ),
    inference(resolution,[],[f174,f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X2,X4),X1) = X4
      | ~ r2_hidden(X4,k1_tops_2(X0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f70,f65])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(k1_tops_2(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X2,X4),X1) = X4
      | ~ r2_hidden(X4,k1_tops_2(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X2,X4),X1) = X4
      | ~ r2_hidden(X4,X3)
      | k1_tops_2(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f260,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k3_xboole_0(X0,sK1),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
      | v4_pre_topc(k3_xboole_0(X0,sK1),k1_pre_topc(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X0,sK0) ) ),
    inference(forward_demodulation,[],[f257,f245])).

fof(f245,plain,(
    ! [X5] : k9_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)),X5,sK1) = k3_xboole_0(X5,sK1) ),
    inference(resolution,[],[f134,f63])).

fof(f134,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f133,f107])).

fof(f107,plain,(
    sK1 = k2_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f106,f38])).

fof(f106,plain,
    ( ~ l1_pre_topc(sK0)
    | sK1 = k2_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f105,f81])).

fof(f81,plain,(
    v1_pre_topc(k1_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f80,f38])).

fof(f80,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_pre_topc(k1_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f61,f37])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_pre_topc(k1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f105,plain,
    ( ~ v1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | sK1 = k2_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f99,f37])).

fof(f99,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | sK1 = k2_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f84,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0)
      | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X2,X0)
      | k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).

fof(f133,plain,(
    m1_subset_1(k2_struct_0(k1_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) ),
    inference(resolution,[],[f126,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f126,plain,(
    l1_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f115,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f257,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k3_xboole_0(X0,sK1),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
      | v4_pre_topc(k9_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)),X0,sK1),k1_pre_topc(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X0,sK0) ) ),
    inference(backward_demodulation,[],[f110,f245])).

fof(f110,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)),X0,sK1),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
      | v4_pre_topc(k9_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)),X0,sK1),k1_pre_topc(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X0,sK0) ) ),
    inference(forward_demodulation,[],[f109,f107])).

fof(f109,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)),X0,sK1),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X0,sK0)
      | v4_pre_topc(k9_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)),X0,k2_struct_0(k1_pre_topc(sK0,sK1))),k1_pre_topc(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f108,f107])).

fof(f108,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)),X0,k2_struct_0(k1_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X0,sK0)
      | v4_pre_topc(k9_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)),X0,k2_struct_0(k1_pre_topc(sK0,sK1))),k1_pre_topc(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f100,f38])).

fof(f100,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)),X0,k2_struct_0(k1_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X0,sK0)
      | v4_pre_topc(k9_subset_1(u1_struct_0(k1_pre_topc(sK0,sK1)),X0,k2_struct_0(k1_pre_topc(sK0,sK1))),k1_pre_topc(sK0,sK1)) ) ),
    inference(resolution,[],[f84,f67])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X3,X0)
      | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X3,X0)
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | v4_pre_topc(X2,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_pre_topc)).

%------------------------------------------------------------------------------
