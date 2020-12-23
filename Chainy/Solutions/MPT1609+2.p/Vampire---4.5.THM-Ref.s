%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1609+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:26 EST 2020

% Result     : Theorem 9.80s
% Output     : Refutation 9.80s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 212 expanded)
%              Number of leaves         :   17 (  75 expanded)
%              Depth                    :   21
%              Number of atoms          :  241 ( 694 expanded)
%              Number of equality atoms :   60 ( 281 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12010,plain,(
    $false ),
    inference(subsumption_resolution,[],[f12009,f3860])).

fof(f3860,plain,(
    m1_subset_1(sK31,u1_struct_0(k3_yellow_1(sK30))) ),
    inference(cnf_transformation,[],[f3547])).

fof(f3547,plain,
    ( ( k3_xboole_0(sK31,sK32) != k12_lattice3(k3_yellow_1(sK30),sK31,sK32)
      | k2_xboole_0(sK31,sK32) != k13_lattice3(k3_yellow_1(sK30),sK31,sK32) )
    & m1_subset_1(sK32,u1_struct_0(k3_yellow_1(sK30)))
    & m1_subset_1(sK31,u1_struct_0(k3_yellow_1(sK30))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK30,sK31,sK32])],[f3123,f3546,f3545])).

fof(f3545,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( k3_xboole_0(X1,X2) != k12_lattice3(k3_yellow_1(X0),X1,X2)
              | k2_xboole_0(X1,X2) != k13_lattice3(k3_yellow_1(X0),X1,X2) )
            & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
        & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) )
   => ( ? [X2] :
          ( ( k3_xboole_0(sK31,X2) != k12_lattice3(k3_yellow_1(sK30),sK31,X2)
            | k2_xboole_0(sK31,X2) != k13_lattice3(k3_yellow_1(sK30),sK31,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_yellow_1(sK30))) )
      & m1_subset_1(sK31,u1_struct_0(k3_yellow_1(sK30))) ) ),
    introduced(choice_axiom,[])).

fof(f3546,plain,
    ( ? [X2] :
        ( ( k3_xboole_0(sK31,X2) != k12_lattice3(k3_yellow_1(sK30),sK31,X2)
          | k2_xboole_0(sK31,X2) != k13_lattice3(k3_yellow_1(sK30),sK31,X2) )
        & m1_subset_1(X2,u1_struct_0(k3_yellow_1(sK30))) )
   => ( ( k3_xboole_0(sK31,sK32) != k12_lattice3(k3_yellow_1(sK30),sK31,sK32)
        | k2_xboole_0(sK31,sK32) != k13_lattice3(k3_yellow_1(sK30),sK31,sK32) )
      & m1_subset_1(sK32,u1_struct_0(k3_yellow_1(sK30))) ) ),
    introduced(choice_axiom,[])).

fof(f3123,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( k3_xboole_0(X1,X2) != k12_lattice3(k3_yellow_1(X0),X1,X2)
            | k2_xboole_0(X1,X2) != k13_lattice3(k3_yellow_1(X0),X1,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
      & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(ennf_transformation,[],[f3099])).

fof(f3099,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
           => ( k3_xboole_0(X1,X2) = k12_lattice3(k3_yellow_1(X0),X1,X2)
              & k2_xboole_0(X1,X2) = k13_lattice3(k3_yellow_1(X0),X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f3098])).

fof(f3098,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
         => ( k3_xboole_0(X1,X2) = k12_lattice3(k3_yellow_1(X0),X1,X2)
            & k2_xboole_0(X1,X2) = k13_lattice3(k3_yellow_1(X0),X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow_1)).

fof(f12009,plain,(
    ~ m1_subset_1(sK31,u1_struct_0(k3_yellow_1(sK30))) ),
    inference(forward_demodulation,[],[f12008,f4692])).

fof(f4692,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f4029,f4440])).

fof(f4440,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f1559])).

fof(f1559,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f4029,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f3103])).

fof(f3103,axiom,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).

fof(f12008,plain,(
    ~ m1_subset_1(sK31,u1_struct_0(k2_yellow_1(k1_zfmisc_1(sK30)))) ),
    inference(subsumption_resolution,[],[f12007,f3861])).

fof(f3861,plain,(
    m1_subset_1(sK32,u1_struct_0(k3_yellow_1(sK30))) ),
    inference(cnf_transformation,[],[f3547])).

fof(f12007,plain,
    ( ~ m1_subset_1(sK32,u1_struct_0(k3_yellow_1(sK30)))
    | ~ m1_subset_1(sK31,u1_struct_0(k2_yellow_1(k1_zfmisc_1(sK30)))) ),
    inference(forward_demodulation,[],[f12006,f4692])).

fof(f12006,plain,
    ( ~ m1_subset_1(sK32,u1_struct_0(k2_yellow_1(k1_zfmisc_1(sK30))))
    | ~ m1_subset_1(sK31,u1_struct_0(k2_yellow_1(k1_zfmisc_1(sK30)))) ),
    inference(subsumption_resolution,[],[f12005,f11926])).

fof(f11926,plain,(
    k2_xboole_0(sK31,sK32) != k13_lattice3(k3_yellow_1(sK30),sK31,sK32) ),
    inference(trivial_inequality_removal,[],[f11911])).

fof(f11911,plain,
    ( k3_xboole_0(sK31,sK32) != k3_xboole_0(sK31,sK32)
    | k2_xboole_0(sK31,sK32) != k13_lattice3(k3_yellow_1(sK30),sK31,sK32) ),
    inference(backward_demodulation,[],[f3862,f11910])).

fof(f11910,plain,(
    k3_xboole_0(sK31,sK32) = k12_lattice3(k3_yellow_1(sK30),sK31,sK32) ),
    inference(subsumption_resolution,[],[f11909,f3860])).

fof(f11909,plain,
    ( ~ m1_subset_1(sK31,u1_struct_0(k3_yellow_1(sK30)))
    | k3_xboole_0(sK31,sK32) = k12_lattice3(k3_yellow_1(sK30),sK31,sK32) ),
    inference(forward_demodulation,[],[f11908,f4692])).

fof(f11908,plain,
    ( k3_xboole_0(sK31,sK32) = k12_lattice3(k3_yellow_1(sK30),sK31,sK32)
    | ~ m1_subset_1(sK31,u1_struct_0(k2_yellow_1(k1_zfmisc_1(sK30)))) ),
    inference(subsumption_resolution,[],[f11907,f3861])).

fof(f11907,plain,
    ( ~ m1_subset_1(sK32,u1_struct_0(k3_yellow_1(sK30)))
    | k3_xboole_0(sK31,sK32) = k12_lattice3(k3_yellow_1(sK30),sK31,sK32)
    | ~ m1_subset_1(sK31,u1_struct_0(k2_yellow_1(k1_zfmisc_1(sK30)))) ),
    inference(forward_demodulation,[],[f11906,f4692])).

fof(f11906,plain,
    ( k3_xboole_0(sK31,sK32) = k12_lattice3(k3_yellow_1(sK30),sK31,sK32)
    | ~ m1_subset_1(sK32,u1_struct_0(k2_yellow_1(k1_zfmisc_1(sK30))))
    | ~ m1_subset_1(sK31,u1_struct_0(k2_yellow_1(k1_zfmisc_1(sK30)))) ),
    inference(forward_demodulation,[],[f11905,f10642])).

fof(f10642,plain,(
    k12_lattice3(k3_yellow_1(sK30),sK31,sK32) = k11_lattice3(k3_yellow_1(sK30),sK31,sK32) ),
    inference(unit_resulting_resolution,[],[f4027,f5380,f4020,f3860,f3861,f3863])).

fof(f3863,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3125])).

fof(f3125,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f3124])).

fof(f3124,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2896])).

fof(f2896,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(f4020,plain,(
    ! [X0] : l1_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f3078])).

fof(f3078,axiom,(
    ! [X0] :
      ( l1_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_1)).

fof(f5380,plain,(
    ! [X0] : v2_lattice3(k3_yellow_1(X0)) ),
    inference(unit_resulting_resolution,[],[f4023,f4020,f4022,f4494])).

fof(f4494,plain,(
    ! [X0] :
      ( ~ v3_lattice3(X0)
      | v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3476])).

fof(f3476,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
        & v1_lattice3(X0) )
      | ~ v3_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3475])).

fof(f3475,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
        & v1_lattice3(X0) )
      | ~ v3_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2906])).

fof(f2906,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v3_lattice3(X0)
       => ( v2_lattice3(X0)
          & v1_lattice3(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_lattice3)).

fof(f4022,plain,(
    ! [X0] : v3_lattice3(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f3086])).

fof(f3086,axiom,(
    ! [X0] :
      ( v3_lattice3(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_yellow_1)).

fof(f4023,plain,(
    ! [X0] : ~ v2_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f3085])).

fof(f3085,axiom,(
    ! [X0] :
      ( v5_orders_2(k3_yellow_1(X0))
      & v4_orders_2(k3_yellow_1(X0))
      & v3_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0))
      & ~ v2_struct_0(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_yellow_1)).

fof(f4027,plain,(
    ! [X0] : v5_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f3085])).

fof(f11905,plain,
    ( k3_xboole_0(sK31,sK32) = k11_lattice3(k3_yellow_1(sK30),sK31,sK32)
    | ~ m1_subset_1(sK32,u1_struct_0(k2_yellow_1(k1_zfmisc_1(sK30))))
    | ~ m1_subset_1(sK31,u1_struct_0(k2_yellow_1(k1_zfmisc_1(sK30)))) ),
    inference(forward_demodulation,[],[f11904,f4692])).

fof(f11904,plain,
    ( k3_xboole_0(sK31,sK32) = k11_lattice3(k2_yellow_1(k1_zfmisc_1(sK30)),sK31,sK32)
    | ~ m1_subset_1(sK32,u1_struct_0(k2_yellow_1(k1_zfmisc_1(sK30))))
    | ~ m1_subset_1(sK31,u1_struct_0(k2_yellow_1(k1_zfmisc_1(sK30)))) ),
    inference(subsumption_resolution,[],[f11880,f4400])).

fof(f4400,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f477])).

fof(f477,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f11880,plain,
    ( k3_xboole_0(sK31,sK32) = k11_lattice3(k2_yellow_1(k1_zfmisc_1(sK30)),sK31,sK32)
    | ~ m1_subset_1(sK32,u1_struct_0(k2_yellow_1(k1_zfmisc_1(sK30))))
    | ~ m1_subset_1(sK31,u1_struct_0(k2_yellow_1(k1_zfmisc_1(sK30))))
    | v1_xboole_0(k1_zfmisc_1(sK30)) ),
    inference(resolution,[],[f8382,f4066])).

fof(f4066,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k3_xboole_0(X1,X2),X0)
      | k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3225])).

fof(f3225,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2)
              | ~ r2_hidden(k3_xboole_0(X1,X2),X0)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f3224])).

fof(f3224,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2)
              | ~ r2_hidden(k3_xboole_0(X1,X2),X0)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3108])).

fof(f3108,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r2_hidden(k3_xboole_0(X1,X2),X0)
               => k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_1)).

fof(f8382,plain,(
    r2_hidden(k3_xboole_0(sK31,sK32),k1_zfmisc_1(sK30)) ),
    inference(forward_demodulation,[],[f8358,f3932])).

fof(f3932,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f8358,plain,(
    r2_hidden(k3_xboole_0(sK32,sK31),k1_zfmisc_1(sK30)) ),
    inference(unit_resulting_resolution,[],[f3860,f3861,f4690])).

fof(f4690,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | r2_hidden(k3_xboole_0(X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(backward_demodulation,[],[f4015,f4440])).

fof(f4015,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(cnf_transformation,[],[f3208])).

fof(f3208,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0))
            & r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0)) )
          | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(ennf_transformation,[],[f3087])).

fof(f3087,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
         => ( r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0))
            & r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l19_yellow_1)).

fof(f3862,plain,
    ( k3_xboole_0(sK31,sK32) != k12_lattice3(k3_yellow_1(sK30),sK31,sK32)
    | k2_xboole_0(sK31,sK32) != k13_lattice3(k3_yellow_1(sK30),sK31,sK32) ),
    inference(cnf_transformation,[],[f3547])).

fof(f12005,plain,
    ( k2_xboole_0(sK31,sK32) = k13_lattice3(k3_yellow_1(sK30),sK31,sK32)
    | ~ m1_subset_1(sK32,u1_struct_0(k2_yellow_1(k1_zfmisc_1(sK30))))
    | ~ m1_subset_1(sK31,u1_struct_0(k2_yellow_1(k1_zfmisc_1(sK30)))) ),
    inference(forward_demodulation,[],[f12004,f10751])).

fof(f10751,plain,(
    k13_lattice3(k3_yellow_1(sK30),sK31,sK32) = k10_lattice3(k3_yellow_1(sK30),sK31,sK32) ),
    inference(unit_resulting_resolution,[],[f4027,f5378,f4020,f3860,f3861,f3937])).

fof(f3937,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_lattice3(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3169])).

fof(f3169,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f3168])).

fof(f3168,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2897])).

fof(f2897,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

fof(f5378,plain,(
    ! [X0] : v1_lattice3(k3_yellow_1(X0)) ),
    inference(unit_resulting_resolution,[],[f4023,f4020,f4022,f4493])).

fof(f4493,plain,(
    ! [X0] :
      ( ~ v3_lattice3(X0)
      | v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3476])).

fof(f12004,plain,
    ( k2_xboole_0(sK31,sK32) = k10_lattice3(k3_yellow_1(sK30),sK31,sK32)
    | ~ m1_subset_1(sK32,u1_struct_0(k2_yellow_1(k1_zfmisc_1(sK30))))
    | ~ m1_subset_1(sK31,u1_struct_0(k2_yellow_1(k1_zfmisc_1(sK30)))) ),
    inference(forward_demodulation,[],[f12003,f4692])).

fof(f12003,plain,
    ( k2_xboole_0(sK31,sK32) = k10_lattice3(k2_yellow_1(k1_zfmisc_1(sK30)),sK31,sK32)
    | ~ m1_subset_1(sK32,u1_struct_0(k2_yellow_1(k1_zfmisc_1(sK30))))
    | ~ m1_subset_1(sK31,u1_struct_0(k2_yellow_1(k1_zfmisc_1(sK30)))) ),
    inference(subsumption_resolution,[],[f11979,f4400])).

fof(f11979,plain,
    ( k2_xboole_0(sK31,sK32) = k10_lattice3(k2_yellow_1(k1_zfmisc_1(sK30)),sK31,sK32)
    | ~ m1_subset_1(sK32,u1_struct_0(k2_yellow_1(k1_zfmisc_1(sK30))))
    | ~ m1_subset_1(sK31,u1_struct_0(k2_yellow_1(k1_zfmisc_1(sK30))))
    | v1_xboole_0(k1_zfmisc_1(sK30)) ),
    inference(resolution,[],[f8417,f4338])).

fof(f4338,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k2_xboole_0(X1,X2),X0)
      | k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3389])).

fof(f3389,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2)
              | ~ r2_hidden(k2_xboole_0(X1,X2),X0)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f3388])).

fof(f3388,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2)
              | ~ r2_hidden(k2_xboole_0(X1,X2),X0)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3107])).

fof(f3107,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r2_hidden(k2_xboole_0(X1,X2),X0)
               => k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_yellow_1)).

fof(f8417,plain,(
    r2_hidden(k2_xboole_0(sK31,sK32),k1_zfmisc_1(sK30)) ),
    inference(forward_demodulation,[],[f8393,f4006])).

fof(f4006,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f8393,plain,(
    r2_hidden(k2_xboole_0(sK32,sK31),k1_zfmisc_1(sK30)) ),
    inference(unit_resulting_resolution,[],[f3860,f3861,f4691])).

fof(f4691,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | r2_hidden(k2_xboole_0(X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(backward_demodulation,[],[f4016,f4440])).

fof(f4016,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(cnf_transformation,[],[f3208])).
%------------------------------------------------------------------------------
