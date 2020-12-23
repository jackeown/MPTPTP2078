%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_1__t95_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:34 EDT 2019

% Result     : Theorem 183.19s
% Output     : Refutation 183.19s
% Verified   : 
% Statistics : Number of formulae       :  271 (1529 expanded)
%              Number of leaves         :   39 ( 465 expanded)
%              Depth                    :   28
%              Number of atoms          :  873 (6593 expanded)
%              Number of equality atoms :   88 ( 259 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27003,plain,(
    $false ),
    inference(subsumption_resolution,[],[f358,f27002])).

fof(f27002,plain,(
    ! [X0] : ~ m1_subset_1(X0,k1_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(global_subsumption,[],[f3454,f25741,f25876,f26998])).

fof(f26998,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_tops_1(sK0,k2_tops_1(sK0,sK1)))
      | ~ m1_subset_1(X0,k1_tops_1(sK0,k2_tops_1(sK0,sK1))) ) ),
    inference(resolution,[],[f25501,f185])).

fof(f185,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t95_tops_1.p',t2_subset)).

fof(f25501,plain,(
    ~ v1_xboole_0(k1_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f3744,f3327])).

fof(f3327,plain,(
    ! [X0] :
      ( v2_tops_1(X0,sK0)
      | ~ v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f3326,f3278])).

fof(f3278,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f2728,f164])).

fof(f164,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f50])).

fof(f50,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t95_tops_1.p',t6_boole)).

fof(f2728,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f894,f155])).

fof(f155,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t95_tops_1.p',t2_boole)).

fof(f894,plain,(
    ! [X1] : m1_subset_1(k3_xboole_0(sK1,X1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f365,f181])).

fof(f181,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t95_tops_1.p',commutativity_k3_xboole_0)).

fof(f365,plain,(
    ! [X21] : m1_subset_1(k3_xboole_0(X21,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f317,f316])).

fof(f316,plain,(
    ! [X21] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X21,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f149,f207])).

fof(f207,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f119])).

fof(f119,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t95_tops_1.p',dt_k9_subset_1)).

fof(f149,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f129])).

fof(f129,plain,
    ( ~ v3_tops_1(k2_tops_1(sK0,sK1),sK0)
    & v3_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f65,f128,f127])).

fof(f127,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v3_tops_1(k2_tops_1(X0,X1),X0)
            & v3_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v3_tops_1(k2_tops_1(sK0,X1),sK0)
          & v3_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f128,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_tops_1(k2_tops_1(X0,X1),X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_tops_1(k2_tops_1(X0,sK1),X0)
        & v3_pre_topc(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tops_1(k2_tops_1(X0,X1),X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tops_1(k2_tops_1(X0,X1),X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
             => v3_tops_1(k2_tops_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
           => v3_tops_1(k2_tops_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t95_tops_1.p',t95_tops_1)).

fof(f317,plain,(
    ! [X22] : k3_xboole_0(X22,sK1) = k9_subset_1(u1_struct_0(sK0),X22,sK1) ),
    inference(resolution,[],[f149,f208])).

fof(f208,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f120])).

fof(f120,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t95_tops_1.p',redefinition_k9_subset_1)).

fof(f3326,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v2_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f3325,f147])).

fof(f147,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f129])).

fof(f3325,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v2_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f3317,f148])).

fof(f148,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f129])).

fof(f3317,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v2_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f3313,f175])).

fof(f175,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f84])).

fof(f84,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f57])).

fof(f57,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t95_tops_1.p',cc4_tops_1)).

fof(f3313,plain,(
    ! [X17] :
      ( v3_tops_1(X17,sK0)
      | ~ v1_xboole_0(X17) ) ),
    inference(subsumption_resolution,[],[f237,f3278])).

fof(f237,plain,(
    ! [X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_xboole_0(X17)
      | v3_tops_1(X17,sK0) ) ),
    inference(subsumption_resolution,[],[f222,f148])).

fof(f222,plain,(
    ! [X17] :
      ( v3_tops_1(X17,sK0)
      | ~ v1_xboole_0(X17)
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f147,f174])).

fof(f174,plain,(
    ! [X0,X1] :
      ( v3_tops_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f56])).

fof(f56,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v3_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t95_tops_1.p',cc3_tops_1)).

fof(f3744,plain,(
    ~ v2_tops_1(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0) ),
    inference(subsumption_resolution,[],[f3743,f437])).

fof(f437,plain,(
    k1_xboole_0 != k1_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f436,f148])).

fof(f436,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f435,f361])).

fof(f361,plain,(
    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f307,f148])).

fof(f307,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f149,f193])).

fof(f193,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t95_tops_1.p',dt_k2_tops_1)).

fof(f435,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f375,f162])).

fof(f162,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f130])).

fof(f130,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f53])).

fof(f53,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t95_tops_1.p',t84_tops_1)).

fof(f375,plain,(
    ~ v2_tops_1(k2_tops_1(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f374,f147])).

fof(f374,plain,
    ( ~ v2_tops_1(k2_tops_1(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f373,f148])).

fof(f373,plain,
    ( ~ v2_tops_1(k2_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f372,f361])).

fof(f372,plain,
    ( ~ v2_tops_1(k2_tops_1(sK0,sK1),sK0)
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f370,f354])).

fof(f354,plain,(
    v4_pre_topc(k2_tops_1(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f353,f147])).

fof(f353,plain,
    ( v4_pre_topc(k2_tops_1(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f302,f148])).

fof(f302,plain,
    ( v4_pre_topc(k2_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f149,f188])).

fof(f188,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f59])).

fof(f59,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t95_tops_1.p',fc11_tops_1)).

fof(f370,plain,
    ( ~ v2_tops_1(k2_tops_1(sK0,sK1),sK0)
    | ~ v4_pre_topc(k2_tops_1(sK0,sK1),sK0)
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f151,f176])).

fof(f176,plain,(
    ! [X0,X1] :
      ( v3_tops_1(X1,X0)
      | ~ v2_tops_1(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f86])).

fof(f86,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f58])).

fof(f58,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_tops_1(X1,X0)
              & v4_pre_topc(X1,X0) )
           => v3_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t95_tops_1.p',cc5_tops_1)).

fof(f151,plain,(
    ~ v3_tops_1(k2_tops_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f129])).

fof(f3743,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,sK1))
    | ~ v2_tops_1(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0) ),
    inference(forward_demodulation,[],[f3685,f683])).

fof(f683,plain,(
    k1_tops_1(sK0,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f636,f148])).

fof(f636,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f361,f195])).

fof(f195,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t95_tops_1.p',projectivity_k1_tops_1)).

fof(f3685,plain,
    ( ~ v2_tops_1(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),sK0)
    | k1_xboole_0 = k1_tops_1(sK0,k1_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f682,f248])).

fof(f248,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tops_1(X3,sK0)
      | k1_xboole_0 = k1_tops_1(sK0,X3) ) ),
    inference(resolution,[],[f148,f161])).

fof(f161,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f130])).

fof(f682,plain,(
    m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f635,f148])).

fof(f635,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f361,f194])).

fof(f194,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t95_tops_1.p',dt_k1_tops_1)).

fof(f25876,plain,(
    ! [X5] :
      ( r2_hidden(X5,k2_pre_topc(sK0,sK1))
      | ~ r2_hidden(X5,k2_tops_1(sK0,sK1)) ) ),
    inference(resolution,[],[f9718,f199])).

fof(f199,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f141])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f139,f140])).

fof(f140,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f139,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t95_tops_1.p',d3_tarski)).

fof(f9718,plain,(
    r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) ),
    inference(superposition,[],[f180,f2051])).

fof(f2051,plain,(
    k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f2048,f1040])).

fof(f1040,plain,(
    m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f977,f148])).

fof(f977,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f312,f192])).

fof(f192,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t95_tops_1.p',dt_k2_pre_topc)).

fof(f312,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f149,f186])).

fof(f186,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t95_tops_1.p',dt_k3_subset_1)).

fof(f2048,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f324,f208])).

fof(f324,plain,(
    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f282,f148])).

fof(f282,plain,
    ( k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f149,f160])).

fof(f160,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t95_tops_1.p',d2_tops_1)).

fof(f180,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t95_tops_1.p',t17_xboole_1)).

fof(f25741,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tops_1(sK0,k2_tops_1(sK0,sK1)))
      | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f25740,f149])).

fof(f25740,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tops_1(sK0,k2_tops_1(sK0,sK1)))
      | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f25734,f361])).

fof(f25734,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,k1_tops_1(sK0,k2_tops_1(sK0,sK1)))
      | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f5697,f1558])).

fof(f1558,plain,(
    ! [X19,X20,X18] :
      ( ~ r1_xboole_0(X19,k1_tops_1(sK0,X18))
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X20,k1_tops_1(sK0,X18))
      | ~ r2_hidden(X20,k2_pre_topc(sK0,X19))
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f1557,f242])).

fof(f242,plain,(
    ! [X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(k1_tops_1(sK0,X23),sK0) ) ),
    inference(subsumption_resolution,[],[f227,f148])).

fof(f227,plain,(
    ! [X23] :
      ( v3_pre_topc(k1_tops_1(sK0,X23),sK0)
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f147,f189])).

fof(f189,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f62])).

fof(f62,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t95_tops_1.p',fc9_tops_1)).

fof(f1557,plain,(
    ! [X19,X20,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_xboole_0(X19,k1_tops_1(sK0,X18))
      | ~ r2_hidden(X20,k1_tops_1(sK0,X18))
      | ~ v3_pre_topc(k1_tops_1(sK0,X18),sK0)
      | ~ r2_hidden(X20,k2_pre_topc(sK0,X19))
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f1556,f1353])).

fof(f1353,plain,(
    ! [X70,X69] :
      ( ~ r2_hidden(X70,k2_pre_topc(sK0,X69))
      | m1_subset_1(X70,u1_struct_0(sK0))
      | ~ m1_subset_1(X69,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f268,f210])).

fof(f210,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f123])).

fof(f123,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f122])).

fof(f122,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t95_tops_1.p',t4_subset)).

fof(f268,plain,(
    ! [X39] :
      ( m1_subset_1(k2_pre_topc(sK0,X39),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f148,f192])).

fof(f1556,plain,(
    ! [X19,X20,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_xboole_0(X19,k1_tops_1(sK0,X18))
      | ~ r2_hidden(X20,k1_tops_1(sK0,X18))
      | ~ v3_pre_topc(k1_tops_1(sK0,X18),sK0)
      | ~ r2_hidden(X20,k2_pre_topc(sK0,X19))
      | ~ m1_subset_1(X20,u1_struct_0(sK0))
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f1555,f690])).

fof(f690,plain,(
    ~ v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f379,f685])).

fof(f685,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f638,f378])).

fof(f378,plain,(
    ~ v1_xboole_0(k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f377,f147])).

fof(f377,plain,
    ( ~ v1_xboole_0(k2_tops_1(sK0,sK1))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f376,f148])).

fof(f376,plain,
    ( ~ v1_xboole_0(k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f371,f361])).

fof(f371,plain,
    ( ~ v1_xboole_0(k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f151,f174])).

fof(f638,plain,
    ( v1_xboole_0(k2_tops_1(sK0,sK1))
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f361,f165])).

fof(f165,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f55])).

fof(f55,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t95_tops_1.p',cc1_subset_1)).

fof(f379,plain,
    ( ~ v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f244,f171])).

fof(f171,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f61])).

fof(f61,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t95_tops_1.p',fc1_struct_0)).

fof(f244,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f148,f157])).

fof(f157,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t95_tops_1.p',dt_l1_pre_topc)).

fof(f1555,plain,(
    ! [X19,X20,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_xboole_0(X19,k1_tops_1(sK0,X18))
      | ~ r2_hidden(X20,k1_tops_1(sK0,X18))
      | ~ v3_pre_topc(k1_tops_1(sK0,X18),sK0)
      | ~ r2_hidden(X20,k2_pre_topc(sK0,X19))
      | ~ m1_subset_1(X20,u1_struct_0(sK0))
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1554,f147])).

fof(f1554,plain,(
    ! [X19,X20,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_xboole_0(X19,k1_tops_1(sK0,X18))
      | ~ r2_hidden(X20,k1_tops_1(sK0,X18))
      | ~ v3_pre_topc(k1_tops_1(sK0,X18),sK0)
      | ~ r2_hidden(X20,k2_pre_topc(sK0,X19))
      | ~ m1_subset_1(X20,u1_struct_0(sK0))
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1504,f148])).

fof(f1504,plain,(
    ! [X19,X20,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_xboole_0(X19,k1_tops_1(sK0,X18))
      | ~ r2_hidden(X20,k1_tops_1(sK0,X18))
      | ~ v3_pre_topc(k1_tops_1(sK0,X18),sK0)
      | ~ r2_hidden(X20,k2_pre_topc(sK0,X19))
      | ~ m1_subset_1(X20,u1_struct_0(sK0))
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f270,f166])).

fof(f166,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X4)
      | ~ r2_hidden(X2,X4)
      | ~ v3_pre_topc(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f134])).

fof(f134,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ( r1_xboole_0(X1,sK2(X0,X1,X2))
                    & r2_hidden(X2,sK2(X0,X1,X2))
                    & v3_pre_topc(sK2(X0,X1,X2),X0)
                    & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( ~ r1_xboole_0(X1,X4)
                      | ~ r2_hidden(X2,X4)
                      | ~ v3_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f132,f133])).

fof(f133,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_xboole_0(X1,X3)
          & r2_hidden(X2,X3)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_xboole_0(X1,sK2(X0,X1,X2))
        & r2_hidden(X2,sK2(X0,X1,X2))
        & v3_pre_topc(sK2(X0,X1,X2),X0)
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f132,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( ~ r1_xboole_0(X1,X4)
                      | ~ r2_hidden(X2,X4)
                      | ~ v3_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f131])).

fof(f131,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( ~ r1_xboole_0(X1,X3)
                      | ~ r2_hidden(X2,X3)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( ~ r1_xboole_0(X1,X3)
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( ~ r1_xboole_0(X1,X3)
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ~ ( r1_xboole_0(X1,X3)
                        & r2_hidden(X2,X3)
                        & v3_pre_topc(X3,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t95_tops_1.p',t39_tops_1)).

fof(f270,plain,(
    ! [X41] :
      ( m1_subset_1(k1_tops_1(sK0,X41),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f148,f194])).

fof(f5697,plain,(
    r1_xboole_0(sK1,k1_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(trivial_inequality_removal,[],[f5695])).

fof(f5695,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK1,k1_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[],[f198,f5626])).

fof(f5626,plain,(
    k3_xboole_0(sK1,k1_tops_1(sK0,k2_tops_1(sK0,sK1))) = k1_xboole_0 ),
    inference(backward_demodulation,[],[f5620,f2107])).

fof(f2107,plain,(
    k3_xboole_0(sK1,k1_tops_1(sK0,k2_tops_1(sK0,sK1))) = k1_tops_1(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f2106,f1854])).

fof(f1854,plain,(
    k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_xboole_0 ),
    inference(backward_demodulation,[],[f1838,f476])).

fof(f476,plain,(
    k3_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k1_xboole_0 ),
    inference(resolution,[],[f323,f197])).

fof(f197,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t95_tops_1.p',d7_xboole_0)).

fof(f323,plain,(
    r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f281,f148])).

fof(f281,plain,
    ( r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f149,f159])).

fof(f159,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f51])).

fof(f51,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t95_tops_1.p',t73_tops_1)).

fof(f1838,plain,(
    k1_tops_1(sK0,sK1) = sK1 ),
    inference(subsumption_resolution,[],[f1837,f148])).

fof(f1837,plain,
    ( k1_tops_1(sK0,sK1) = sK1
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1820,f150])).

fof(f150,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f129])).

fof(f1820,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | k1_tops_1(sK0,sK1) = sK1
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f341,f149])).

fof(f341,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
      | ~ v3_pre_topc(X11,X10)
      | k1_tops_1(X10,X11) = X11
      | ~ l1_pre_topc(X10) ) ),
    inference(subsumption_resolution,[],[f340,f147])).

fof(f340,plain,(
    ! [X10,X11] :
      ( k1_tops_1(X10,X11) = X11
      | ~ v3_pre_topc(X11,X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
      | ~ l1_pre_topc(X10)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f293,f148])).

fof(f293,plain,(
    ! [X10,X11] :
      ( k1_tops_1(X10,X11) = X11
      | ~ v3_pre_topc(X11,X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
      | ~ l1_pre_topc(X10)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f149,f172])).

fof(f172,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f48])).

fof(f48,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t95_tops_1.p',t55_tops_1)).

fof(f2106,plain,(
    k3_xboole_0(sK1,k1_tops_1(sK0,k2_tops_1(sK0,sK1))) = k1_tops_1(sK0,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f2087,f181])).

fof(f2087,plain,(
    k3_xboole_0(sK1,k1_tops_1(sK0,k2_tops_1(sK0,sK1))) = k1_tops_1(sK0,k3_xboole_0(k2_tops_1(sK0,sK1),sK1)) ),
    inference(resolution,[],[f1928,f361])).

fof(f1928,plain,(
    ! [X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0)))
      | k3_xboole_0(sK1,k1_tops_1(sK0,X19)) = k1_tops_1(sK0,k3_xboole_0(X19,sK1)) ) ),
    inference(forward_demodulation,[],[f1888,f181])).

fof(f1888,plain,(
    ! [X19] :
      ( k3_xboole_0(k1_tops_1(sK0,X19),sK1) = k1_tops_1(sK0,k3_xboole_0(X19,sK1))
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(backward_demodulation,[],[f1838,f824])).

fof(f824,plain,(
    ! [X19] :
      ( k3_xboole_0(k1_tops_1(sK0,X19),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,k3_xboole_0(X19,sK1))
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(backward_demodulation,[],[f757,f366])).

fof(f366,plain,(
    ! [X19] :
      ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X19),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,k3_xboole_0(X19,sK1))
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(backward_demodulation,[],[f317,f352])).

fof(f352,plain,(
    ! [X19] :
      ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X19),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X19,sK1))
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f351,f147])).

fof(f351,plain,(
    ! [X19] :
      ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X19),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X19,sK1))
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f301,f148])).

fof(f301,plain,(
    ! [X19] :
      ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X19),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X19,sK1))
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f149,f177])).

fof(f177,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f88])).

fof(f88,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f44])).

fof(f44,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t95_tops_1.p',t46_tops_1)).

fof(f757,plain,(
    ! [X22] : k3_xboole_0(X22,k1_tops_1(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),X22,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f362,f208])).

fof(f362,plain,(
    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f308,f148])).

fof(f308,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f149,f194])).

fof(f5620,plain,(
    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f3225,f5615])).

fof(f5615,plain,(
    v2_tops_1(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f3218,f5613])).

fof(f5613,plain,(
    v3_tops_1(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f3217,f5612])).

fof(f5612,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f5552,f152])).

fof(f152,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t95_tops_1.p',dt_o_0_0_xboole_0)).

fof(f5552,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(global_subsumption,[],[f1649,f3225,f3327,f3675,f5534])).

fof(f5534,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[],[f5495,f1854])).

fof(f5495,plain,(
    ! [X1] :
      ( k1_xboole_0 != k1_tops_1(sK0,k3_xboole_0(sK1,X1))
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[],[f5490,f181])).

fof(f5490,plain,(
    ! [X2] :
      ( k1_xboole_0 != k1_tops_1(sK0,k3_xboole_0(X2,sK1))
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(inner_rewriting,[],[f5489])).

fof(f5489,plain,(
    ! [X2] :
      ( v1_xboole_0(k1_tops_1(sK0,k3_xboole_0(X2,sK1)))
      | k1_xboole_0 != k1_tops_1(sK0,k3_xboole_0(X2,sK1)) ) ),
    inference(subsumption_resolution,[],[f5488,f148])).

fof(f5488,plain,(
    ! [X2] :
      ( v1_xboole_0(k1_tops_1(sK0,k3_xboole_0(X2,sK1)))
      | k1_xboole_0 != k1_tops_1(sK0,k3_xboole_0(X2,sK1))
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f5480,f365])).

fof(f5480,plain,(
    ! [X2] :
      ( v1_xboole_0(k1_tops_1(sK0,k3_xboole_0(X2,sK1)))
      | k1_xboole_0 != k1_tops_1(sK0,k3_xboole_0(X2,sK1))
      | ~ m1_subset_1(k3_xboole_0(X2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f941,f162])).

fof(f941,plain,(
    ! [X43] :
      ( ~ v2_tops_1(k3_xboole_0(X43,sK1),sK0)
      | v1_xboole_0(k1_tops_1(sK0,k3_xboole_0(X43,sK1))) ) ),
    inference(subsumption_resolution,[],[f875,f148])).

fof(f875,plain,(
    ! [X43] :
      ( v1_xboole_0(k1_tops_1(sK0,k3_xboole_0(X43,sK1)))
      | ~ v2_tops_1(k3_xboole_0(X43,sK1),sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f365,f191])).

fof(f191,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f60])).

fof(f60,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v2_tops_1(X1,X0)
        & l1_pre_topc(X0) )
     => v1_xboole_0(k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t95_tops_1.p',fc13_tops_1)).

fof(f3675,plain,(
    ! [X0] :
      ( r1_tarski(X0,u1_struct_0(sK0))
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f3270,f164])).

fof(f3270,plain,(
    r1_tarski(k1_xboole_0,u1_struct_0(sK0)) ),
    inference(resolution,[],[f2728,f202])).

fof(f202,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t95_tops_1.p',t3_subset)).

fof(f1649,plain,(
    ! [X12] :
      ( ~ r1_tarski(X12,u1_struct_0(sK0))
      | ~ v2_tops_1(X12,sK0)
      | v2_tops_1(k1_xboole_0,sK0) ) ),
    inference(resolution,[],[f1632,f203])).

fof(f203,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f142])).

fof(f1632,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tops_1(k1_xboole_0,sK0)
      | ~ v2_tops_1(X3,sK0) ) ),
    inference(subsumption_resolution,[],[f1629,f148])).

fof(f1629,plain,(
    ! [X3] :
      ( v2_tops_1(k1_xboole_0,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tops_1(X3,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(trivial_inequality_removal,[],[f1628])).

fof(f1628,plain,(
    ! [X3] :
      ( k1_xboole_0 != k1_xboole_0
      | v2_tops_1(k1_xboole_0,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tops_1(X3,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(duplicate_literal_removal,[],[f1626])).

fof(f1626,plain,(
    ! [X3] :
      ( k1_xboole_0 != k1_xboole_0
      | v2_tops_1(k1_xboole_0,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tops_1(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f1623,f161])).

fof(f1623,plain,(
    ! [X4] :
      ( k1_xboole_0 != k1_tops_1(sK0,X4)
      | v2_tops_1(k1_xboole_0,sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(inner_rewriting,[],[f1622])).

fof(f1622,plain,(
    ! [X4] :
      ( k1_xboole_0 != k1_tops_1(sK0,X4)
      | v2_tops_1(k1_tops_1(sK0,X4),sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f1621,f270])).

fof(f1621,plain,(
    ! [X4] :
      ( k1_xboole_0 != k1_tops_1(sK0,X4)
      | v2_tops_1(k1_tops_1(sK0,X4),sK0)
      | ~ m1_subset_1(k1_tops_1(sK0,X4),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f1615,f148])).

fof(f1615,plain,(
    ! [X4] :
      ( k1_xboole_0 != k1_tops_1(sK0,X4)
      | v2_tops_1(k1_tops_1(sK0,X4),sK0)
      | ~ m1_subset_1(k1_tops_1(sK0,X4),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f249,f195])).

fof(f249,plain,(
    ! [X4] :
      ( k1_xboole_0 != k1_tops_1(sK0,X4)
      | v2_tops_1(X4,sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f148,f162])).

fof(f3217,plain,
    ( v3_tops_1(k1_xboole_0,sK0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f2728,f237])).

fof(f3218,plain,
    ( ~ v3_tops_1(k1_xboole_0,sK0)
    | v2_tops_1(k1_xboole_0,sK0) ),
    inference(resolution,[],[f2728,f238])).

fof(f238,plain,(
    ! [X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_tops_1(X18,sK0)
      | v2_tops_1(X18,sK0) ) ),
    inference(subsumption_resolution,[],[f223,f148])).

fof(f223,plain,(
    ! [X18] :
      ( v2_tops_1(X18,sK0)
      | ~ v3_tops_1(X18,sK0)
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f147,f175])).

fof(f3225,plain,
    ( ~ v2_tops_1(k1_xboole_0,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) ),
    inference(resolution,[],[f2728,f248])).

fof(f198,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f137])).

fof(f3454,plain,(
    ! [X2] :
      ( r2_hidden(X2,k2_tops_1(sK0,sK1))
      | ~ r2_hidden(X2,k1_tops_1(sK0,k2_tops_1(sK0,sK1))) ) ),
    inference(resolution,[],[f649,f199])).

fof(f649,plain,(
    r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f607,f148])).

fof(f607,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f361,f158])).

fof(f158,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t95_tops_1.p',t44_tops_1)).

fof(f358,plain,(
    m1_subset_1(o_2_2_tops_1(sK0,sK1),k1_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f357,f147])).

fof(f357,plain,
    ( m1_subset_1(o_2_2_tops_1(sK0,sK1),k1_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f304,f148])).

fof(f304,plain,
    ( m1_subset_1(o_2_2_tops_1(sK0,sK1),k1_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f149,f190])).

fof(f190,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_2_tops_1(X0,X1),k1_tops_1(X0,k2_tops_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_2_tops_1(X0,X1),k1_tops_1(X0,k2_tops_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_2_tops_1(X0,X1),k1_tops_1(X0,k2_tops_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => m1_subset_1(o_2_2_tops_1(X0,X1),k1_tops_1(X0,k2_tops_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t95_tops_1.p',dt_o_2_2_tops_1)).
%------------------------------------------------------------------------------
