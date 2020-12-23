%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_1__t32_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:28 EDT 2019

% Result     : Theorem 115.14s
% Output     : Refutation 115.18s
% Verified   : 
% Statistics : Number of formulae       :  144 (1248 expanded)
%              Number of leaves         :   18 ( 437 expanded)
%              Depth                    :   21
%              Number of atoms          :  438 (5421 expanded)
%              Number of equality atoms :   95 ( 265 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f170547,plain,(
    $false ),
    inference(global_subsumption,[],[f123256,f170540])).

fof(f170540,plain,(
    r2_hidden(sK3(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))),k2_pre_topc(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(superposition,[],[f6024,f4797])).

fof(f4797,plain,(
    k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f4796,f198])).

fof(f198,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f178,f93])).

fof(f93,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f43,f71,f70,f69])).

fof(f69,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),sK1,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,sK2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,sK2)))
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
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
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t32_tops_1.p',t32_tops_1)).

fof(f178,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f95,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t32_tops_1.p',dt_k2_pre_topc)).

fof(f95,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f72])).

fof(f4796,plain,
    ( k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f4784,f171])).

fof(f171,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f151,f93])).

fof(f151,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f94,f105])).

fof(f94,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f72])).

fof(f4784,plain,
    ( k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f1123,f131])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t32_tops_1.p',redefinition_k4_subset_1)).

fof(f1123,plain,(
    k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1122,f1092])).

fof(f1092,plain,(
    k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)) = k2_pre_topc(sK0,k2_xboole_0(sK1,k2_pre_topc(sK0,sK2))) ),
    inference(forward_demodulation,[],[f1091,f545])).

fof(f545,plain,(
    k2_xboole_0(sK1,sK2) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) ),
    inference(resolution,[],[f159,f95])).

fof(f159,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_xboole_0(sK1,X7) = k4_subset_1(u1_struct_0(sK0),sK1,X7) ) ),
    inference(resolution,[],[f94,f131])).

fof(f1091,plain,(
    k2_pre_topc(sK0,k2_xboole_0(sK1,k2_pre_topc(sK0,sK2))) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(forward_demodulation,[],[f1072,f1081])).

fof(f1081,plain,(
    k2_pre_topc(sK0,k2_xboole_0(sK1,k2_pre_topc(sK0,sK2))) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) ),
    inference(forward_demodulation,[],[f1080,f539])).

fof(f539,plain,(
    k2_xboole_0(sK1,k2_pre_topc(sK0,sK2)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)) ),
    inference(resolution,[],[f159,f198])).

fof(f1080,plain,(
    k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2))) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) ),
    inference(forward_demodulation,[],[f1063,f199])).

fof(f199,plain,(
    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f179,f93])).

fof(f179,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f95,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t32_tops_1.p',projectivity_k2_pre_topc)).

fof(f1063,plain,(
    k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2))) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_pre_topc(sK0,sK2))) ),
    inference(resolution,[],[f168,f198])).

fof(f168,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X0)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f167,f92])).

fof(f92,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f72])).

fof(f167,plain,(
    ! [X0] :
      ( k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X0)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f149,f93])).

fof(f149,plain,(
    ! [X0] :
      ( k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X0)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f94,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t32_tops_1.p',t50_pre_topc)).

fof(f1072,plain,(
    k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) ),
    inference(resolution,[],[f168,f95])).

fof(f1122,plain,(
    k2_pre_topc(sK0,k2_xboole_0(sK1,k2_pre_topc(sK0,sK2))) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1121,f861])).

fof(f861,plain,(
    k2_xboole_0(sK1,k2_pre_topc(sK0,sK2)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),sK1) ),
    inference(forward_demodulation,[],[f844,f539])).

fof(f844,plain,(
    k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)) ),
    inference(resolution,[],[f157,f198])).

fof(f157,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_subset_1(u1_struct_0(sK0),X5,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,X5) ) ),
    inference(resolution,[],[f94,f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t32_tops_1.p',commutativity_k4_subset_1)).

fof(f1121,plain,(
    k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),sK1)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1104,f199])).

fof(f1104,plain,(
    k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),sK1)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f170,f198])).

fof(f170,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X1,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f169,f92])).

fof(f169,plain,(
    ! [X1] :
      ( k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X1,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f150,f93])).

fof(f150,plain,(
    ! [X1] :
      ( k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X1,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f94,f109])).

fof(f6024,plain,(
    ! [X2] : r2_hidden(sK3(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))),k2_xboole_0(X2,k2_pre_topc(sK0,sK1))) ),
    inference(resolution,[],[f1035,f134])).

fof(f134,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f113])).

fof(f113,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
              & ~ r2_hidden(sK6(X0,X1,X2),X0) )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( r2_hidden(sK6(X0,X1,X2),X1)
            | r2_hidden(sK6(X0,X1,X2),X0)
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f84,f85])).

fof(f85,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
            & ~ r2_hidden(sK6(X0,X1,X2),X0) )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( r2_hidden(sK6(X0,X1,X2),X1)
          | r2_hidden(sK6(X0,X1,X2),X0)
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f83])).

fof(f83,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f82])).

fof(f82,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t32_tops_1.p',d3_xboole_0)).

fof(f1035,plain,(
    r2_hidden(sK3(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))),k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f262,f139])).

fof(f139,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f121])).

fof(f121,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK7(X0,X1,X2),X1)
            | ~ r2_hidden(sK7(X0,X1,X2),X0)
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
              & r2_hidden(sK7(X0,X1,X2),X0) )
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f89,f90])).

fof(f90,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK7(X0,X1,X2),X1)
          | ~ r2_hidden(sK7(X0,X1,X2),X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
            & r2_hidden(sK7(X0,X1,X2),X0) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f89,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f88])).

fof(f88,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f87])).

fof(f87,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t32_tops_1.p',d5_xboole_0)).

fof(f262,plain,(
    r2_hidden(sK3(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
    inference(backward_demodulation,[],[f238,f203])).

fof(f203,plain,(
    r2_hidden(sK3(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))),k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
    inference(resolution,[],[f173,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f75,f76])).

fof(f76,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t32_tops_1.p',d3_tarski)).

fof(f173,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(backward_demodulation,[],[f154,f96])).

fof(f96,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f72])).

fof(f154,plain,(
    ! [X2] : k7_subset_1(u1_struct_0(sK0),sK1,X2) = k4_xboole_0(sK1,X2) ),
    inference(resolution,[],[f94,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t32_tops_1.p',redefinition_k7_subset_1)).

fof(f238,plain,(
    ! [X2] : k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X2) = k4_xboole_0(k2_pre_topc(sK0,sK1),X2) ),
    inference(resolution,[],[f171,f102])).

fof(f123256,plain,(
    ~ r2_hidden(sK3(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))),k2_pre_topc(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f123255,f880])).

fof(f880,plain,(
    k2_xboole_0(sK1,sK2) = k2_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f879,f545])).

fof(f879,plain,(
    k2_xboole_0(sK2,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) ),
    inference(forward_demodulation,[],[f853,f562])).

fof(f562,plain,(
    k2_xboole_0(sK2,sK1) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) ),
    inference(resolution,[],[f160,f95])).

fof(f160,plain,(
    ! [X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_xboole_0(X8,sK1) = k4_subset_1(u1_struct_0(sK0),X8,sK1) ) ),
    inference(resolution,[],[f94,f131])).

fof(f853,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) ),
    inference(resolution,[],[f157,f95])).

fof(f123255,plain,(
    ~ r2_hidden(sK3(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))),k2_pre_topc(sK0,k2_xboole_0(sK2,sK1))) ),
    inference(forward_demodulation,[],[f123254,f127])).

fof(f127,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t32_tops_1.p',t39_xboole_1)).

fof(f123254,plain,(
    ~ r2_hidden(sK3(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))),k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) ),
    inference(subsumption_resolution,[],[f123233,f1036])).

fof(f1036,plain,(
    ~ r2_hidden(sK3(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))),k2_pre_topc(sK0,sK2)) ),
    inference(resolution,[],[f262,f138])).

fof(f138,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f122])).

fof(f122,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f91])).

fof(f123233,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))),k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))))
    | r2_hidden(sK3(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))),k2_pre_topc(sK0,sK2)) ),
    inference(superposition,[],[f971,f6922])).

fof(f6922,plain,(
    ! [X2] : k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,X2))) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X2))) ),
    inference(forward_demodulation,[],[f6886,f1168])).

fof(f1168,plain,(
    ! [X2] : k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,X2))) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X2))) ),
    inference(backward_demodulation,[],[f1167,f1164])).

fof(f1164,plain,(
    ! [X2] : k2_pre_topc(sK0,k2_xboole_0(sK2,k2_pre_topc(sK0,k4_xboole_0(sK1,X2)))) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X2))) ),
    inference(forward_demodulation,[],[f1163,f987])).

fof(f987,plain,(
    ! [X8] : k2_xboole_0(sK2,k2_pre_topc(sK0,k4_xboole_0(sK1,X8))) = k4_subset_1(u1_struct_0(sK0),sK2,k2_pre_topc(sK0,k4_xboole_0(sK1,X8))) ),
    inference(resolution,[],[f298,f186])).

fof(f186,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_xboole_0(sK2,X7) = k4_subset_1(u1_struct_0(sK0),sK2,X7) ) ),
    inference(resolution,[],[f95,f131])).

fof(f298,plain,(
    ! [X4] : m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(sK1,X4)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f274,f93])).

fof(f274,plain,(
    ! [X4] :
      ( m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(sK1,X4)),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f174,f105])).

fof(f174,plain,(
    ! [X3] : m1_subset_1(k4_xboole_0(sK1,X3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f155,f154])).

fof(f155,plain,(
    ! [X3] : m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,X3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f94,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t32_tops_1.p',dt_k7_subset_1)).

fof(f1163,plain,(
    ! [X2] : k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,k2_pre_topc(sK0,k4_xboole_0(sK1,X2)))) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X2))) ),
    inference(forward_demodulation,[],[f1144,f299])).

fof(f299,plain,(
    ! [X5] : k2_pre_topc(sK0,k4_xboole_0(sK1,X5)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k4_xboole_0(sK1,X5))) ),
    inference(subsumption_resolution,[],[f275,f93])).

fof(f275,plain,(
    ! [X5] :
      ( k2_pre_topc(sK0,k4_xboole_0(sK1,X5)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k4_xboole_0(sK1,X5)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f174,f104])).

fof(f1144,plain,(
    ! [X2] : k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,k2_pre_topc(sK0,k4_xboole_0(sK1,X2)))) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k2_pre_topc(sK0,k4_xboole_0(sK1,X2)))) ),
    inference(resolution,[],[f195,f298])).

fof(f195,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,X0)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f194,f92])).

fof(f194,plain,(
    ! [X0] :
      ( k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,X0)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f176,f93])).

fof(f176,plain,(
    ! [X0] :
      ( k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,X0)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f95,f109])).

fof(f1167,plain,(
    ! [X7] : k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,X7))) = k2_pre_topc(sK0,k2_xboole_0(sK2,k2_pre_topc(sK0,k4_xboole_0(sK1,X7)))) ),
    inference(forward_demodulation,[],[f1166,f671])).

fof(f671,plain,(
    ! [X6] : k2_xboole_0(sK2,k4_xboole_0(sK1,X6)) = k4_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(sK1,X6)) ),
    inference(resolution,[],[f186,f174])).

fof(f1166,plain,(
    ! [X7] : k2_pre_topc(sK0,k2_xboole_0(sK2,k2_pre_topc(sK0,k4_xboole_0(sK1,X7)))) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(sK1,X7))) ),
    inference(forward_demodulation,[],[f1148,f1164])).

fof(f1148,plain,(
    ! [X7] : k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(sK1,X7))) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X7))) ),
    inference(resolution,[],[f195,f174])).

fof(f6886,plain,(
    ! [X2] : k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X2))) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X2))) ),
    inference(resolution,[],[f351,f298])).

fof(f351,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_xboole_0(k2_pre_topc(sK0,sK2),X7) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),X7) ) ),
    inference(resolution,[],[f198,f131])).

fof(f971,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK3(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))),k2_xboole_0(X3,k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))))
      | r2_hidden(sK3(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))),X3) ) ),
    inference(resolution,[],[f263,f136])).

fof(f136,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f86])).

fof(f263,plain,(
    ~ r2_hidden(sK3(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(backward_demodulation,[],[f238,f204])).

fof(f204,plain,(
    ~ r2_hidden(sK3(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f173,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f77])).
%------------------------------------------------------------------------------
