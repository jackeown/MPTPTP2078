%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_1__t74_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:31 EDT 2019

% Result     : Theorem 74.24s
% Output     : Refutation 74.24s
% Verified   : 
% Statistics : Number of formulae       :  175 (2795 expanded)
%              Number of leaves         :   27 ( 874 expanded)
%              Depth                    :   32
%              Number of atoms          :  318 (6694 expanded)
%              Number of equality atoms :  106 (1934 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f33329,plain,(
    $false ),
    inference(subsumption_resolution,[],[f33328,f242])).

fof(f242,plain,(
    k1_tops_1(sK0,sK1) != k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f241,f124])).

fof(f124,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f113])).

fof(f113,plain,
    ( k1_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f64,f112,f111])).

fof(f111,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( k1_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k2_tops_1(sK0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f112,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k1_tops_1(X0,sK1) != k7_subset_1(u1_struct_0(X0),sK1,k2_tops_1(X0,sK1))
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t74_tops_1.p',t74_tops_1)).

fof(f241,plain,
    ( k1_tops_1(sK0,sK1) != k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f125,f169])).

fof(f169,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f97,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t74_tops_1.p',redefinition_k7_subset_1)).

fof(f125,plain,(
    k1_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f113])).

fof(f33328,plain,(
    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f33220,f3257])).

fof(f3257,plain,(
    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f3256,f1416])).

fof(f1416,plain,(
    k1_tops_1(sK0,sK1) = k3_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f251,f140])).

fof(f140,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t74_tops_1.p',commutativity_k3_xboole_0)).

fof(f251,plain,(
    k1_tops_1(sK0,sK1) = k3_xboole_0(k1_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f227,f145])).

fof(f145,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f46])).

fof(f46,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t74_tops_1.p',t28_xboole_1)).

fof(f227,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f192,f123])).

fof(f123,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f113])).

fof(f192,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f124,f134])).

fof(f134,plain,(
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
    inference(ennf_transformation,[],[f53])).

fof(f53,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t74_tops_1.p',t44_tops_1)).

fof(f3256,plain,(
    k3_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k4_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f3215,f369])).

fof(f369,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f231,f148])).

fof(f148,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t74_tops_1.p',involutiveness_k3_subset_1)).

fof(f231,plain,(
    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f196,f123])).

fof(f196,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f124,f154])).

fof(f154,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t74_tops_1.p',dt_k1_tops_1)).

fof(f3215,plain,(
    k3_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))) = k4_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f368,f240])).

fof(f240,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k3_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),X0)) = k4_xboole_0(sK1,X0) ) ),
    inference(forward_demodulation,[],[f239,f140])).

fof(f239,plain,(
    ! [X0] :
      ( k3_xboole_0(k3_subset_1(u1_struct_0(sK0),X0),sK1) = k4_xboole_0(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(backward_demodulation,[],[f238,f236])).

fof(f236,plain,(
    ! [X0] :
      ( k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),X0)) = k4_xboole_0(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(backward_demodulation,[],[f213,f203])).

fof(f203,plain,(
    ! [X0] :
      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f124,f150])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f49])).

fof(f49,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t74_tops_1.p',t32_subset_1)).

fof(f213,plain,(
    ! [X9] : k7_subset_1(u1_struct_0(sK0),sK1,X9) = k4_xboole_0(sK1,X9) ),
    inference(resolution,[],[f124,f169])).

fof(f238,plain,(
    ! [X11] : k3_xboole_0(X11,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X11) ),
    inference(forward_demodulation,[],[f215,f214])).

fof(f214,plain,(
    ! [X10] : k3_xboole_0(X10,sK1) = k9_subset_1(u1_struct_0(sK0),X10,sK1) ),
    inference(resolution,[],[f124,f170])).

fof(f170,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f98,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t74_tops_1.p',redefinition_k9_subset_1)).

fof(f215,plain,(
    ! [X11] : k9_subset_1(u1_struct_0(sK0),X11,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X11) ),
    inference(resolution,[],[f124,f171])).

fof(f171,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f99])).

fof(f99,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t74_tops_1.p',commutativity_k9_subset_1)).

fof(f368,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f231,f147])).

fof(f147,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t74_tops_1.p',dt_k3_subset_1)).

fof(f33220,plain,(
    k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) ),
    inference(superposition,[],[f14001,f1131])).

fof(f1131,plain,(
    k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f1125,f368])).

fof(f1125,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f842,f170])).

fof(f842,plain,(
    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f840,f229])).

fof(f229,plain,(
    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f194,f123])).

fof(f194,plain,
    ( k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f124,f136])).

fof(f136,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t74_tops_1.p',d2_tops_1)).

fof(f840,plain,(
    k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f829,f649])).

fof(f649,plain,(
    m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f604,f123])).

fof(f604,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f200,f153])).

fof(f153,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t74_tops_1.p',dt_k2_pre_topc)).

fof(f200,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f124,f147])).

fof(f829,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f148,f228])).

fof(f228,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f193,f123])).

fof(f193,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f124,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t74_tops_1.p',d1_tops_1)).

fof(f14001,plain,(
    ! [X1] : k4_xboole_0(sK1,X1) = k4_xboole_0(sK1,k3_xboole_0(k2_pre_topc(sK0,sK1),X1)) ),
    inference(backward_demodulation,[],[f13998,f1392])).

fof(f1392,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,X1)) = k4_xboole_0(sK1,k3_xboole_0(k2_pre_topc(sK0,sK1),X1)) ),
    inference(superposition,[],[f165,f1387])).

fof(f1387,plain,(
    k4_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = k1_xboole_0 ),
    inference(backward_demodulation,[],[f1385,f1087])).

fof(f1087,plain,(
    k3_xboole_0(sK1,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k4_xboole_0(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1076,f638])).

fof(f638,plain,(
    k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) ),
    inference(forward_demodulation,[],[f637,f201])).

fof(f201,plain,(
    k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
    inference(resolution,[],[f124,f148])).

fof(f637,plain,(
    k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) ),
    inference(subsumption_resolution,[],[f602,f123])).

fof(f602,plain,
    ( k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f200,f135])).

fof(f1076,plain,(
    k3_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k4_xboole_0(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f240,f230])).

fof(f230,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f195,f123])).

fof(f195,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f124,f153])).

fof(f1385,plain,(
    k3_xboole_0(sK1,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k1_xboole_0 ),
    inference(resolution,[],[f904,f158])).

fof(f158,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t74_tops_1.p',d7_xboole_0)).

fof(f904,plain,(
    r1_xboole_0(sK1,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(forward_demodulation,[],[f903,f638])).

fof(f903,plain,(
    r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f894,f230])).

fof(f894,plain,
    ( r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f207,f226])).

fof(f226,plain,(
    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f191,f123])).

fof(f191,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f124,f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f54])).

fof(f54,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t74_tops_1.p',t48_pre_topc)).

fof(f207,plain,(
    ! [X4] :
      ( ~ r1_tarski(sK1,X4)
      | r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f124,f152])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k3_subset_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(X1,X2)
              | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f52])).

fof(f52,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t74_tops_1.p',t44_subset_1)).

fof(f165,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t74_tops_1.p',t54_xboole_1)).

fof(f13998,plain,(
    ! [X7] : k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,X7)) = k4_xboole_0(sK1,X7) ),
    inference(backward_demodulation,[],[f13977,f13973])).

fof(f13973,plain,(
    ! [X7] : k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,X7)) = k3_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k3_xboole_0(sK1,X7))) ),
    inference(backward_demodulation,[],[f13936,f1255])).

fof(f1255,plain,(
    ! [X7] : k3_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k3_xboole_0(sK1,X7))) = k4_xboole_0(sK1,k3_xboole_0(sK1,X7)) ),
    inference(resolution,[],[f584,f240])).

fof(f584,plain,(
    ! [X2] : m1_subset_1(k3_xboole_0(sK1,X2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f237,f140])).

fof(f237,plain,(
    ! [X8] : m1_subset_1(k3_xboole_0(X8,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f214,f212])).

fof(f212,plain,(
    ! [X8] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X8,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f124,f168])).

fof(f168,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t74_tops_1.p',dt_k9_subset_1)).

fof(f13936,plain,(
    ! [X17] : k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,X17)) = k4_xboole_0(sK1,k3_xboole_0(sK1,X17)) ),
    inference(superposition,[],[f165,f13215])).

fof(f13215,plain,(
    k4_xboole_0(sK1,sK1) = k1_xboole_0 ),
    inference(forward_demodulation,[],[f13185,f12808])).

fof(f12808,plain,(
    k3_subset_1(sK1,sK1) = k1_xboole_0 ),
    inference(backward_demodulation,[],[f12807,f12781])).

fof(f12781,plain,(
    k3_subset_1(sK1,k3_subset_1(sK1,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[],[f12594,f148])).

fof(f12594,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) ),
    inference(subsumption_resolution,[],[f12589,f915])).

fof(f915,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f884,f161])).

fof(f161,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f51,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t74_tops_1.p',t3_subset)).

fof(f884,plain,(
    r1_tarski(k1_xboole_0,u1_struct_0(sK0)) ),
    inference(superposition,[],[f779,f130])).

fof(f130,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t74_tops_1.p',t2_boole)).

fof(f779,plain,(
    ! [X2] : r1_tarski(k3_xboole_0(sK1,X2),u1_struct_0(sK0)) ),
    inference(superposition,[],[f564,f140])).

fof(f564,plain,(
    ! [X24] : r1_tarski(k3_xboole_0(X24,sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f237,f160])).

fof(f160,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f118])).

fof(f12589,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f12524,f890])).

fof(f890,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,k3_subset_1(u1_struct_0(sK0),sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(X0,k1_zfmisc_1(sK1)) ) ),
    inference(resolution,[],[f206,f161])).

fof(f206,plain,(
    ! [X3] :
      ( r1_tarski(X3,sK1)
      | ~ r1_xboole_0(X3,k3_subset_1(u1_struct_0(sK0),sK1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f124,f151])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_xboole_0(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f116])).

fof(f12524,plain,(
    r1_xboole_0(k1_xboole_0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f12376,f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t74_tops_1.p',symmetry_r1_xboole_0)).

fof(f12376,plain,(
    r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f12375,f1029])).

fof(f1029,plain,(
    k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) = k1_xboole_0 ),
    inference(backward_demodulation,[],[f1028,f996])).

fof(f996,plain,(
    k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[],[f915,f148])).

fof(f1028,plain,(
    u1_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f997,f128])).

fof(f128,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f50])).

fof(f50,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t74_tops_1.p',t3_boole)).

fof(f997,plain,(
    k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k4_xboole_0(u1_struct_0(sK0),k1_xboole_0) ),
    inference(resolution,[],[f915,f149])).

fof(f149,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t74_tops_1.p',d5_subset_1)).

fof(f12375,plain,(
    r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f12361,f1030])).

fof(f1030,plain,(
    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f1028,f995])).

fof(f995,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f915,f147])).

fof(f12361,plain,
    ( r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f616,f618])).

fof(f618,plain,(
    r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f200,f160])).

fof(f616,plain,(
    ! [X4] :
      ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),X4)
      | r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f200,f152])).

fof(f12807,plain,(
    k3_subset_1(sK1,k1_xboole_0) = sK1 ),
    inference(forward_demodulation,[],[f12782,f128])).

fof(f12782,plain,(
    k3_subset_1(sK1,k1_xboole_0) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(resolution,[],[f12594,f149])).

fof(f13185,plain,(
    k3_subset_1(sK1,sK1) = k4_xboole_0(sK1,sK1) ),
    inference(resolution,[],[f12809,f149])).

fof(f12809,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    inference(backward_demodulation,[],[f12807,f12780])).

fof(f12780,plain,(
    m1_subset_1(k3_subset_1(sK1,k1_xboole_0),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f12594,f147])).

fof(f13977,plain,(
    ! [X2] : k3_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k3_xboole_0(sK1,X2))) = k4_xboole_0(sK1,X2) ),
    inference(superposition,[],[f13964,f140])).

fof(f13964,plain,(
    ! [X8] : k3_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k3_xboole_0(X8,sK1))) = k4_xboole_0(sK1,X8) ),
    inference(backward_demodulation,[],[f13963,f1070])).

fof(f1070,plain,(
    ! [X8] : k3_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k3_xboole_0(X8,sK1))) = k4_xboole_0(sK1,k3_xboole_0(X8,sK1)) ),
    inference(resolution,[],[f240,f237])).

fof(f13963,plain,(
    ! [X16] : k4_xboole_0(sK1,X16) = k4_xboole_0(sK1,k3_xboole_0(X16,sK1)) ),
    inference(forward_demodulation,[],[f13935,f127])).

fof(f127,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t74_tops_1.p',t1_boole)).

fof(f13935,plain,(
    ! [X16] : k2_xboole_0(k4_xboole_0(sK1,X16),k1_xboole_0) = k4_xboole_0(sK1,k3_xboole_0(X16,sK1)) ),
    inference(superposition,[],[f165,f13215])).
%------------------------------------------------------------------------------
