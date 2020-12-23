%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 193 expanded)
%              Number of leaves         :   10 (  69 expanded)
%              Depth                    :   18
%              Number of atoms          :  163 ( 999 expanded)
%              Number of equality atoms :    6 (  22 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f127,plain,(
    $false ),
    inference(global_subsumption,[],[f22,f126])).

fof(f126,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f125,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f125,plain,(
    ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(global_subsumption,[],[f23,f107,f121])).

fof(f121,plain,
    ( ~ v2_tex_2(sK2,sK0)
    | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f100,f32])).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f26,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f100,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2)
    | ~ v2_tex_2(sK2,sK0)
    | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f95,f22])).

fof(f95,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(k3_xboole_0(sK1,sK2),X0)
      | ~ v2_tex_2(X0,sK0)
      | ~ r1_tarski(sK2,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f87,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X1,X0),X2)
      | ~ r1_tarski(X0,X2) ) ),
    inference(superposition,[],[f30,f27])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f87,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(k3_xboole_0(sK1,sK2),u1_struct_0(sK0))
      | ~ r1_tarski(k3_xboole_0(sK1,sK2),X0)
      | ~ v2_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f82,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f82,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | ~ r1_tarski(k3_xboole_0(sK1,sK2),X0) ) ),
    inference(global_subsumption,[],[f20,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(k3_xboole_0(sK1,sK2),X0)
      | ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f80,f41])).

fof(f41,plain,(
    ! [X1] : k9_subset_1(u1_struct_0(sK0),X1,sK2) = k3_xboole_0(X1,sK2) ),
    inference(resolution,[],[f31,f22])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f80,plain,(
    ! [X0] :
      ( ~ r1_tarski(k3_xboole_0(sK1,sK2),X0)
      | ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f78,f41])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK0)
      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f25,f24])).

fof(f24,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & ( v2_tex_2(sK2,sK0)
      | v2_tex_2(sK1,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f17,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & ( v2_tex_2(X2,sK0)
                | v2_tex_2(X1,sK0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
            & ( v2_tex_2(X2,sK0)
              | v2_tex_2(X1,sK0) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
          & ( v2_tex_2(X2,sK0)
            | v2_tex_2(sK1,sK0) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
        & ( v2_tex_2(X2,sK0)
          | v2_tex_2(sK1,sK0) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      & ( v2_tex_2(sK2,sK0)
        | v2_tex_2(sK1,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    | v2_tex_2(X1,X0) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
               => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tex_2)).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X1,X0)
                  & r1_tarski(X2,X1) )
               => v2_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).

fof(f20,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f107,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(global_subsumption,[],[f22,f106])).

fof(f106,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f102,f28])).

fof(f102,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(resolution,[],[f99,f26])).

fof(f99,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
    | ~ v2_tex_2(sK1,sK0)
    | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f95,f21])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f23,plain,
    ( v2_tex_2(sK2,sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f22,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:48:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.36  ipcrm: permission denied for id (730038273)
% 0.12/0.36  ipcrm: permission denied for id (734330882)
% 0.12/0.36  ipcrm: permission denied for id (730136580)
% 0.12/0.36  ipcrm: permission denied for id (734396421)
% 0.12/0.36  ipcrm: permission denied for id (730202118)
% 0.12/0.37  ipcrm: permission denied for id (730267655)
% 0.12/0.37  ipcrm: permission denied for id (734429192)
% 0.12/0.37  ipcrm: permission denied for id (730333193)
% 0.12/0.37  ipcrm: permission denied for id (730431500)
% 0.12/0.37  ipcrm: permission denied for id (734527501)
% 0.12/0.38  ipcrm: permission denied for id (734593039)
% 0.12/0.38  ipcrm: permission denied for id (730595345)
% 0.12/0.38  ipcrm: permission denied for id (734789654)
% 0.12/0.39  ipcrm: permission denied for id (734822423)
% 0.12/0.39  ipcrm: permission denied for id (730890264)
% 0.12/0.39  ipcrm: permission denied for id (730988571)
% 0.12/0.39  ipcrm: permission denied for id (731054110)
% 0.12/0.40  ipcrm: permission denied for id (734986271)
% 0.12/0.40  ipcrm: permission denied for id (735019040)
% 0.12/0.40  ipcrm: permission denied for id (731152417)
% 0.12/0.40  ipcrm: permission denied for id (735051810)
% 0.20/0.40  ipcrm: permission denied for id (735084579)
% 0.20/0.40  ipcrm: permission denied for id (735117348)
% 0.20/0.40  ipcrm: permission denied for id (735150117)
% 0.20/0.40  ipcrm: permission denied for id (731316262)
% 0.20/0.41  ipcrm: permission denied for id (731414569)
% 0.20/0.41  ipcrm: permission denied for id (731447338)
% 0.20/0.41  ipcrm: permission denied for id (735281196)
% 0.20/0.42  ipcrm: permission denied for id (731611183)
% 0.20/0.42  ipcrm: permission denied for id (735445042)
% 0.20/0.42  ipcrm: permission denied for id (731742259)
% 0.20/0.42  ipcrm: permission denied for id (731775028)
% 0.20/0.42  ipcrm: permission denied for id (731807797)
% 0.20/0.43  ipcrm: permission denied for id (731873335)
% 0.20/0.43  ipcrm: permission denied for id (735510584)
% 0.20/0.43  ipcrm: permission denied for id (735543353)
% 0.20/0.43  ipcrm: permission denied for id (735608891)
% 0.20/0.43  ipcrm: permission denied for id (735674429)
% 0.20/0.43  ipcrm: permission denied for id (732069950)
% 0.20/0.44  ipcrm: permission denied for id (732102719)
% 0.20/0.44  ipcrm: permission denied for id (735707200)
% 0.20/0.44  ipcrm: permission denied for id (732168257)
% 0.20/0.44  ipcrm: permission denied for id (735739970)
% 0.20/0.44  ipcrm: permission denied for id (732233795)
% 0.20/0.44  ipcrm: permission denied for id (732266564)
% 0.20/0.44  ipcrm: permission denied for id (732299333)
% 0.20/0.45  ipcrm: permission denied for id (732332102)
% 0.20/0.45  ipcrm: permission denied for id (732364871)
% 0.20/0.45  ipcrm: permission denied for id (735772744)
% 0.20/0.45  ipcrm: permission denied for id (735805513)
% 0.20/0.45  ipcrm: permission denied for id (735838282)
% 0.20/0.45  ipcrm: permission denied for id (735903820)
% 0.20/0.45  ipcrm: permission denied for id (735936589)
% 0.20/0.46  ipcrm: permission denied for id (736002126)
% 0.20/0.46  ipcrm: permission denied for id (736067664)
% 0.20/0.46  ipcrm: permission denied for id (736100433)
% 0.20/0.46  ipcrm: permission denied for id (736133202)
% 0.20/0.46  ipcrm: permission denied for id (732790868)
% 0.20/0.47  ipcrm: permission denied for id (732856406)
% 0.20/0.47  ipcrm: permission denied for id (732889175)
% 0.20/0.47  ipcrm: permission denied for id (736231512)
% 0.20/0.47  ipcrm: permission denied for id (732954713)
% 0.20/0.47  ipcrm: permission denied for id (733020251)
% 0.20/0.47  ipcrm: permission denied for id (733053020)
% 0.20/0.47  ipcrm: permission denied for id (733085789)
% 0.20/0.48  ipcrm: permission denied for id (733118558)
% 0.20/0.48  ipcrm: permission denied for id (733216864)
% 0.20/0.48  ipcrm: permission denied for id (733249633)
% 0.20/0.48  ipcrm: permission denied for id (733282402)
% 0.20/0.48  ipcrm: permission denied for id (733413477)
% 0.20/0.49  ipcrm: permission denied for id (733446246)
% 0.20/0.49  ipcrm: permission denied for id (733511783)
% 0.20/0.49  ipcrm: permission denied for id (736428137)
% 0.20/0.49  ipcrm: permission denied for id (733610091)
% 0.20/0.49  ipcrm: permission denied for id (733675629)
% 0.20/0.50  ipcrm: permission denied for id (733708398)
% 0.20/0.50  ipcrm: permission denied for id (733741167)
% 0.20/0.50  ipcrm: permission denied for id (736526448)
% 0.20/0.50  ipcrm: permission denied for id (733806705)
% 0.20/0.50  ipcrm: permission denied for id (733905012)
% 0.20/0.50  ipcrm: permission denied for id (733937781)
% 0.20/0.51  ipcrm: permission denied for id (733970550)
% 0.20/0.51  ipcrm: permission denied for id (736624759)
% 0.20/0.51  ipcrm: permission denied for id (734036088)
% 0.20/0.51  ipcrm: permission denied for id (734068857)
% 0.20/0.51  ipcrm: permission denied for id (734101626)
% 0.20/0.51  ipcrm: permission denied for id (734167164)
% 0.20/0.51  ipcrm: permission denied for id (734199933)
% 0.20/0.52  ipcrm: permission denied for id (734232702)
% 0.20/0.52  ipcrm: permission denied for id (734265471)
% 0.20/0.58  % (1780)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.58  % (1779)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.59  % (1779)Refutation found. Thanks to Tanya!
% 0.20/0.59  % SZS status Theorem for theBenchmark
% 0.20/0.59  % SZS output start Proof for theBenchmark
% 0.20/0.59  fof(f127,plain,(
% 0.20/0.59    $false),
% 0.20/0.59    inference(global_subsumption,[],[f22,f126])).
% 0.20/0.59  fof(f126,plain,(
% 0.20/0.59    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.59    inference(resolution,[],[f125,f28])).
% 0.20/0.59  fof(f28,plain,(
% 0.20/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.59    inference(cnf_transformation,[],[f19])).
% 0.20/0.59  fof(f19,plain,(
% 0.20/0.59    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.59    inference(nnf_transformation,[],[f5])).
% 0.20/0.59  fof(f5,axiom,(
% 0.20/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.59  fof(f125,plain,(
% 0.20/0.59    ~r1_tarski(sK2,u1_struct_0(sK0))),
% 0.20/0.59    inference(global_subsumption,[],[f23,f107,f121])).
% 0.20/0.59  fof(f121,plain,(
% 0.20/0.59    ~v2_tex_2(sK2,sK0) | ~r1_tarski(sK2,u1_struct_0(sK0))),
% 0.20/0.59    inference(resolution,[],[f100,f32])).
% 0.20/0.59  fof(f32,plain,(
% 0.20/0.59    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 0.20/0.59    inference(superposition,[],[f26,f27])).
% 0.20/0.59  fof(f27,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f1])).
% 0.20/0.59  fof(f1,axiom,(
% 0.20/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.59  fof(f26,plain,(
% 0.20/0.59    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f3])).
% 0.20/0.59  fof(f3,axiom,(
% 0.20/0.59    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.59  fof(f100,plain,(
% 0.20/0.59    ~r1_tarski(k3_xboole_0(sK1,sK2),sK2) | ~v2_tex_2(sK2,sK0) | ~r1_tarski(sK2,u1_struct_0(sK0))),
% 0.20/0.59    inference(resolution,[],[f95,f22])).
% 0.20/0.59  fof(f95,plain,(
% 0.20/0.59    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k3_xboole_0(sK1,sK2),X0) | ~v2_tex_2(X0,sK0) | ~r1_tarski(sK2,u1_struct_0(sK0))) )),
% 0.20/0.59    inference(resolution,[],[f87,f36])).
% 0.20/0.59  fof(f36,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X2) | ~r1_tarski(X0,X2)) )),
% 0.20/0.59    inference(superposition,[],[f30,f27])).
% 0.20/0.59  fof(f30,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f13])).
% 0.20/0.59  fof(f13,plain,(
% 0.20/0.59    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.20/0.59    inference(ennf_transformation,[],[f2])).
% 0.20/0.59  fof(f2,axiom,(
% 0.20/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).
% 0.20/0.59  fof(f87,plain,(
% 0.20/0.59    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k3_xboole_0(sK1,sK2),u1_struct_0(sK0)) | ~r1_tarski(k3_xboole_0(sK1,sK2),X0) | ~v2_tex_2(X0,sK0)) )),
% 0.20/0.59    inference(resolution,[],[f82,f29])).
% 0.20/0.59  fof(f29,plain,(
% 0.20/0.59    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f19])).
% 0.20/0.59  fof(f82,plain,(
% 0.20/0.59    ( ! [X0] : (~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | ~r1_tarski(k3_xboole_0(sK1,sK2),X0)) )),
% 0.20/0.59    inference(global_subsumption,[],[f20,f81])).
% 0.20/0.59  fof(f81,plain,(
% 0.20/0.59    ( ! [X0] : (~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k3_xboole_0(sK1,sK2),X0) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.20/0.59    inference(forward_demodulation,[],[f80,f41])).
% 0.20/0.59  fof(f41,plain,(
% 0.20/0.59    ( ! [X1] : (k9_subset_1(u1_struct_0(sK0),X1,sK2) = k3_xboole_0(X1,sK2)) )),
% 0.20/0.59    inference(resolution,[],[f31,f22])).
% 0.20/0.59  fof(f31,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f14])).
% 0.20/0.59  fof(f14,plain,(
% 0.20/0.59    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.59    inference(ennf_transformation,[],[f4])).
% 0.20/0.59  fof(f4,axiom,(
% 0.20/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.20/0.59  fof(f80,plain,(
% 0.20/0.59    ( ! [X0] : (~r1_tarski(k3_xboole_0(sK1,sK2),X0) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.20/0.59    inference(forward_demodulation,[],[f78,f41])).
% 0.20/0.59  fof(f78,plain,(
% 0.20/0.59    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0) | ~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.20/0.59    inference(resolution,[],[f25,f24])).
% 0.20/0.59  fof(f24,plain,(
% 0.20/0.59    ~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.20/0.59    inference(cnf_transformation,[],[f18])).
% 0.20/0.59  fof(f18,plain,(
% 0.20/0.59    ((~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & (v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.20/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f17,f16,f15])).
% 0.20/0.59  fof(f15,plain,(
% 0.20/0.59    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(X1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.20/0.59    introduced(choice_axiom,[])).
% 0.20/0.59  fof(f16,plain,(
% 0.20/0.59    ? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(X1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.59    introduced(choice_axiom,[])).
% 0.20/0.59  fof(f17,plain,(
% 0.20/0.59    ? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & (v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.59    introduced(choice_axiom,[])).
% 0.20/0.59  fof(f10,plain,(
% 0.20/0.59    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.59    inference(flattening,[],[f9])).
% 0.20/0.59  fof(f9,plain,(
% 0.20/0.59    ? [X0] : (? [X1] : (? [X2] : ((~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.59    inference(ennf_transformation,[],[f8])).
% 0.20/0.59  fof(f8,negated_conjecture,(
% 0.20/0.59    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.20/0.59    inference(negated_conjecture,[],[f7])).
% 0.20/0.59  fof(f7,conjecture,(
% 0.20/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tex_2)).
% 0.20/0.59  fof(f25,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f12])).
% 0.20/0.59  fof(f12,plain,(
% 0.20/0.59    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.59    inference(flattening,[],[f11])).
% 0.20/0.59  fof(f11,plain,(
% 0.20/0.59    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) | (~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.59    inference(ennf_transformation,[],[f6])).
% 0.20/0.59  fof(f6,axiom,(
% 0.20/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & r1_tarski(X2,X1)) => v2_tex_2(X2,X0)))))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).
% 0.20/0.59  fof(f20,plain,(
% 0.20/0.59    l1_pre_topc(sK0)),
% 0.20/0.59    inference(cnf_transformation,[],[f18])).
% 0.20/0.59  fof(f107,plain,(
% 0.20/0.59    ~v2_tex_2(sK1,sK0)),
% 0.20/0.59    inference(global_subsumption,[],[f22,f106])).
% 0.20/0.59  fof(f106,plain,(
% 0.20/0.59    ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.59    inference(resolution,[],[f102,f28])).
% 0.20/0.59  fof(f102,plain,(
% 0.20/0.59    ~r1_tarski(sK2,u1_struct_0(sK0)) | ~v2_tex_2(sK1,sK0)),
% 0.20/0.59    inference(resolution,[],[f99,f26])).
% 0.20/0.59  fof(f99,plain,(
% 0.20/0.59    ~r1_tarski(k3_xboole_0(sK1,sK2),sK1) | ~v2_tex_2(sK1,sK0) | ~r1_tarski(sK2,u1_struct_0(sK0))),
% 0.20/0.59    inference(resolution,[],[f95,f21])).
% 0.20/0.59  fof(f21,plain,(
% 0.20/0.59    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.59    inference(cnf_transformation,[],[f18])).
% 0.20/0.59  fof(f23,plain,(
% 0.20/0.59    v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)),
% 0.20/0.59    inference(cnf_transformation,[],[f18])).
% 0.20/0.59  fof(f22,plain,(
% 0.20/0.59    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.59    inference(cnf_transformation,[],[f18])).
% 0.20/0.59  % SZS output end Proof for theBenchmark
% 0.20/0.59  % (1779)------------------------------
% 0.20/0.59  % (1779)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (1779)Termination reason: Refutation
% 0.20/0.59  
% 0.20/0.59  % (1779)Memory used [KB]: 6268
% 0.20/0.59  % (1779)Time elapsed: 0.036 s
% 0.20/0.59  % (1779)------------------------------
% 0.20/0.59  % (1779)------------------------------
% 0.20/0.59  % (1787)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.20/0.59  % (1781)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.60  % (1631)Success in time 0.243 s
%------------------------------------------------------------------------------
