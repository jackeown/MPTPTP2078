%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1874+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:36 EST 2020

% Result     : Theorem 3.74s
% Output     : Refutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 278 expanded)
%              Number of leaves         :   13 (  97 expanded)
%              Depth                    :   20
%              Number of atoms          :  269 (1679 expanded)
%              Number of equality atoms :   39 ( 256 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8631,plain,(
    $false ),
    inference(subsumption_resolution,[],[f8630,f5107])).

fof(f5107,plain,(
    ~ v2_struct_0(sK65) ),
    inference(cnf_transformation,[],[f4521])).

fof(f4521,plain,
    ( k6_domain_1(u1_struct_0(sK65),sK67) != k9_subset_1(u1_struct_0(sK65),sK66,k2_pre_topc(sK65,k6_domain_1(u1_struct_0(sK65),sK67)))
    & r2_hidden(sK67,sK66)
    & m1_subset_1(sK67,u1_struct_0(sK65))
    & v2_tex_2(sK66,sK65)
    & m1_subset_1(sK66,k1_zfmisc_1(u1_struct_0(sK65)))
    & l1_pre_topc(sK65)
    & v2_pre_topc(sK65)
    & ~ v2_struct_0(sK65) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK65,sK66,sK67])],[f3711,f4520,f4519,f4518])).

fof(f4518,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(sK65),X2) != k9_subset_1(u1_struct_0(sK65),X1,k2_pre_topc(sK65,k6_domain_1(u1_struct_0(sK65),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK65)) )
          & v2_tex_2(X1,sK65)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK65))) )
      & l1_pre_topc(sK65)
      & v2_pre_topc(sK65)
      & ~ v2_struct_0(sK65) ) ),
    introduced(choice_axiom,[])).

fof(f4519,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k6_domain_1(u1_struct_0(sK65),X2) != k9_subset_1(u1_struct_0(sK65),X1,k2_pre_topc(sK65,k6_domain_1(u1_struct_0(sK65),X2)))
            & r2_hidden(X2,X1)
            & m1_subset_1(X2,u1_struct_0(sK65)) )
        & v2_tex_2(X1,sK65)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK65))) )
   => ( ? [X2] :
          ( k6_domain_1(u1_struct_0(sK65),X2) != k9_subset_1(u1_struct_0(sK65),sK66,k2_pre_topc(sK65,k6_domain_1(u1_struct_0(sK65),X2)))
          & r2_hidden(X2,sK66)
          & m1_subset_1(X2,u1_struct_0(sK65)) )
      & v2_tex_2(sK66,sK65)
      & m1_subset_1(sK66,k1_zfmisc_1(u1_struct_0(sK65))) ) ),
    introduced(choice_axiom,[])).

fof(f4520,plain,
    ( ? [X2] :
        ( k6_domain_1(u1_struct_0(sK65),X2) != k9_subset_1(u1_struct_0(sK65),sK66,k2_pre_topc(sK65,k6_domain_1(u1_struct_0(sK65),X2)))
        & r2_hidden(X2,sK66)
        & m1_subset_1(X2,u1_struct_0(sK65)) )
   => ( k6_domain_1(u1_struct_0(sK65),sK67) != k9_subset_1(u1_struct_0(sK65),sK66,k2_pre_topc(sK65,k6_domain_1(u1_struct_0(sK65),sK67)))
      & r2_hidden(sK67,sK66)
      & m1_subset_1(sK67,u1_struct_0(sK65)) ) ),
    introduced(choice_axiom,[])).

fof(f3711,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3710])).

fof(f3710,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3689])).

fof(f3689,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tex_2(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( r2_hidden(X2,X1)
                   => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3688])).

fof(f3688,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,X1)
                 => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_tex_2)).

fof(f8630,plain,(
    v2_struct_0(sK65) ),
    inference(subsumption_resolution,[],[f8629,f5108])).

fof(f5108,plain,(
    v2_pre_topc(sK65) ),
    inference(cnf_transformation,[],[f4521])).

fof(f8629,plain,
    ( ~ v2_pre_topc(sK65)
    | v2_struct_0(sK65) ),
    inference(subsumption_resolution,[],[f8628,f5109])).

fof(f5109,plain,(
    l1_pre_topc(sK65) ),
    inference(cnf_transformation,[],[f4521])).

fof(f8628,plain,
    ( ~ l1_pre_topc(sK65)
    | ~ v2_pre_topc(sK65)
    | v2_struct_0(sK65) ),
    inference(subsumption_resolution,[],[f8627,f5110])).

fof(f5110,plain,(
    m1_subset_1(sK66,k1_zfmisc_1(u1_struct_0(sK65))) ),
    inference(cnf_transformation,[],[f4521])).

fof(f8627,plain,
    ( ~ m1_subset_1(sK66,k1_zfmisc_1(u1_struct_0(sK65)))
    | ~ l1_pre_topc(sK65)
    | ~ v2_pre_topc(sK65)
    | v2_struct_0(sK65) ),
    inference(subsumption_resolution,[],[f8626,f5111])).

fof(f5111,plain,(
    v2_tex_2(sK66,sK65) ),
    inference(cnf_transformation,[],[f4521])).

fof(f8626,plain,
    ( ~ v2_tex_2(sK66,sK65)
    | ~ m1_subset_1(sK66,k1_zfmisc_1(u1_struct_0(sK65)))
    | ~ l1_pre_topc(sK65)
    | ~ v2_pre_topc(sK65)
    | v2_struct_0(sK65) ),
    inference(subsumption_resolution,[],[f8625,f7965])).

fof(f7965,plain,(
    m1_subset_1(k2_tarski(sK67,sK67),k1_zfmisc_1(u1_struct_0(sK65))) ),
    inference(backward_demodulation,[],[f7956,f7959])).

fof(f7959,plain,(
    k6_domain_1(u1_struct_0(sK65),sK67) = k2_tarski(sK67,sK67) ),
    inference(subsumption_resolution,[],[f7928,f7878])).

fof(f7878,plain,(
    ~ v1_xboole_0(u1_struct_0(sK65)) ),
    inference(backward_demodulation,[],[f7866,f7848])).

fof(f7848,plain,(
    u1_struct_0(sK65) = k2_struct_0(sK65) ),
    inference(resolution,[],[f7410,f5596])).

fof(f5596,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4035])).

fof(f4035,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1773])).

fof(f1773,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f7410,plain,(
    l1_struct_0(sK65) ),
    inference(resolution,[],[f5109,f5741])).

fof(f5741,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4092])).

fof(f4092,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1782])).

fof(f1782,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f7866,plain,(
    ~ v1_xboole_0(k2_struct_0(sK65)) ),
    inference(subsumption_resolution,[],[f7846,f5107])).

fof(f7846,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK65))
    | v2_struct_0(sK65) ),
    inference(resolution,[],[f7410,f5574])).

fof(f5574,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4030])).

fof(f4030,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4029])).

fof(f4029,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1800])).

fof(f1800,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f7928,plain,
    ( k6_domain_1(u1_struct_0(sK65),sK67) = k2_tarski(sK67,sK67)
    | v1_xboole_0(u1_struct_0(sK65)) ),
    inference(resolution,[],[f5112,f6328])).

fof(f6328,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f5203,f6152])).

fof(f6152,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f254])).

fof(f254,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f5203,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3764])).

fof(f3764,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f3763])).

fof(f3763,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1935])).

fof(f1935,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f5112,plain,(
    m1_subset_1(sK67,u1_struct_0(sK65)) ),
    inference(cnf_transformation,[],[f4521])).

fof(f7956,plain,(
    m1_subset_1(k6_domain_1(u1_struct_0(sK65),sK67),k1_zfmisc_1(u1_struct_0(sK65))) ),
    inference(subsumption_resolution,[],[f7921,f7878])).

fof(f7921,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK65),sK67),k1_zfmisc_1(u1_struct_0(sK65)))
    | v1_xboole_0(u1_struct_0(sK65)) ),
    inference(resolution,[],[f5112,f5202])).

fof(f5202,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3762])).

fof(f3762,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f3761])).

fof(f3761,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1893])).

fof(f1893,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f8625,plain,
    ( ~ m1_subset_1(k2_tarski(sK67,sK67),k1_zfmisc_1(u1_struct_0(sK65)))
    | ~ v2_tex_2(sK66,sK65)
    | ~ m1_subset_1(sK66,k1_zfmisc_1(u1_struct_0(sK65)))
    | ~ l1_pre_topc(sK65)
    | ~ v2_pre_topc(sK65)
    | v2_struct_0(sK65) ),
    inference(subsumption_resolution,[],[f8611,f7794])).

fof(f7794,plain,(
    r1_tarski(k2_tarski(sK67,sK67),sK66) ),
    inference(resolution,[],[f5113,f6405])).

fof(f6405,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f5633,f6152])).

fof(f5633,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f4815])).

fof(f4815,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f302])).

fof(f302,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f5113,plain,(
    r2_hidden(sK67,sK66) ),
    inference(cnf_transformation,[],[f4521])).

fof(f8611,plain,
    ( ~ r1_tarski(k2_tarski(sK67,sK67),sK66)
    | ~ m1_subset_1(k2_tarski(sK67,sK67),k1_zfmisc_1(u1_struct_0(sK65)))
    | ~ v2_tex_2(sK66,sK65)
    | ~ m1_subset_1(sK66,k1_zfmisc_1(u1_struct_0(sK65)))
    | ~ l1_pre_topc(sK65)
    | ~ v2_pre_topc(sK65)
    | v2_struct_0(sK65) ),
    inference(trivial_inequality_removal,[],[f8606])).

fof(f8606,plain,
    ( k2_tarski(sK67,sK67) != k2_tarski(sK67,sK67)
    | ~ r1_tarski(k2_tarski(sK67,sK67),sK66)
    | ~ m1_subset_1(k2_tarski(sK67,sK67),k1_zfmisc_1(u1_struct_0(sK65)))
    | ~ v2_tex_2(sK66,sK65)
    | ~ m1_subset_1(sK66,k1_zfmisc_1(u1_struct_0(sK65)))
    | ~ l1_pre_topc(sK65)
    | ~ v2_pre_topc(sK65)
    | v2_struct_0(sK65) ),
    inference(superposition,[],[f7960,f5241])).

fof(f5241,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
      | ~ r1_tarski(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4608])).

fof(f4608,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( sK90(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK90(X0,X1)))
                & r1_tarski(sK90(X0,X1),X1)
                & m1_subset_1(sK90(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK90])],[f4606,f4607])).

fof(f4607,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK90(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK90(X0,X1)))
        & r1_tarski(sK90(X0,X1),X1)
        & m1_subset_1(sK90(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f4606,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f4605])).

fof(f4605,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3796])).

fof(f3796,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3795])).

fof(f3795,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3687])).

fof(f3687,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X2,X1)
                 => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).

fof(f7960,plain,(
    k2_tarski(sK67,sK67) != k9_subset_1(u1_struct_0(sK65),sK66,k2_pre_topc(sK65,k2_tarski(sK67,sK67))) ),
    inference(backward_demodulation,[],[f5114,f7959])).

fof(f5114,plain,(
    k6_domain_1(u1_struct_0(sK65),sK67) != k9_subset_1(u1_struct_0(sK65),sK66,k2_pre_topc(sK65,k6_domain_1(u1_struct_0(sK65),sK67))) ),
    inference(cnf_transformation,[],[f4521])).
%------------------------------------------------------------------------------
