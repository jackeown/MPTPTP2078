%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:37 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 151 expanded)
%              Number of leaves         :   14 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :  182 ( 425 expanded)
%              Number of equality atoms :   44 (  79 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f462,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f148,f309,f334,f461])).

fof(f461,plain,
    ( spl6_2
    | ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f456])).

fof(f456,plain,
    ( $false
    | spl6_2
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f48,f406])).

fof(f406,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl6_2
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f197,f304])).

fof(f304,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f302])).

fof(f302,plain,
    ( spl6_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f197,plain,
    ( ~ r1_xboole_0(sK2,sK2)
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f191,f191,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
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

fof(f191,plain,
    ( r2_hidden(sK5(sK1),sK2)
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f26,f156,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f156,plain,
    ( r2_hidden(sK5(sK1),sK1)
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f154,f45])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f154,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f97,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f97,plain,
    ( k1_xboole_0 != sK1
    | spl6_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f26,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

fof(f48,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,X0)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f334,plain,
    ( spl6_2
    | ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f326])).

fof(f326,plain,
    ( $false
    | spl6_2
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f26,f97,f314,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = X0
      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f314,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | spl6_2
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f170,f308])).

fof(f308,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f306])).

fof(f306,plain,
    ( spl6_4
  <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f170,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1))
    | spl6_2 ),
    inference(backward_demodulation,[],[f27,f169])).

fof(f169,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | spl6_2 ),
    inference(forward_demodulation,[],[f163,f67])).

fof(f67,plain,(
    k1_setfam_1(sK1) = k6_setfam_1(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f28,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f163,plain,
    ( k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1)
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f97,f28,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f27,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f309,plain,
    ( spl6_3
    | spl6_4 ),
    inference(avatar_split_clause,[],[f60,f306,f302])).

fof(f60,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f58,f53])).

fof(f53,plain,(
    k1_setfam_1(sK2) = k6_setfam_1(sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f25,f38])).

fof(f25,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f58,plain,
    ( k1_xboole_0 = sK2
    | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2) ),
    inference(resolution,[],[f25,f30])).

fof(f148,plain,(
    ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f144])).

fof(f144,plain,
    ( $false
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f54,f138,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f138,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),sK0)
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f101,f124])).

fof(f124,plain,
    ( sK0 = k8_setfam_1(sK0,k1_xboole_0)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f102,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k8_setfam_1(X0,k1_xboole_0) = X0 ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 != X1
      | k8_setfam_1(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f102,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f28,f98])).

fof(f98,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f101,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0))
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f27,f98])).

fof(f54,plain,(
    m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f25,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:47:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.38  ipcrm: permission denied for id (825753602)
% 0.14/0.38  ipcrm: permission denied for id (825819139)
% 0.14/0.38  ipcrm: permission denied for id (825851908)
% 0.14/0.39  ipcrm: permission denied for id (825917447)
% 0.14/0.40  ipcrm: permission denied for id (826015757)
% 0.14/0.40  ipcrm: permission denied for id (826081294)
% 0.14/0.40  ipcrm: permission denied for id (826114063)
% 0.14/0.40  ipcrm: permission denied for id (826212370)
% 0.14/0.40  ipcrm: permission denied for id (826245139)
% 0.14/0.40  ipcrm: permission denied for id (826277908)
% 0.14/0.41  ipcrm: permission denied for id (826343446)
% 0.14/0.41  ipcrm: permission denied for id (826376215)
% 0.14/0.41  ipcrm: permission denied for id (826572829)
% 0.14/0.41  ipcrm: permission denied for id (826605598)
% 0.14/0.42  ipcrm: permission denied for id (826638367)
% 0.14/0.42  ipcrm: permission denied for id (826671136)
% 0.14/0.42  ipcrm: permission denied for id (826769444)
% 0.14/0.42  ipcrm: permission denied for id (826802213)
% 0.14/0.42  ipcrm: permission denied for id (826867751)
% 0.21/0.43  ipcrm: permission denied for id (826966059)
% 0.21/0.43  ipcrm: permission denied for id (827031598)
% 0.21/0.43  ipcrm: permission denied for id (827064367)
% 0.21/0.43  ipcrm: permission denied for id (827162674)
% 0.21/0.43  ipcrm: permission denied for id (827195443)
% 0.21/0.43  ipcrm: permission denied for id (827260981)
% 0.21/0.44  ipcrm: permission denied for id (827392058)
% 0.21/0.44  ipcrm: permission denied for id (827457596)
% 0.21/0.44  ipcrm: permission denied for id (827555903)
% 0.21/0.44  ipcrm: permission denied for id (827588673)
% 0.21/0.45  ipcrm: permission denied for id (827654212)
% 0.21/0.45  ipcrm: permission denied for id (827785288)
% 0.21/0.45  ipcrm: permission denied for id (827818057)
% 0.21/0.45  ipcrm: permission denied for id (827850827)
% 0.21/0.45  ipcrm: permission denied for id (827883596)
% 0.21/0.46  ipcrm: permission denied for id (827916366)
% 0.21/0.46  ipcrm: permission denied for id (827981904)
% 0.21/0.46  ipcrm: permission denied for id (828047442)
% 0.21/0.46  ipcrm: permission denied for id (828080211)
% 0.21/0.46  ipcrm: permission denied for id (828112980)
% 0.21/0.46  ipcrm: permission denied for id (828145749)
% 0.21/0.47  ipcrm: permission denied for id (828178519)
% 0.21/0.47  ipcrm: permission denied for id (828244058)
% 0.21/0.47  ipcrm: permission denied for id (828309595)
% 0.21/0.47  ipcrm: permission denied for id (828342364)
% 0.21/0.47  ipcrm: permission denied for id (828375133)
% 0.21/0.47  ipcrm: permission denied for id (828440671)
% 0.21/0.48  ipcrm: permission denied for id (828604516)
% 0.21/0.48  ipcrm: permission denied for id (828670055)
% 0.21/0.49  ipcrm: permission denied for id (828735593)
% 0.21/0.49  ipcrm: permission denied for id (828801133)
% 0.21/0.49  ipcrm: permission denied for id (828833903)
% 0.21/0.50  ipcrm: permission denied for id (828899442)
% 0.21/0.50  ipcrm: permission denied for id (828932211)
% 0.21/0.50  ipcrm: permission denied for id (828997749)
% 0.21/0.50  ipcrm: permission denied for id (829030518)
% 0.21/0.51  ipcrm: permission denied for id (829128827)
% 0.21/0.51  ipcrm: permission denied for id (829161596)
% 0.21/0.51  ipcrm: permission denied for id (829227134)
% 0.21/0.51  ipcrm: permission denied for id (829259903)
% 0.79/0.65  % (30086)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.19/0.66  % (30084)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.19/0.66  % (30098)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.19/0.66  % (30090)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.19/0.66  % (30088)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.19/0.66  % (30084)Refutation not found, incomplete strategy% (30084)------------------------------
% 1.19/0.66  % (30084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.66  % (30084)Termination reason: Refutation not found, incomplete strategy
% 1.19/0.66  
% 1.19/0.66  % (30084)Memory used [KB]: 1663
% 1.19/0.66  % (30084)Time elapsed: 0.091 s
% 1.19/0.66  % (30084)------------------------------
% 1.19/0.66  % (30084)------------------------------
% 1.19/0.66  % (30103)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.19/0.67  % (30085)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.19/0.67  % (30100)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.19/0.67  % (30088)Refutation found. Thanks to Tanya!
% 1.19/0.67  % SZS status Theorem for theBenchmark
% 1.19/0.67  % SZS output start Proof for theBenchmark
% 1.19/0.67  fof(f462,plain,(
% 1.19/0.67    $false),
% 1.19/0.67    inference(avatar_sat_refutation,[],[f148,f309,f334,f461])).
% 1.19/0.67  fof(f461,plain,(
% 1.19/0.67    spl6_2 | ~spl6_3),
% 1.19/0.67    inference(avatar_contradiction_clause,[],[f456])).
% 1.19/0.67  fof(f456,plain,(
% 1.19/0.67    $false | (spl6_2 | ~spl6_3)),
% 1.19/0.67    inference(unit_resulting_resolution,[],[f48,f406])).
% 1.19/0.67  fof(f406,plain,(
% 1.19/0.67    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | (spl6_2 | ~spl6_3)),
% 1.19/0.67    inference(backward_demodulation,[],[f197,f304])).
% 1.19/0.67  fof(f304,plain,(
% 1.19/0.67    k1_xboole_0 = sK2 | ~spl6_3),
% 1.19/0.67    inference(avatar_component_clause,[],[f302])).
% 1.19/0.67  fof(f302,plain,(
% 1.19/0.67    spl6_3 <=> k1_xboole_0 = sK2),
% 1.19/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.19/0.67  fof(f197,plain,(
% 1.19/0.67    ~r1_xboole_0(sK2,sK2) | spl6_2),
% 1.19/0.67    inference(unit_resulting_resolution,[],[f191,f191,f42])).
% 1.19/0.67  fof(f42,plain,(
% 1.19/0.67    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.19/0.67    inference(cnf_transformation,[],[f24])).
% 1.19/0.67  fof(f24,plain,(
% 1.19/0.67    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.19/0.67    inference(ennf_transformation,[],[f13])).
% 1.19/0.67  fof(f13,plain,(
% 1.19/0.67    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.19/0.67    inference(rectify,[],[f4])).
% 1.19/0.67  fof(f4,axiom,(
% 1.19/0.67    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.19/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.19/0.67  fof(f191,plain,(
% 1.19/0.67    r2_hidden(sK5(sK1),sK2) | spl6_2),
% 1.19/0.67    inference(unit_resulting_resolution,[],[f26,f156,f34])).
% 1.19/0.67  fof(f34,plain,(
% 1.19/0.67    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.19/0.67    inference(cnf_transformation,[],[f18])).
% 1.19/0.67  fof(f18,plain,(
% 1.19/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.19/0.67    inference(ennf_transformation,[],[f2])).
% 1.19/0.67  fof(f2,axiom,(
% 1.19/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.19/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.19/0.67  fof(f156,plain,(
% 1.19/0.67    r2_hidden(sK5(sK1),sK1) | spl6_2),
% 1.19/0.67    inference(unit_resulting_resolution,[],[f154,f45])).
% 1.19/0.67  fof(f45,plain,(
% 1.19/0.67    ( ! [X0] : (r2_hidden(sK5(X0),X0) | v1_xboole_0(X0)) )),
% 1.19/0.67    inference(cnf_transformation,[],[f1])).
% 1.19/0.67  fof(f1,axiom,(
% 1.19/0.67    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.19/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.19/0.67  fof(f154,plain,(
% 1.19/0.67    ~v1_xboole_0(sK1) | spl6_2),
% 1.19/0.67    inference(unit_resulting_resolution,[],[f97,f39])).
% 1.19/0.67  fof(f39,plain,(
% 1.19/0.67    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.19/0.67    inference(cnf_transformation,[],[f22])).
% 1.19/0.67  fof(f22,plain,(
% 1.19/0.67    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.19/0.67    inference(ennf_transformation,[],[f3])).
% 1.19/0.67  fof(f3,axiom,(
% 1.19/0.67    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.19/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.19/0.67  fof(f97,plain,(
% 1.19/0.67    k1_xboole_0 != sK1 | spl6_2),
% 1.19/0.67    inference(avatar_component_clause,[],[f96])).
% 1.19/0.67  fof(f96,plain,(
% 1.19/0.67    spl6_2 <=> k1_xboole_0 = sK1),
% 1.19/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.19/0.67  fof(f26,plain,(
% 1.19/0.67    r1_tarski(sK1,sK2)),
% 1.19/0.67    inference(cnf_transformation,[],[f15])).
% 1.19/0.67  fof(f15,plain,(
% 1.19/0.67    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.19/0.67    inference(flattening,[],[f14])).
% 1.19/0.67  fof(f14,plain,(
% 1.19/0.67    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.19/0.67    inference(ennf_transformation,[],[f12])).
% 1.19/0.67  fof(f12,negated_conjecture,(
% 1.19/0.67    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 1.19/0.67    inference(negated_conjecture,[],[f11])).
% 1.19/0.67  fof(f11,conjecture,(
% 1.19/0.67    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 1.19/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).
% 1.19/0.67  fof(f48,plain,(
% 1.19/0.67    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.19/0.67    inference(equality_resolution,[],[f41])).
% 1.19/0.67  fof(f41,plain,(
% 1.19/0.67    ( ! [X0] : (r1_xboole_0(X0,X0) | k1_xboole_0 != X0) )),
% 1.19/0.67    inference(cnf_transformation,[],[f23])).
% 1.19/0.67  fof(f23,plain,(
% 1.19/0.67    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 1.19/0.67    inference(ennf_transformation,[],[f5])).
% 1.19/0.67  fof(f5,axiom,(
% 1.19/0.67    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.19/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 1.19/0.67  fof(f334,plain,(
% 1.19/0.67    spl6_2 | ~spl6_4),
% 1.19/0.67    inference(avatar_contradiction_clause,[],[f326])).
% 1.19/0.67  fof(f326,plain,(
% 1.19/0.67    $false | (spl6_2 | ~spl6_4)),
% 1.19/0.67    inference(unit_resulting_resolution,[],[f26,f97,f314,f37])).
% 1.19/0.67  fof(f37,plain,(
% 1.19/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = X0 | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))) )),
% 1.19/0.67    inference(cnf_transformation,[],[f20])).
% 1.19/0.67  fof(f20,plain,(
% 1.19/0.67    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 1.19/0.67    inference(flattening,[],[f19])).
% 1.19/0.67  fof(f19,plain,(
% 1.19/0.67    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 1.19/0.67    inference(ennf_transformation,[],[f10])).
% 1.19/0.67  fof(f10,axiom,(
% 1.19/0.67    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 1.19/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).
% 1.19/0.67  fof(f314,plain,(
% 1.19/0.67    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | (spl6_2 | ~spl6_4)),
% 1.19/0.67    inference(backward_demodulation,[],[f170,f308])).
% 1.19/0.67  fof(f308,plain,(
% 1.19/0.67    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl6_4),
% 1.19/0.67    inference(avatar_component_clause,[],[f306])).
% 1.19/0.67  fof(f306,plain,(
% 1.19/0.67    spl6_4 <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 1.19/0.67    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.19/0.67  fof(f170,plain,(
% 1.19/0.67    ~r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1)) | spl6_2),
% 1.19/0.67    inference(backward_demodulation,[],[f27,f169])).
% 1.19/0.67  fof(f169,plain,(
% 1.19/0.67    k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | spl6_2),
% 1.19/0.67    inference(forward_demodulation,[],[f163,f67])).
% 1.19/0.67  fof(f67,plain,(
% 1.19/0.67    k1_setfam_1(sK1) = k6_setfam_1(sK0,sK1)),
% 1.19/0.67    inference(unit_resulting_resolution,[],[f28,f38])).
% 1.19/0.67  fof(f38,plain,(
% 1.19/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k6_setfam_1(X0,X1) = k1_setfam_1(X1)) )),
% 1.19/0.67    inference(cnf_transformation,[],[f21])).
% 1.19/0.67  fof(f21,plain,(
% 1.19/0.67    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.19/0.67    inference(ennf_transformation,[],[f8])).
% 1.19/0.67  fof(f8,axiom,(
% 1.19/0.67    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 1.19/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 1.19/0.67  fof(f28,plain,(
% 1.19/0.67    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.19/0.67    inference(cnf_transformation,[],[f15])).
% 1.19/0.67  fof(f163,plain,(
% 1.19/0.67    k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1) | spl6_2),
% 1.19/0.67    inference(unit_resulting_resolution,[],[f97,f28,f30])).
% 1.19/0.67  fof(f30,plain,(
% 1.19/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)) )),
% 1.19/0.67    inference(cnf_transformation,[],[f16])).
% 1.19/0.67  fof(f16,plain,(
% 1.19/0.67    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.19/0.67    inference(ennf_transformation,[],[f6])).
% 1.19/0.67  fof(f6,axiom,(
% 1.19/0.67    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 1.19/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).
% 1.19/0.67  fof(f27,plain,(
% 1.19/0.67    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 1.19/0.67    inference(cnf_transformation,[],[f15])).
% 1.19/0.67  fof(f309,plain,(
% 1.19/0.67    spl6_3 | spl6_4),
% 1.19/0.67    inference(avatar_split_clause,[],[f60,f306,f302])).
% 1.19/0.67  fof(f60,plain,(
% 1.19/0.67    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | k1_xboole_0 = sK2),
% 1.19/0.67    inference(forward_demodulation,[],[f58,f53])).
% 1.19/0.67  fof(f53,plain,(
% 1.19/0.67    k1_setfam_1(sK2) = k6_setfam_1(sK0,sK2)),
% 1.19/0.67    inference(unit_resulting_resolution,[],[f25,f38])).
% 1.19/0.67  fof(f25,plain,(
% 1.19/0.67    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.19/0.67    inference(cnf_transformation,[],[f15])).
% 1.19/0.67  fof(f58,plain,(
% 1.19/0.67    k1_xboole_0 = sK2 | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2)),
% 1.19/0.67    inference(resolution,[],[f25,f30])).
% 1.19/0.67  fof(f148,plain,(
% 1.19/0.67    ~spl6_2),
% 1.19/0.67    inference(avatar_contradiction_clause,[],[f144])).
% 1.19/0.67  fof(f144,plain,(
% 1.19/0.67    $false | ~spl6_2),
% 1.19/0.67    inference(unit_resulting_resolution,[],[f54,f138,f33])).
% 1.19/0.67  fof(f33,plain,(
% 1.19/0.67    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.19/0.67    inference(cnf_transformation,[],[f9])).
% 1.19/0.67  fof(f9,axiom,(
% 1.19/0.67    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.19/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.19/0.67  fof(f138,plain,(
% 1.19/0.67    ~r1_tarski(k8_setfam_1(sK0,sK2),sK0) | ~spl6_2),
% 1.19/0.67    inference(backward_demodulation,[],[f101,f124])).
% 1.19/0.67  fof(f124,plain,(
% 1.19/0.67    sK0 = k8_setfam_1(sK0,k1_xboole_0) | ~spl6_2),
% 1.19/0.67    inference(unit_resulting_resolution,[],[f102,f47])).
% 1.19/0.67  fof(f47,plain,(
% 1.19/0.67    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 1.19/0.67    inference(equality_resolution,[],[f29])).
% 1.19/0.67  fof(f29,plain,(
% 1.19/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 != X1 | k8_setfam_1(X0,X1) = X0) )),
% 1.19/0.67    inference(cnf_transformation,[],[f16])).
% 1.19/0.67  fof(f102,plain,(
% 1.19/0.67    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl6_2),
% 1.19/0.67    inference(backward_demodulation,[],[f28,f98])).
% 1.19/0.67  fof(f98,plain,(
% 1.19/0.67    k1_xboole_0 = sK1 | ~spl6_2),
% 1.19/0.67    inference(avatar_component_clause,[],[f96])).
% 1.19/0.67  fof(f101,plain,(
% 1.19/0.67    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) | ~spl6_2),
% 1.19/0.67    inference(backward_demodulation,[],[f27,f98])).
% 1.19/0.67  fof(f54,plain,(
% 1.19/0.67    m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 1.19/0.67    inference(unit_resulting_resolution,[],[f25,f31])).
% 1.19/0.67  fof(f31,plain,(
% 1.19/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.19/0.67    inference(cnf_transformation,[],[f17])).
% 1.19/0.67  fof(f17,plain,(
% 1.19/0.67    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.19/0.67    inference(ennf_transformation,[],[f7])).
% 1.19/0.67  fof(f7,axiom,(
% 1.19/0.67    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.19/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).
% 1.19/0.67  % SZS output end Proof for theBenchmark
% 1.19/0.67  % (30088)------------------------------
% 1.19/0.67  % (30088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.67  % (30088)Termination reason: Refutation
% 1.19/0.67  
% 1.19/0.67  % (30088)Memory used [KB]: 6396
% 1.19/0.67  % (30088)Time elapsed: 0.103 s
% 1.19/0.67  % (30088)------------------------------
% 1.19/0.67  % (30088)------------------------------
% 1.19/0.67  % (30093)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.19/0.67  % (29923)Success in time 0.305 s
%------------------------------------------------------------------------------
