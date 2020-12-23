%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   97 (13704 expanded)
%              Number of leaves         :   12 (3473 expanded)
%              Depth                    :   22
%              Number of atoms          :  234 (43590 expanded)
%              Number of equality atoms :   26 (9036 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1019,plain,(
    $false ),
    inference(global_subsumption,[],[f665,f1004])).

fof(f1004,plain,(
    v1_partfun1(sK0,sK0) ),
    inference(superposition,[],[f37,f963])).

fof(f963,plain,(
    sK0 = k6_partfun1(sK0) ),
    inference(forward_demodulation,[],[f960,f732])).

fof(f732,plain,(
    sK0 = k2_relat_1(sK0) ),
    inference(backward_demodulation,[],[f645,f648])).

fof(f648,plain,(
    sK0 = sK2 ),
    inference(backward_demodulation,[],[f568,f645])).

fof(f568,plain,(
    sK2 = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f246,f245,f432,f555,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( sP4(sK3(X0,X1),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK3(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f555,plain,(
    ! [X0] : ~ sP4(X0,sK2) ),
    inference(unit_resulting_resolution,[],[f246,f245,f456,f77])).

fof(f77,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ sP4(X2,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ sP4(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f456,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f406,f180])).

fof(f180,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X5,X6)
      | ~ v1_xboole_0(X6) ) ),
    inference(resolution,[],[f75,f85])).

fof(f85,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f79,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f79,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f406,plain,(
    v1_xboole_0(k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f245,f371,f257,f311,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f311,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f302,f256])).

fof(f256,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f251,f234])).

fof(f234,plain,(
    sK2 = sK9(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f193,f68])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( sK9(X0,X1,X3) = X3
      | ~ sP8(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r1_tarski(k2_relat_1(X4),X1)
              & k1_relat_1(X4) = X0
              & X3 = X4
              & v1_funct_1(X4)
              & v1_relat_1(X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).

fof(f193,plain,(
    sP8(sK2,sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f36,f81])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_funct_2(X0,X1))
      | sP8(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( sP8(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f36,plain,(
    r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

fof(f251,plain,(
    sK0 = k1_relat_1(sK9(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f193,f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( k1_relat_1(sK9(X0,X1,X3)) = X0
      | ~ sP8(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f302,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    inference(unit_resulting_resolution,[],[f246,f245,f40])).

fof(f40,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f257,plain,(
    v1_funct_2(sK2,sK0,k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f243,f256])).

fof(f243,plain,(
    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f208,f234])).

fof(f208,plain,(
    v1_funct_2(sK9(sK0,sK1,sK2),k1_relat_1(sK9(sK0,sK1,sK2)),k2_relat_1(sK9(sK0,sK1,sK2))) ),
    inference(unit_resulting_resolution,[],[f197,f196,f39])).

fof(f39,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f196,plain,(
    v1_funct_1(sK9(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f193,f67])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( v1_funct_1(sK9(X0,X1,X3))
      | ~ sP8(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f197,plain,(
    v1_relat_1(sK9(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f193,f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( v1_relat_1(sK9(X0,X1,X3))
      | ~ sP8(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f371,plain,(
    ~ v1_partfun1(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f245,f369,f367,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_partfun1(X2,X0)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f367,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f352,f256])).

fof(f352,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    inference(unit_resulting_resolution,[],[f246,f273,f79,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f273,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(forward_demodulation,[],[f264,f234])).

fof(f264,plain,(
    r1_tarski(k2_relat_1(sK9(sK0,sK1,sK2)),sK1) ),
    inference(unit_resulting_resolution,[],[f193,f70])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(k2_relat_1(sK9(X0,X1,X3)),X1)
      | ~ sP8(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f369,plain,(
    ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(global_subsumption,[],[f35,f245,f367])).

fof(f35,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f432,plain,(
    ! [X0] : ~ r2_hidden(X0,sK2) ),
    inference(unit_resulting_resolution,[],[f419,f180])).

fof(f419,plain,(
    v1_xboole_0(sK2) ),
    inference(global_subsumption,[],[f406,f413])).

fof(f413,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f311,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f245,plain,(
    v1_funct_1(sK2) ),
    inference(backward_demodulation,[],[f196,f234])).

fof(f246,plain,(
    v1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f197,f234])).

fof(f645,plain,(
    sK0 = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f246,f245,f555,f631,f46])).

fof(f631,plain,(
    ! [X0] : ~ r2_hidden(X0,sK0) ),
    inference(forward_demodulation,[],[f566,f256])).

fof(f566,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f555,f78])).

fof(f78,plain,(
    ! [X0,X3] :
      ( sP4(k1_funct_1(X0,X3),X0)
      | ~ r2_hidden(X3,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | sP4(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f960,plain,(
    k6_partfun1(sK0) = k2_relat_1(sK0) ),
    inference(unit_resulting_resolution,[],[f657,f656,f716,f693,f46])).

fof(f693,plain,(
    ! [X0] : ~ r2_hidden(X0,k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f513,f648])).

fof(f513,plain,(
    ! [X0] : ~ r2_hidden(X0,k6_partfun1(sK2)) ),
    inference(unit_resulting_resolution,[],[f441,f180])).

fof(f441,plain,(
    v1_xboole_0(k6_partfun1(sK2)) ),
    inference(unit_resulting_resolution,[],[f419,f216])).

fof(f216,plain,(
    ! [X0] :
      ( v1_xboole_0(k6_partfun1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f51,f38])).

fof(f38,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f716,plain,(
    ! [X0] : ~ sP4(X0,sK0) ),
    inference(backward_demodulation,[],[f555,f648])).

fof(f656,plain,(
    v1_funct_1(sK0) ),
    inference(backward_demodulation,[],[f245,f648])).

fof(f657,plain,(
    v1_relat_1(sK0) ),
    inference(backward_demodulation,[],[f246,f648])).

fof(f37,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f665,plain,(
    ~ v1_partfun1(sK0,sK0) ),
    inference(backward_demodulation,[],[f371,f648])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:16:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.50  % (18442)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (18426)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.50  % (18424)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (18434)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (18441)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.51  % (18432)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (18442)Refutation not found, incomplete strategy% (18442)------------------------------
% 0.20/0.51  % (18442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (18443)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (18442)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (18442)Memory used [KB]: 10746
% 0.20/0.52  % (18442)Time elapsed: 0.107 s
% 0.20/0.52  % (18442)------------------------------
% 0.20/0.52  % (18442)------------------------------
% 0.20/0.52  % (18428)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (18423)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (18433)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (18425)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (18427)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (18438)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.52  % (18440)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (18422)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (18435)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (18440)Refutation not found, incomplete strategy% (18440)------------------------------
% 0.20/0.53  % (18440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (18440)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (18440)Memory used [KB]: 10746
% 0.20/0.53  % (18440)Time elapsed: 0.121 s
% 0.20/0.53  % (18440)------------------------------
% 0.20/0.53  % (18440)------------------------------
% 0.20/0.53  % (18439)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.53  % (18436)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (18449)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (18448)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (18420)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (18431)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (18429)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (18430)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (18445)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (18430)Refutation not found, incomplete strategy% (18430)------------------------------
% 0.20/0.54  % (18430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (18430)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (18430)Memory used [KB]: 10746
% 0.20/0.54  % (18430)Time elapsed: 0.139 s
% 0.20/0.54  % (18430)------------------------------
% 0.20/0.54  % (18430)------------------------------
% 0.20/0.55  % (18444)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.55  % (18421)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.56  % (18447)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.56  % (18446)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.56  % (18437)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.58  % (18444)Refutation found. Thanks to Tanya!
% 0.20/0.58  % SZS status Theorem for theBenchmark
% 0.20/0.58  % SZS output start Proof for theBenchmark
% 0.20/0.58  fof(f1019,plain,(
% 0.20/0.58    $false),
% 0.20/0.58    inference(global_subsumption,[],[f665,f1004])).
% 0.20/0.58  fof(f1004,plain,(
% 0.20/0.58    v1_partfun1(sK0,sK0)),
% 0.20/0.58    inference(superposition,[],[f37,f963])).
% 0.20/0.58  fof(f963,plain,(
% 0.20/0.58    sK0 = k6_partfun1(sK0)),
% 0.20/0.58    inference(forward_demodulation,[],[f960,f732])).
% 0.20/0.58  fof(f732,plain,(
% 0.20/0.58    sK0 = k2_relat_1(sK0)),
% 0.20/0.58    inference(backward_demodulation,[],[f645,f648])).
% 0.20/0.58  fof(f648,plain,(
% 0.20/0.58    sK0 = sK2),
% 0.20/0.58    inference(backward_demodulation,[],[f568,f645])).
% 0.20/0.58  fof(f568,plain,(
% 0.20/0.58    sK2 = k2_relat_1(sK2)),
% 0.20/0.58    inference(unit_resulting_resolution,[],[f246,f245,f432,f555,f46])).
% 0.20/0.58  fof(f46,plain,(
% 0.20/0.58    ( ! [X0,X1] : (sP4(sK3(X0,X1),X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK3(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 0.20/0.58    inference(cnf_transformation,[],[f22])).
% 0.20/0.58  fof(f22,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.58    inference(flattening,[],[f21])).
% 0.20/0.58  fof(f21,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f6])).
% 0.20/0.58  fof(f6,axiom,(
% 0.20/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 0.20/0.58  fof(f555,plain,(
% 0.20/0.58    ( ! [X0] : (~sP4(X0,sK2)) )),
% 0.20/0.58    inference(unit_resulting_resolution,[],[f246,f245,f456,f77])).
% 0.20/0.58  fof(f77,plain,(
% 0.20/0.58    ( ! [X2,X0] : (r2_hidden(X2,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~sP4(X2,X0) | ~v1_relat_1(X0)) )),
% 0.20/0.58    inference(equality_resolution,[],[f44])).
% 0.20/0.58  fof(f44,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~sP4(X2,X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.20/0.58    inference(cnf_transformation,[],[f22])).
% 0.20/0.58  fof(f456,plain,(
% 0.20/0.58    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2))) )),
% 0.20/0.58    inference(unit_resulting_resolution,[],[f406,f180])).
% 0.20/0.58  fof(f180,plain,(
% 0.20/0.58    ( ! [X6,X5] : (~r2_hidden(X5,X6) | ~v1_xboole_0(X6)) )),
% 0.20/0.58    inference(resolution,[],[f75,f85])).
% 0.20/0.58  fof(f85,plain,(
% 0.20/0.58    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.58    inference(unit_resulting_resolution,[],[f79,f58])).
% 0.20/0.58  fof(f58,plain,(
% 0.20/0.58    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f3])).
% 0.20/0.58  fof(f3,axiom,(
% 0.20/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.58  fof(f79,plain,(
% 0.20/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.58    inference(equality_resolution,[],[f53])).
% 0.20/0.58  fof(f53,plain,(
% 0.20/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.58    inference(cnf_transformation,[],[f2])).
% 0.20/0.58  fof(f2,axiom,(
% 0.20/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.58  fof(f75,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | ~v1_xboole_0(X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f34])).
% 0.20/0.58  fof(f34,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.58    inference(ennf_transformation,[],[f4])).
% 0.20/0.58  fof(f4,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.58  fof(f406,plain,(
% 0.20/0.58    v1_xboole_0(k2_relat_1(sK2))),
% 0.20/0.58    inference(unit_resulting_resolution,[],[f245,f371,f257,f311,f48])).
% 0.20/0.58  fof(f48,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f24])).
% 0.20/0.58  fof(f24,plain,(
% 0.20/0.58    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.58    inference(flattening,[],[f23])).
% 0.20/0.58  fof(f23,plain,(
% 0.20/0.58    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.58    inference(ennf_transformation,[],[f12])).
% 0.20/0.58  fof(f12,axiom,(
% 0.20/0.58    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.20/0.58  fof(f311,plain,(
% 0.20/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2))))),
% 0.20/0.58    inference(forward_demodulation,[],[f302,f256])).
% 0.20/0.58  fof(f256,plain,(
% 0.20/0.58    sK0 = k1_relat_1(sK2)),
% 0.20/0.58    inference(forward_demodulation,[],[f251,f234])).
% 0.20/0.58  fof(f234,plain,(
% 0.20/0.58    sK2 = sK9(sK0,sK1,sK2)),
% 0.20/0.58    inference(unit_resulting_resolution,[],[f193,f68])).
% 0.20/0.58  fof(f68,plain,(
% 0.20/0.58    ( ! [X0,X3,X1] : (sK9(X0,X1,X3) = X3 | ~sP8(X3,X1,X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f13])).
% 0.20/0.58  fof(f13,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).
% 0.20/0.58  fof(f193,plain,(
% 0.20/0.58    sP8(sK2,sK1,sK0)),
% 0.20/0.58    inference(unit_resulting_resolution,[],[f36,f81])).
% 0.20/0.58  fof(f81,plain,(
% 0.20/0.58    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_funct_2(X0,X1)) | sP8(X3,X1,X0)) )),
% 0.20/0.58    inference(equality_resolution,[],[f72])).
% 0.20/0.58  fof(f72,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (sP8(X3,X1,X0) | ~r2_hidden(X3,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.20/0.58    inference(cnf_transformation,[],[f13])).
% 0.20/0.58  fof(f36,plain,(
% 0.20/0.58    r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 0.20/0.58    inference(cnf_transformation,[],[f18])).
% 0.20/0.58  fof(f18,plain,(
% 0.20/0.58    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1)))),
% 0.20/0.58    inference(ennf_transformation,[],[f17])).
% 0.20/0.58  fof(f17,negated_conjecture,(
% 0.20/0.58    ~! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.58    inference(negated_conjecture,[],[f16])).
% 0.20/0.58  fof(f16,conjecture,(
% 0.20/0.58    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).
% 0.20/0.58  fof(f251,plain,(
% 0.20/0.58    sK0 = k1_relat_1(sK9(sK0,sK1,sK2))),
% 0.20/0.58    inference(unit_resulting_resolution,[],[f193,f69])).
% 0.20/0.58  fof(f69,plain,(
% 0.20/0.58    ( ! [X0,X3,X1] : (k1_relat_1(sK9(X0,X1,X3)) = X0 | ~sP8(X3,X1,X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f13])).
% 0.20/0.58  fof(f302,plain,(
% 0.20/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.20/0.58    inference(unit_resulting_resolution,[],[f246,f245,f40])).
% 0.20/0.58  fof(f40,plain,(
% 0.20/0.58    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f20])).
% 0.20/0.58  fof(f20,plain,(
% 0.20/0.58    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.58    inference(flattening,[],[f19])).
% 0.20/0.58  fof(f19,plain,(
% 0.20/0.58    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f15])).
% 0.20/0.58  fof(f15,axiom,(
% 0.20/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.20/0.58  fof(f257,plain,(
% 0.20/0.58    v1_funct_2(sK2,sK0,k2_relat_1(sK2))),
% 0.20/0.58    inference(backward_demodulation,[],[f243,f256])).
% 0.20/0.58  fof(f243,plain,(
% 0.20/0.58    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.20/0.58    inference(backward_demodulation,[],[f208,f234])).
% 0.20/0.58  fof(f208,plain,(
% 0.20/0.58    v1_funct_2(sK9(sK0,sK1,sK2),k1_relat_1(sK9(sK0,sK1,sK2)),k2_relat_1(sK9(sK0,sK1,sK2)))),
% 0.20/0.58    inference(unit_resulting_resolution,[],[f197,f196,f39])).
% 0.20/0.58  fof(f39,plain,(
% 0.20/0.58    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f20])).
% 0.20/0.58  fof(f196,plain,(
% 0.20/0.58    v1_funct_1(sK9(sK0,sK1,sK2))),
% 0.20/0.58    inference(unit_resulting_resolution,[],[f193,f67])).
% 0.20/0.58  fof(f67,plain,(
% 0.20/0.58    ( ! [X0,X3,X1] : (v1_funct_1(sK9(X0,X1,X3)) | ~sP8(X3,X1,X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f13])).
% 0.20/0.58  fof(f197,plain,(
% 0.20/0.58    v1_relat_1(sK9(sK0,sK1,sK2))),
% 0.20/0.58    inference(unit_resulting_resolution,[],[f193,f66])).
% 0.20/0.58  fof(f66,plain,(
% 0.20/0.58    ( ! [X0,X3,X1] : (v1_relat_1(sK9(X0,X1,X3)) | ~sP8(X3,X1,X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f13])).
% 0.20/0.58  fof(f371,plain,(
% 0.20/0.58    ~v1_partfun1(sK2,sK0)),
% 0.20/0.58    inference(unit_resulting_resolution,[],[f245,f369,f367,f64])).
% 0.20/0.58  fof(f64,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_partfun1(X2,X0) | v1_funct_2(X2,X0,X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f33])).
% 0.20/0.58  fof(f33,plain,(
% 0.20/0.58    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.58    inference(flattening,[],[f32])).
% 0.20/0.60  fof(f32,plain,(
% 0.20/0.60    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.60    inference(ennf_transformation,[],[f11])).
% 0.20/0.60  fof(f11,axiom,(
% 0.20/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).
% 0.20/0.60  fof(f367,plain,(
% 0.20/0.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.60    inference(forward_demodulation,[],[f352,f256])).
% 0.20/0.60  fof(f352,plain,(
% 0.20/0.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))),
% 0.20/0.60    inference(unit_resulting_resolution,[],[f246,f273,f79,f60])).
% 0.20/0.60  fof(f60,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | ~v1_relat_1(X2)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f29])).
% 0.20/0.60  fof(f29,plain,(
% 0.20/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.20/0.60    inference(flattening,[],[f28])).
% 0.20/0.60  fof(f28,plain,(
% 0.20/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.20/0.60    inference(ennf_transformation,[],[f10])).
% 0.20/0.60  fof(f10,axiom,(
% 0.20/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.20/0.60  fof(f273,plain,(
% 0.20/0.60    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.20/0.60    inference(forward_demodulation,[],[f264,f234])).
% 0.20/0.60  fof(f264,plain,(
% 0.20/0.60    r1_tarski(k2_relat_1(sK9(sK0,sK1,sK2)),sK1)),
% 0.20/0.60    inference(unit_resulting_resolution,[],[f193,f70])).
% 0.20/0.60  fof(f70,plain,(
% 0.20/0.60    ( ! [X0,X3,X1] : (r1_tarski(k2_relat_1(sK9(X0,X1,X3)),X1) | ~sP8(X3,X1,X0)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f13])).
% 0.20/0.60  fof(f369,plain,(
% 0.20/0.60    ~v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.60    inference(global_subsumption,[],[f35,f245,f367])).
% 0.20/0.60  fof(f35,plain,(
% 0.20/0.60    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 0.20/0.60    inference(cnf_transformation,[],[f18])).
% 0.20/0.60  fof(f432,plain,(
% 0.20/0.60    ( ! [X0] : (~r2_hidden(X0,sK2)) )),
% 0.20/0.60    inference(unit_resulting_resolution,[],[f419,f180])).
% 0.20/0.60  fof(f419,plain,(
% 0.20/0.60    v1_xboole_0(sK2)),
% 0.20/0.60    inference(global_subsumption,[],[f406,f413])).
% 0.20/0.60  fof(f413,plain,(
% 0.20/0.60    ~v1_xboole_0(k2_relat_1(sK2)) | v1_xboole_0(sK2)),
% 0.20/0.60    inference(resolution,[],[f311,f51])).
% 0.20/0.60  fof(f51,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0) | v1_xboole_0(X2)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f26])).
% 0.20/0.60  fof(f26,plain,(
% 0.20/0.60    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.20/0.60    inference(ennf_transformation,[],[f9])).
% 0.20/0.60  fof(f9,axiom,(
% 0.20/0.60    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.20/0.60  fof(f245,plain,(
% 0.20/0.60    v1_funct_1(sK2)),
% 0.20/0.60    inference(backward_demodulation,[],[f196,f234])).
% 0.20/0.60  fof(f246,plain,(
% 0.20/0.60    v1_relat_1(sK2)),
% 0.20/0.60    inference(backward_demodulation,[],[f197,f234])).
% 0.20/0.60  fof(f645,plain,(
% 0.20/0.60    sK0 = k2_relat_1(sK2)),
% 0.20/0.60    inference(unit_resulting_resolution,[],[f246,f245,f555,f631,f46])).
% 0.20/0.60  fof(f631,plain,(
% 0.20/0.60    ( ! [X0] : (~r2_hidden(X0,sK0)) )),
% 0.20/0.60    inference(forward_demodulation,[],[f566,f256])).
% 0.20/0.60  fof(f566,plain,(
% 0.20/0.60    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2))) )),
% 0.20/0.60    inference(unit_resulting_resolution,[],[f555,f78])).
% 0.20/0.60  fof(f78,plain,(
% 0.20/0.60    ( ! [X0,X3] : (sP4(k1_funct_1(X0,X3),X0) | ~r2_hidden(X3,k1_relat_1(X0))) )),
% 0.20/0.60    inference(equality_resolution,[],[f41])).
% 0.20/0.60  fof(f41,plain,(
% 0.20/0.60    ( ! [X2,X0,X3] : (~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | sP4(X2,X0)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f22])).
% 0.20/0.60  fof(f960,plain,(
% 0.20/0.60    k6_partfun1(sK0) = k2_relat_1(sK0)),
% 0.20/0.60    inference(unit_resulting_resolution,[],[f657,f656,f716,f693,f46])).
% 0.20/0.60  fof(f693,plain,(
% 0.20/0.60    ( ! [X0] : (~r2_hidden(X0,k6_partfun1(sK0))) )),
% 0.20/0.60    inference(backward_demodulation,[],[f513,f648])).
% 0.20/0.60  fof(f513,plain,(
% 0.20/0.60    ( ! [X0] : (~r2_hidden(X0,k6_partfun1(sK2))) )),
% 0.20/0.60    inference(unit_resulting_resolution,[],[f441,f180])).
% 0.20/0.60  fof(f441,plain,(
% 0.20/0.60    v1_xboole_0(k6_partfun1(sK2))),
% 0.20/0.60    inference(unit_resulting_resolution,[],[f419,f216])).
% 0.20/0.60  fof(f216,plain,(
% 0.20/0.60    ( ! [X0] : (v1_xboole_0(k6_partfun1(X0)) | ~v1_xboole_0(X0)) )),
% 0.20/0.60    inference(resolution,[],[f51,f38])).
% 0.20/0.60  fof(f38,plain,(
% 0.20/0.60    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.20/0.60    inference(cnf_transformation,[],[f14])).
% 0.20/0.60  fof(f14,axiom,(
% 0.20/0.60    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.20/0.60  fof(f716,plain,(
% 0.20/0.60    ( ! [X0] : (~sP4(X0,sK0)) )),
% 0.20/0.60    inference(backward_demodulation,[],[f555,f648])).
% 0.20/0.60  fof(f656,plain,(
% 0.20/0.60    v1_funct_1(sK0)),
% 0.20/0.60    inference(backward_demodulation,[],[f245,f648])).
% 0.20/0.60  fof(f657,plain,(
% 0.20/0.60    v1_relat_1(sK0)),
% 0.20/0.60    inference(backward_demodulation,[],[f246,f648])).
% 0.20/0.60  fof(f37,plain,(
% 0.20/0.60    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f14])).
% 0.20/0.60  fof(f665,plain,(
% 0.20/0.60    ~v1_partfun1(sK0,sK0)),
% 0.20/0.60    inference(backward_demodulation,[],[f371,f648])).
% 0.20/0.60  % SZS output end Proof for theBenchmark
% 0.20/0.60  % (18444)------------------------------
% 0.20/0.60  % (18444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.60  % (18444)Termination reason: Refutation
% 0.20/0.60  
% 0.20/0.60  % (18444)Memory used [KB]: 7036
% 0.20/0.60  % (18444)Time elapsed: 0.178 s
% 0.20/0.60  % (18444)------------------------------
% 0.20/0.60  % (18444)------------------------------
% 1.90/0.60  % (18419)Success in time 0.247 s
%------------------------------------------------------------------------------
