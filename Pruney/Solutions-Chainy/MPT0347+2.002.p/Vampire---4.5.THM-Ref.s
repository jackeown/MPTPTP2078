%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 748 expanded)
%              Number of leaves         :    6 ( 170 expanded)
%              Depth                    :   20
%              Number of atoms          :  244 (3055 expanded)
%              Number of equality atoms :   50 ( 526 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4780,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4770,f4747])).

fof(f4747,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(resolution,[],[f4729,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f4729,plain,(
    r2_hidden(sK5(sK2,sK3,sK1),sK0) ),
    inference(resolution,[],[f4722,f46])).

fof(f46,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f19,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f19,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k7_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( r2_hidden(X4,X1)
                  <=> ( ~ r2_hidden(X4,X3)
                      & r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k7_subset_1(X0,X2,X3) != X1
              & ! [X4] :
                  ( ( r2_hidden(X4,X1)
                  <=> ( ~ r2_hidden(X4,X3)
                      & r2_hidden(X4,X2) ) )
                  | ~ m1_subset_1(X4,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,X1)
                      <=> ( ~ r2_hidden(X4,X3)
                          & r2_hidden(X4,X2) ) ) )
                 => k7_subset_1(X0,X2,X3) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(X0))
             => ( ! [X4] :
                    ( m1_subset_1(X4,X0)
                   => ( r2_hidden(X4,X1)
                    <=> ( ~ r2_hidden(X4,X3)
                        & r2_hidden(X4,X2) ) ) )
               => k7_subset_1(X0,X2,X3) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_subset_1)).

fof(f4722,plain,(
    r2_hidden(sK5(sK2,sK3,sK1),sK1) ),
    inference(subsumption_resolution,[],[f4712,f137])).

fof(f137,plain,(
    sK1 != k4_xboole_0(sK2,sK3) ),
    inference(superposition,[],[f17,f41])).

fof(f41,plain,(
    ! [X0] : k7_subset_1(sK0,sK2,X0) = k4_xboole_0(sK2,X0) ),
    inference(resolution,[],[f18,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f18,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f17,plain,(
    sK1 != k7_subset_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f4712,plain,
    ( r2_hidden(sK5(sK2,sK3,sK1),sK1)
    | sK1 = k4_xboole_0(sK2,sK3) ),
    inference(factoring,[],[f4228])).

fof(f4228,plain,(
    ! [X1] :
      ( r2_hidden(sK5(sK2,sK3,X1),X1)
      | r2_hidden(sK5(sK2,sK3,X1),sK1)
      | k4_xboole_0(sK2,sK3) = X1 ) ),
    inference(subsumption_resolution,[],[f4227,f594])).

fof(f594,plain,(
    ! [X14,X13] :
      ( ~ v1_xboole_0(sK0)
      | k4_xboole_0(sK2,X13) = X14
      | r2_hidden(sK5(sK2,X13,X14),X14) ) ),
    inference(resolution,[],[f78,f21])).

fof(f78,plain,(
    ! [X12,X11] :
      ( r2_hidden(sK5(sK2,X11,X12),sK0)
      | r2_hidden(sK5(sK2,X11,X12),X12)
      | k4_xboole_0(sK2,X11) = X12 ) ),
    inference(resolution,[],[f42,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f42,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f18,f26])).

fof(f4227,plain,(
    ! [X1] :
      ( r2_hidden(sK5(sK2,sK3,X1),X1)
      | v1_xboole_0(sK0)
      | r2_hidden(sK5(sK2,sK3,X1),sK1)
      | k4_xboole_0(sK2,sK3) = X1 ) ),
    inference(duplicate_literal_removal,[],[f4159])).

fof(f4159,plain,(
    ! [X1] :
      ( r2_hidden(sK5(sK2,sK3,X1),X1)
      | v1_xboole_0(sK0)
      | r2_hidden(sK5(sK2,sK3,X1),sK1)
      | k4_xboole_0(sK2,sK3) = X1
      | r2_hidden(sK5(sK2,sK3,X1),X1)
      | k4_xboole_0(sK2,sK3) = X1 ) ),
    inference(resolution,[],[f212,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f212,plain,(
    ! [X12,X11] :
      ( r2_hidden(sK5(sK2,X11,X12),sK3)
      | r2_hidden(sK5(sK2,X11,X12),X12)
      | v1_xboole_0(sK0)
      | r2_hidden(sK5(sK2,X11,X12),sK1)
      | k4_xboole_0(sK2,X11) = X12 ) ),
    inference(resolution,[],[f143,f29])).

fof(f143,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | r2_hidden(X1,sK3)
      | r2_hidden(X1,sK1)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f142,f42])).

fof(f142,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | r2_hidden(X1,sK3)
      | r2_hidden(X1,sK1)
      | v1_xboole_0(sK0)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f15,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f15,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK0)
      | ~ r2_hidden(X4,sK2)
      | r2_hidden(X4,sK3)
      | r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f4770,plain,(
    v1_xboole_0(sK0) ),
    inference(resolution,[],[f4738,f4726])).

fof(f4726,plain,(
    r2_hidden(sK5(sK2,sK3,sK1),sK2) ),
    inference(resolution,[],[f4722,f1573])).

fof(f1573,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | r2_hidden(X3,sK2) ) ),
    inference(subsumption_resolution,[],[f1570,f1369])).

fof(f1369,plain,(
    ! [X11] : ~ r2_hidden(X11,k4_xboole_0(sK1,sK0)) ),
    inference(backward_demodulation,[],[f1319,f1336])).

fof(f1336,plain,(
    k4_xboole_0(sK3,sK0) = k4_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f1319,f866])).

fof(f866,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK1,sK0,X0),X0)
      | k4_xboole_0(sK1,sK0) = X0 ) ),
    inference(duplicate_literal_removal,[],[f825])).

fof(f825,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK1,sK0,X0),X0)
      | k4_xboole_0(sK1,sK0) = X0
      | r2_hidden(sK5(sK1,sK0,X0),X0)
      | k4_xboole_0(sK1,sK0) = X0 ) ),
    inference(resolution,[],[f90,f30])).

fof(f90,plain,(
    ! [X12,X11] :
      ( r2_hidden(sK5(sK1,X11,X12),sK0)
      | r2_hidden(sK5(sK1,X11,X12),X12)
      | k4_xboole_0(sK1,X11) = X12 ) ),
    inference(resolution,[],[f46,f29])).

fof(f1319,plain,(
    ! [X11] : ~ r2_hidden(X11,k4_xboole_0(sK3,sK0)) ),
    inference(subsumption_resolution,[],[f1308,f1307])).

fof(f1307,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X9,k4_xboole_0(sK3,sK0))
      | ~ r2_hidden(X9,X8) ) ),
    inference(superposition,[],[f35,f1287])).

fof(f1287,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(sK3,sK0) ),
    inference(duplicate_literal_removal,[],[f1275])).

fof(f1275,plain,(
    ! [X0] :
      ( k4_xboole_0(X0,X0) = k4_xboole_0(sK3,sK0)
      | k4_xboole_0(X0,X0) = k4_xboole_0(sK3,sK0) ) ),
    inference(resolution,[],[f434,f433])).

fof(f433,plain,(
    ! [X10,X9] :
      ( r2_hidden(sK5(sK3,sK0,k4_xboole_0(X9,X10)),X9)
      | k4_xboole_0(X9,X10) = k4_xboole_0(sK3,sK0) ) ),
    inference(resolution,[],[f391,f36])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f391,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK3,sK0,X0),X0)
      | k4_xboole_0(sK3,sK0) = X0 ) ),
    inference(duplicate_literal_removal,[],[f356])).

fof(f356,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK3,sK0,X0),X0)
      | k4_xboole_0(sK3,sK0) = X0
      | r2_hidden(sK5(sK3,sK0,X0),X0)
      | k4_xboole_0(sK3,sK0) = X0 ) ),
    inference(resolution,[],[f69,f30])).

fof(f69,plain,(
    ! [X12,X11] :
      ( r2_hidden(sK5(sK3,X11,X12),sK0)
      | r2_hidden(sK5(sK3,X11,X12),X12)
      | k4_xboole_0(sK3,X11) = X12 ) ),
    inference(resolution,[],[f38,f29])).

fof(f38,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK3)
      | r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f16,f26])).

fof(f16,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f434,plain,(
    ! [X12,X11] :
      ( ~ r2_hidden(sK5(sK3,sK0,k4_xboole_0(X11,X12)),X12)
      | k4_xboole_0(X11,X12) = k4_xboole_0(sK3,sK0) ) ),
    inference(resolution,[],[f391,f35])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f1308,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(X11,k4_xboole_0(sK3,sK0))
      | r2_hidden(X11,X10) ) ),
    inference(superposition,[],[f36,f1287])).

fof(f1570,plain,(
    ! [X3] :
      ( r2_hidden(X3,k4_xboole_0(sK1,sK0))
      | ~ r2_hidden(X3,sK1)
      | r2_hidden(X3,sK2) ) ),
    inference(superposition,[],[f34,f1392])).

fof(f1392,plain,(
    k4_xboole_0(sK1,sK0) = k4_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f1337,f1336])).

fof(f1337,plain,(
    k4_xboole_0(sK3,sK0) = k4_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f1319,f1151])).

fof(f1151,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK1,sK2,X0),X0)
      | k4_xboole_0(sK1,sK2) = X0 ) ),
    inference(subsumption_resolution,[],[f1150,f834])).

fof(f834,plain,(
    ! [X14,X13] :
      ( ~ v1_xboole_0(sK0)
      | k4_xboole_0(sK1,X13) = X14
      | r2_hidden(sK5(sK1,X13,X14),X14) ) ),
    inference(resolution,[],[f90,f21])).

fof(f1150,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK1,sK2,X0),X0)
      | v1_xboole_0(sK0)
      | k4_xboole_0(sK1,sK2) = X0 ) ),
    inference(duplicate_literal_removal,[],[f1106])).

% (5218)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f1106,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK1,sK2,X0),X0)
      | v1_xboole_0(sK0)
      | k4_xboole_0(sK1,sK2) = X0
      | r2_hidden(sK5(sK1,sK2,X0),X0)
      | k4_xboole_0(sK1,sK2) = X0 ) ),
    inference(resolution,[],[f151,f30])).

fof(f151,plain,(
    ! [X12,X11] :
      ( r2_hidden(sK5(sK1,X11,X12),sK2)
      | r2_hidden(sK5(sK1,X11,X12),X12)
      | v1_xboole_0(sK0)
      | k4_xboole_0(sK1,X11) = X12 ) ),
    inference(resolution,[],[f82,f29])).

fof(f82,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | r2_hidden(X1,sK2)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f81,f46])).

fof(f81,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK2)
      | ~ r2_hidden(X1,sK1)
      | v1_xboole_0(sK0)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f13,f24])).

fof(f13,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK0)
      | r2_hidden(X4,sK2)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f4738,plain,
    ( ~ r2_hidden(sK5(sK2,sK3,sK1),sK2)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f4737,f137])).

fof(f4737,plain,
    ( v1_xboole_0(sK0)
    | ~ r2_hidden(sK5(sK2,sK3,sK1),sK2)
    | sK1 = k4_xboole_0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f4724,f4722])).

fof(f4724,plain,
    ( v1_xboole_0(sK0)
    | ~ r2_hidden(sK5(sK2,sK3,sK1),sK2)
    | ~ r2_hidden(sK5(sK2,sK3,sK1),sK1)
    | sK1 = k4_xboole_0(sK2,sK3) ),
    inference(resolution,[],[f4722,f172])).

fof(f172,plain,(
    ! [X14,X13] :
      ( ~ r2_hidden(sK5(X13,sK3,X14),sK1)
      | v1_xboole_0(sK0)
      | ~ r2_hidden(sK5(X13,sK3,X14),X13)
      | ~ r2_hidden(sK5(X13,sK3,X14),X14)
      | k4_xboole_0(X13,sK3) = X14 ) ),
    inference(resolution,[],[f121,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(sK5(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f121,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK3)
      | ~ r2_hidden(X1,sK1)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f120,f46])).

fof(f120,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK3)
      | ~ r2_hidden(X1,sK1)
      | v1_xboole_0(sK0)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f14,f24])).

fof(f14,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK0)
      | ~ r2_hidden(X4,sK3)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:52:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (5220)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.46  % (5215)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.47  % (5208)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (5207)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (5211)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (5216)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (5217)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (5212)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (5221)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (5220)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f4780,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f4770,f4747])).
% 0.21/0.50  fof(f4747,plain,(
% 0.21/0.50    ~v1_xboole_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f4729,f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.50  fof(f4729,plain,(
% 0.21/0.50    r2_hidden(sK5(sK2,sK3,sK1),sK0)),
% 0.21/0.50    inference(resolution,[],[f4722,f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X1] : (~r2_hidden(X1,sK1) | r2_hidden(X1,sK0)) )),
% 0.21/0.50    inference(resolution,[],[f19,f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ? [X0,X1] : (? [X2] : (? [X3] : (k7_subset_1(X0,X2,X3) != X1 & ! [X4] : ((r2_hidden(X4,X1) <=> (~r2_hidden(X4,X3) & r2_hidden(X4,X2))) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(flattening,[],[f8])).
% 0.21/0.50  fof(f8,plain,(
% 0.21/0.50    ? [X0,X1] : (? [X2] : (? [X3] : ((k7_subset_1(X0,X2,X3) != X1 & ! [X4] : ((r2_hidden(X4,X1) <=> (~r2_hidden(X4,X3) & r2_hidden(X4,X2))) | ~m1_subset_1(X4,X0))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,X1) <=> (~r2_hidden(X4,X3) & r2_hidden(X4,X2)))) => k7_subset_1(X0,X2,X3) = X1))))),
% 0.21/0.50    inference(negated_conjecture,[],[f6])).
% 0.21/0.50  fof(f6,conjecture,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,X1) <=> (~r2_hidden(X4,X3) & r2_hidden(X4,X2)))) => k7_subset_1(X0,X2,X3) = X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_subset_1)).
% 0.21/0.50  fof(f4722,plain,(
% 0.21/0.50    r2_hidden(sK5(sK2,sK3,sK1),sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f4712,f137])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    sK1 != k4_xboole_0(sK2,sK3)),
% 0.21/0.50    inference(superposition,[],[f17,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0] : (k7_subset_1(sK0,sK2,X0) = k4_xboole_0(sK2,X0)) )),
% 0.21/0.50    inference(resolution,[],[f18,f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    sK1 != k7_subset_1(sK0,sK2,sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f4712,plain,(
% 0.21/0.50    r2_hidden(sK5(sK2,sK3,sK1),sK1) | sK1 = k4_xboole_0(sK2,sK3)),
% 0.21/0.50    inference(factoring,[],[f4228])).
% 0.21/0.50  fof(f4228,plain,(
% 0.21/0.50    ( ! [X1] : (r2_hidden(sK5(sK2,sK3,X1),X1) | r2_hidden(sK5(sK2,sK3,X1),sK1) | k4_xboole_0(sK2,sK3) = X1) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f4227,f594])).
% 0.21/0.50  fof(f594,plain,(
% 0.21/0.50    ( ! [X14,X13] : (~v1_xboole_0(sK0) | k4_xboole_0(sK2,X13) = X14 | r2_hidden(sK5(sK2,X13,X14),X14)) )),
% 0.21/0.50    inference(resolution,[],[f78,f21])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ( ! [X12,X11] : (r2_hidden(sK5(sK2,X11,X12),sK0) | r2_hidden(sK5(sK2,X11,X12),X12) | k4_xboole_0(sK2,X11) = X12) )),
% 0.21/0.50    inference(resolution,[],[f42,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X1] : (~r2_hidden(X1,sK2) | r2_hidden(X1,sK0)) )),
% 0.21/0.50    inference(resolution,[],[f18,f26])).
% 0.21/0.50  fof(f4227,plain,(
% 0.21/0.50    ( ! [X1] : (r2_hidden(sK5(sK2,sK3,X1),X1) | v1_xboole_0(sK0) | r2_hidden(sK5(sK2,sK3,X1),sK1) | k4_xboole_0(sK2,sK3) = X1) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f4159])).
% 0.21/0.50  fof(f4159,plain,(
% 0.21/0.50    ( ! [X1] : (r2_hidden(sK5(sK2,sK3,X1),X1) | v1_xboole_0(sK0) | r2_hidden(sK5(sK2,sK3,X1),sK1) | k4_xboole_0(sK2,sK3) = X1 | r2_hidden(sK5(sK2,sK3,X1),X1) | k4_xboole_0(sK2,sK3) = X1) )),
% 0.21/0.50    inference(resolution,[],[f212,f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f212,plain,(
% 0.21/0.50    ( ! [X12,X11] : (r2_hidden(sK5(sK2,X11,X12),sK3) | r2_hidden(sK5(sK2,X11,X12),X12) | v1_xboole_0(sK0) | r2_hidden(sK5(sK2,X11,X12),sK1) | k4_xboole_0(sK2,X11) = X12) )),
% 0.21/0.50    inference(resolution,[],[f143,f29])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    ( ! [X1] : (~r2_hidden(X1,sK2) | r2_hidden(X1,sK3) | r2_hidden(X1,sK1) | v1_xboole_0(sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f142,f42])).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    ( ! [X1] : (~r2_hidden(X1,sK2) | r2_hidden(X1,sK3) | r2_hidden(X1,sK1) | v1_xboole_0(sK0) | ~r2_hidden(X1,sK0)) )),
% 0.21/0.50    inference(resolution,[],[f15,f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ( ! [X4] : (~m1_subset_1(X4,sK0) | ~r2_hidden(X4,sK2) | r2_hidden(X4,sK3) | r2_hidden(X4,sK1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f4770,plain,(
% 0.21/0.50    v1_xboole_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f4738,f4726])).
% 0.21/0.50  fof(f4726,plain,(
% 0.21/0.50    r2_hidden(sK5(sK2,sK3,sK1),sK2)),
% 0.21/0.50    inference(resolution,[],[f4722,f1573])).
% 0.21/0.50  fof(f1573,plain,(
% 0.21/0.50    ( ! [X3] : (~r2_hidden(X3,sK1) | r2_hidden(X3,sK2)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f1570,f1369])).
% 0.21/0.50  fof(f1369,plain,(
% 0.21/0.50    ( ! [X11] : (~r2_hidden(X11,k4_xboole_0(sK1,sK0))) )),
% 0.21/0.50    inference(backward_demodulation,[],[f1319,f1336])).
% 0.21/0.50  fof(f1336,plain,(
% 0.21/0.50    k4_xboole_0(sK3,sK0) = k4_xboole_0(sK1,sK0)),
% 0.21/0.50    inference(resolution,[],[f1319,f866])).
% 0.21/0.50  fof(f866,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK5(sK1,sK0,X0),X0) | k4_xboole_0(sK1,sK0) = X0) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f825])).
% 0.21/0.50  fof(f825,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK5(sK1,sK0,X0),X0) | k4_xboole_0(sK1,sK0) = X0 | r2_hidden(sK5(sK1,sK0,X0),X0) | k4_xboole_0(sK1,sK0) = X0) )),
% 0.21/0.50    inference(resolution,[],[f90,f30])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    ( ! [X12,X11] : (r2_hidden(sK5(sK1,X11,X12),sK0) | r2_hidden(sK5(sK1,X11,X12),X12) | k4_xboole_0(sK1,X11) = X12) )),
% 0.21/0.50    inference(resolution,[],[f46,f29])).
% 0.21/0.50  fof(f1319,plain,(
% 0.21/0.50    ( ! [X11] : (~r2_hidden(X11,k4_xboole_0(sK3,sK0))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f1308,f1307])).
% 0.21/0.50  fof(f1307,plain,(
% 0.21/0.50    ( ! [X8,X9] : (~r2_hidden(X9,k4_xboole_0(sK3,sK0)) | ~r2_hidden(X9,X8)) )),
% 0.21/0.50    inference(superposition,[],[f35,f1287])).
% 0.21/0.50  fof(f1287,plain,(
% 0.21/0.50    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(sK3,sK0)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f1275])).
% 0.21/0.50  fof(f1275,plain,(
% 0.21/0.50    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(sK3,sK0) | k4_xboole_0(X0,X0) = k4_xboole_0(sK3,sK0)) )),
% 0.21/0.50    inference(resolution,[],[f434,f433])).
% 0.21/0.50  fof(f433,plain,(
% 0.21/0.50    ( ! [X10,X9] : (r2_hidden(sK5(sK3,sK0,k4_xboole_0(X9,X10)),X9) | k4_xboole_0(X9,X10) = k4_xboole_0(sK3,sK0)) )),
% 0.21/0.50    inference(resolution,[],[f391,f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(equality_resolution,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f391,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK5(sK3,sK0,X0),X0) | k4_xboole_0(sK3,sK0) = X0) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f356])).
% 0.21/0.50  fof(f356,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK5(sK3,sK0,X0),X0) | k4_xboole_0(sK3,sK0) = X0 | r2_hidden(sK5(sK3,sK0,X0),X0) | k4_xboole_0(sK3,sK0) = X0) )),
% 0.21/0.50    inference(resolution,[],[f69,f30])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X12,X11] : (r2_hidden(sK5(sK3,X11,X12),sK0) | r2_hidden(sK5(sK3,X11,X12),X12) | k4_xboole_0(sK3,X11) = X12) )),
% 0.21/0.50    inference(resolution,[],[f38,f29])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X1] : (~r2_hidden(X1,sK3) | r2_hidden(X1,sK0)) )),
% 0.21/0.50    inference(resolution,[],[f16,f26])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f434,plain,(
% 0.21/0.50    ( ! [X12,X11] : (~r2_hidden(sK5(sK3,sK0,k4_xboole_0(X11,X12)),X12) | k4_xboole_0(X11,X12) = k4_xboole_0(sK3,sK0)) )),
% 0.21/0.50    inference(resolution,[],[f391,f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(equality_resolution,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f1308,plain,(
% 0.21/0.50    ( ! [X10,X11] : (~r2_hidden(X11,k4_xboole_0(sK3,sK0)) | r2_hidden(X11,X10)) )),
% 0.21/0.50    inference(superposition,[],[f36,f1287])).
% 0.21/0.50  fof(f1570,plain,(
% 0.21/0.50    ( ! [X3] : (r2_hidden(X3,k4_xboole_0(sK1,sK0)) | ~r2_hidden(X3,sK1) | r2_hidden(X3,sK2)) )),
% 0.21/0.50    inference(superposition,[],[f34,f1392])).
% 0.21/0.50  fof(f1392,plain,(
% 0.21/0.50    k4_xboole_0(sK1,sK0) = k4_xboole_0(sK1,sK2)),
% 0.21/0.50    inference(forward_demodulation,[],[f1337,f1336])).
% 0.21/0.50  fof(f1337,plain,(
% 0.21/0.50    k4_xboole_0(sK3,sK0) = k4_xboole_0(sK1,sK2)),
% 0.21/0.50    inference(resolution,[],[f1319,f1151])).
% 0.21/0.50  fof(f1151,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK5(sK1,sK2,X0),X0) | k4_xboole_0(sK1,sK2) = X0) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f1150,f834])).
% 0.21/0.50  fof(f834,plain,(
% 0.21/0.50    ( ! [X14,X13] : (~v1_xboole_0(sK0) | k4_xboole_0(sK1,X13) = X14 | r2_hidden(sK5(sK1,X13,X14),X14)) )),
% 0.21/0.50    inference(resolution,[],[f90,f21])).
% 0.21/0.50  fof(f1150,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK5(sK1,sK2,X0),X0) | v1_xboole_0(sK0) | k4_xboole_0(sK1,sK2) = X0) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f1106])).
% 0.21/0.50  % (5218)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  fof(f1106,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK5(sK1,sK2,X0),X0) | v1_xboole_0(sK0) | k4_xboole_0(sK1,sK2) = X0 | r2_hidden(sK5(sK1,sK2,X0),X0) | k4_xboole_0(sK1,sK2) = X0) )),
% 0.21/0.50    inference(resolution,[],[f151,f30])).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    ( ! [X12,X11] : (r2_hidden(sK5(sK1,X11,X12),sK2) | r2_hidden(sK5(sK1,X11,X12),X12) | v1_xboole_0(sK0) | k4_xboole_0(sK1,X11) = X12) )),
% 0.21/0.50    inference(resolution,[],[f82,f29])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ( ! [X1] : (~r2_hidden(X1,sK1) | r2_hidden(X1,sK2) | v1_xboole_0(sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f81,f46])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ( ! [X1] : (r2_hidden(X1,sK2) | ~r2_hidden(X1,sK1) | v1_xboole_0(sK0) | ~r2_hidden(X1,sK0)) )),
% 0.21/0.50    inference(resolution,[],[f13,f24])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ( ! [X4] : (~m1_subset_1(X4,sK0) | r2_hidden(X4,sK2) | ~r2_hidden(X4,sK1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(equality_resolution,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f4738,plain,(
% 0.21/0.50    ~r2_hidden(sK5(sK2,sK3,sK1),sK2) | v1_xboole_0(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f4737,f137])).
% 0.21/0.50  fof(f4737,plain,(
% 0.21/0.50    v1_xboole_0(sK0) | ~r2_hidden(sK5(sK2,sK3,sK1),sK2) | sK1 = k4_xboole_0(sK2,sK3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f4724,f4722])).
% 0.21/0.50  fof(f4724,plain,(
% 0.21/0.50    v1_xboole_0(sK0) | ~r2_hidden(sK5(sK2,sK3,sK1),sK2) | ~r2_hidden(sK5(sK2,sK3,sK1),sK1) | sK1 = k4_xboole_0(sK2,sK3)),
% 0.21/0.50    inference(resolution,[],[f4722,f172])).
% 0.21/0.50  fof(f172,plain,(
% 0.21/0.50    ( ! [X14,X13] : (~r2_hidden(sK5(X13,sK3,X14),sK1) | v1_xboole_0(sK0) | ~r2_hidden(sK5(X13,sK3,X14),X13) | ~r2_hidden(sK5(X13,sK3,X14),X14) | k4_xboole_0(X13,sK3) = X14) )),
% 0.21/0.50    inference(resolution,[],[f121,f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    ( ! [X1] : (~r2_hidden(X1,sK3) | ~r2_hidden(X1,sK1) | v1_xboole_0(sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f120,f46])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    ( ! [X1] : (~r2_hidden(X1,sK3) | ~r2_hidden(X1,sK1) | v1_xboole_0(sK0) | ~r2_hidden(X1,sK0)) )),
% 0.21/0.50    inference(resolution,[],[f14,f24])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ( ! [X4] : (~m1_subset_1(X4,sK0) | ~r2_hidden(X4,sK3) | ~r2_hidden(X4,sK1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (5220)------------------------------
% 0.21/0.50  % (5220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (5220)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (5220)Memory used [KB]: 2942
% 0.21/0.50  % (5220)Time elapsed: 0.068 s
% 0.21/0.50  % (5220)------------------------------
% 0.21/0.50  % (5220)------------------------------
% 0.21/0.50  % (5206)Success in time 0.144 s
%------------------------------------------------------------------------------
