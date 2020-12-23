%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:32 EST 2020

% Result     : Theorem 1.90s
% Output     : Refutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :  169 (2710 expanded)
%              Number of leaves         :   29 ( 712 expanded)
%              Depth                    :   23
%              Number of atoms          :  456 (9109 expanded)
%              Number of equality atoms :   77 ( 440 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1449,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f177,f345,f349,f639,f647,f707,f1448])).

fof(f1448,plain,
    ( ~ spl7_1
    | spl7_3
    | ~ spl7_10 ),
    inference(avatar_contradiction_clause,[],[f1446])).

fof(f1446,plain,
    ( $false
    | ~ spl7_1
    | spl7_3
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f61,f1362,f548,f458,f1381,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f1381,plain,
    ( ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl7_1
    | spl7_3
    | ~ spl7_10 ),
    inference(backward_demodulation,[],[f1328,f1367])).

fof(f1367,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_1
    | spl7_3
    | ~ spl7_10 ),
    inference(forward_demodulation,[],[f1331,f510])).

fof(f510,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f477,f505])).

fof(f505,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f422,f473,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f473,plain,(
    ! [X0] : r1_tarski(k7_relat_1(k1_xboole_0,X0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f464,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f464,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f422,f284])).

fof(f284,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ r1_tarski(X0,sK4) ) ),
    inference(resolution,[],[f151,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f151,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(sK4))
      | v1_relat_1(X2) ) ),
    inference(resolution,[],[f130,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f130,plain,(
    v1_relat_1(sK4) ),
    inference(unit_resulting_resolution,[],[f76,f58,f75])).

fof(f58,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          & r1_tarski(X1,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(X3) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          & r1_tarski(X1,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(X3) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ~ v1_xboole_0(X3)
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
              & v1_funct_2(X4,X0,X3)
              & v1_funct_1(X4) )
           => ( ( r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
                & r1_tarski(X1,X0) )
             => ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
                & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
            & v1_funct_2(X4,X0,X3)
            & v1_funct_1(X4) )
         => ( ( r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
              & r1_tarski(X1,X0) )
           => ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
              & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_funct_2)).

fof(f76,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f422,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f419,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
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

fof(f419,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f408,f273])).

fof(f273,plain,(
    k1_xboole_0 = k1_relat_1(k7_relat_1(sK4,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f147,f92])).

fof(f92,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f147,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),X0) ),
    inference(unit_resulting_resolution,[],[f130,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f408,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK4,k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f89,f270,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f270,plain,(
    ! [X0] : m1_subset_1(k1_relat_1(k7_relat_1(sK4,X0)),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f147,f66])).

fof(f89,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f477,plain,(
    k1_xboole_0 = k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f422,f464,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f1331,plain,
    ( sK1 = k1_relat_1(k1_xboole_0)
    | ~ spl7_1
    | spl7_3
    | ~ spl7_10 ),
    inference(backward_demodulation,[],[f1124,f1327])).

fof(f1327,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK1)
    | ~ spl7_1
    | spl7_3
    | ~ spl7_10 ),
    inference(forward_demodulation,[],[f1326,f510])).

fof(f1326,plain,
    ( k7_relat_1(sK4,sK1) = k1_relat_1(k1_xboole_0)
    | ~ spl7_1
    | spl7_3
    | ~ spl7_10 ),
    inference(forward_demodulation,[],[f1308,f505])).

fof(f1308,plain,
    ( k7_relat_1(sK4,sK1) = k1_relat_1(k7_relat_1(k1_xboole_0,k7_relat_1(sK4,sK1)))
    | ~ spl7_1
    | spl7_3
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f464,f1271,f71])).

fof(f1271,plain,
    ( ! [X0] : r1_tarski(k7_relat_1(sK4,sK1),X0)
    | ~ spl7_1
    | spl7_3
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f1257,f94])).

fof(f1257,plain,
    ( ! [X0] : ~ r2_hidden(X0,k7_relat_1(sK4,sK1))
    | ~ spl7_1
    | spl7_3
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f1234,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f1234,plain,
    ( v1_xboole_0(k7_relat_1(sK4,sK1))
    | ~ spl7_1
    | spl7_3
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f89,f1155,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f1155,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ spl7_1
    | spl7_3
    | ~ spl7_10 ),
    inference(backward_demodulation,[],[f167,f1150])).

fof(f1150,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_1
    | spl7_3
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f176,f167,f1135,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f1135,plain,
    ( sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | ~ spl7_1
    | ~ spl7_10 ),
    inference(backward_demodulation,[],[f370,f1124])).

fof(f370,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK1)) = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | ~ spl7_1 ),
    inference(unit_resulting_resolution,[],[f167,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f176,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl7_3
  <=> v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f167,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl7_1
  <=> m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f1124,plain,
    ( sK1 = k1_relat_1(k7_relat_1(sK4,sK1))
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f59,f709])).

fof(f709,plain,
    ( ! [X5] :
        ( ~ r1_tarski(X5,sK0)
        | k1_relat_1(k7_relat_1(sK4,X5)) = X5 )
    | ~ spl7_10 ),
    inference(backward_demodulation,[],[f154,f638])).

fof(f638,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f636])).

fof(f636,plain,
    ( spl7_10
  <=> sK0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f154,plain,(
    ! [X5] :
      ( ~ r1_tarski(X5,k1_relat_1(sK4))
      | k1_relat_1(k7_relat_1(sK4,X5)) = X5 ) ),
    inference(resolution,[],[f130,f71])).

fof(f59,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f1328,plain,
    ( ~ v1_partfun1(k1_xboole_0,sK1)
    | ~ spl7_1
    | spl7_3
    | ~ spl7_10 ),
    inference(backward_demodulation,[],[f369,f1327])).

fof(f369,plain,
    ( ~ v1_partfun1(k7_relat_1(sK4,sK1),sK1)
    | ~ spl7_1
    | spl7_3 ),
    inference(unit_resulting_resolution,[],[f140,f176,f167,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f140,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK4,X0)) ),
    inference(forward_demodulation,[],[f123,f125])).

fof(f125,plain,(
    ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK0,sK3,sK4,X0) ),
    inference(unit_resulting_resolution,[],[f56,f58,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f56,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f29])).

fof(f123,plain,(
    ! [X0] : v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0)) ),
    inference(unit_resulting_resolution,[],[f56,f58,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f458,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f422,f66])).

fof(f548,plain,(
    ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f458,f517,f100])).

fof(f100,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f517,plain,(
    ! [X0,X1] : k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f491,f510])).

fof(f491,plain,(
    ! [X0,X1] : k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f458,f91])).

fof(f1362,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl7_1
    | spl7_3
    | ~ spl7_10 ),
    inference(forward_demodulation,[],[f1329,f505])).

fof(f1329,plain,
    ( ! [X0] : v1_funct_1(k7_relat_1(k1_xboole_0,X0))
    | ~ spl7_1
    | spl7_3
    | ~ spl7_10 ),
    inference(backward_demodulation,[],[f376,f1327])).

fof(f376,plain,
    ( ! [X0] : v1_funct_1(k7_relat_1(k7_relat_1(sK4,sK1),X0))
    | ~ spl7_1 ),
    inference(forward_demodulation,[],[f364,f366])).

fof(f366,plain,
    ( ! [X0] : k2_partfun1(sK1,sK2,k7_relat_1(sK4,sK1),X0) = k7_relat_1(k7_relat_1(sK4,sK1),X0)
    | ~ spl7_1 ),
    inference(unit_resulting_resolution,[],[f140,f167,f64])).

fof(f364,plain,
    ( ! [X0] : v1_funct_1(k2_partfun1(sK1,sK2,k7_relat_1(sK4,sK1),X0))
    | ~ spl7_1 ),
    inference(unit_resulting_resolution,[],[f140,f167,f62])).

fof(f61,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f707,plain,(
    ~ spl7_9 ),
    inference(avatar_contradiction_clause,[],[f699])).

fof(f699,plain,
    ( $false
    | ~ spl7_9 ),
    inference(unit_resulting_resolution,[],[f89,f458,f650,f86])).

fof(f650,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_9 ),
    inference(backward_demodulation,[],[f61,f634])).

fof(f634,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f632])).

fof(f632,plain,
    ( spl7_9
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f647,plain,(
    spl7_8 ),
    inference(avatar_contradiction_clause,[],[f642])).

fof(f642,plain,
    ( $false
    | spl7_8 ),
    inference(unit_resulting_resolution,[],[f131,f630,f66])).

fof(f630,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | spl7_8 ),
    inference(avatar_component_clause,[],[f628])).

fof(f628,plain,
    ( spl7_8
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f131,plain,(
    r1_tarski(sK4,k2_zfmisc_1(sK0,sK3)) ),
    inference(unit_resulting_resolution,[],[f58,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f639,plain,
    ( ~ spl7_8
    | spl7_9
    | spl7_10 ),
    inference(avatar_split_clause,[],[f134,f636,f632,f628])).

fof(f134,plain,
    ( sK0 = k1_relat_1(sK4)
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(backward_demodulation,[],[f112,f129])).

fof(f129,plain,(
    k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4) ),
    inference(unit_resulting_resolution,[],[f58,f91])).

fof(f112,plain,
    ( k1_xboole_0 = sK3
    | sK0 = k1_relset_1(sK0,sK3,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(resolution,[],[f57,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f57,plain,(
    v1_funct_2(sK4,sK0,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f349,plain,(
    spl7_2 ),
    inference(avatar_contradiction_clause,[],[f346])).

fof(f346,plain,
    ( $false
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f140,f172])).

fof(f172,plain,
    ( ~ v1_funct_1(k7_relat_1(sK4,sK1))
    | spl7_2 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl7_2
  <=> v1_funct_1(k7_relat_1(sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f345,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f339])).

fof(f339,plain,
    ( $false
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f163,f312,f67])).

fof(f312,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,sK1),sK2)
    | spl7_1 ),
    inference(forward_demodulation,[],[f300,f145])).

fof(f145,plain,(
    ! [X0] : k9_relat_1(sK4,X0) = k2_relat_1(k7_relat_1(sK4,X0)) ),
    inference(unit_resulting_resolution,[],[f130,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f300,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2)
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f147,f168,f288,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f288,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK4,X0)) ),
    inference(unit_resulting_resolution,[],[f146,f284])).

fof(f146,plain,(
    ! [X0] : r1_tarski(k7_relat_1(sK4,X0),sK4) ),
    inference(unit_resulting_resolution,[],[f130,f73])).

fof(f168,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f166])).

fof(f163,plain,(
    m1_subset_1(k9_relat_1(sK4,sK1),k1_zfmisc_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f135,f66])).

fof(f135,plain,(
    r1_tarski(k9_relat_1(sK4,sK1),sK2) ),
    inference(backward_demodulation,[],[f60,f126])).

fof(f126,plain,(
    ! [X0] : k7_relset_1(sK0,sK3,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(unit_resulting_resolution,[],[f58,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f60,plain,(
    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f177,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f138,f174,f170,f166])).

fof(f138,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | ~ v1_funct_1(k7_relat_1(sK4,sK1))
    | ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(forward_demodulation,[],[f137,f125])).

fof(f137,plain,
    ( ~ v1_funct_1(k7_relat_1(sK4,sK1))
    | ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) ),
    inference(forward_demodulation,[],[f136,f125])).

fof(f136,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) ),
    inference(backward_demodulation,[],[f55,f125])).

fof(f55,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:16:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (20490)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (20496)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (20512)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (20518)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (20515)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.53  % (20491)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (20494)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (20513)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (20495)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (20505)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (20512)Refutation not found, incomplete strategy% (20512)------------------------------
% 0.22/0.54  % (20512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (20507)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (20492)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (20500)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (20499)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (20510)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (20504)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (20501)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (20502)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (20497)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (20519)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (20498)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (20512)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (20512)Memory used [KB]: 11001
% 0.22/0.55  % (20512)Time elapsed: 0.129 s
% 0.22/0.55  % (20512)------------------------------
% 0.22/0.55  % (20512)------------------------------
% 0.22/0.55  % (20509)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (20511)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (20503)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (20516)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (20517)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.56  % (20514)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.56  % (20506)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.56  % (20508)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.56  % (20493)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.90/0.62  % (20494)Refutation found. Thanks to Tanya!
% 1.90/0.62  % SZS status Theorem for theBenchmark
% 1.90/0.62  % SZS output start Proof for theBenchmark
% 1.90/0.62  fof(f1449,plain,(
% 1.90/0.62    $false),
% 1.90/0.62    inference(avatar_sat_refutation,[],[f177,f345,f349,f639,f647,f707,f1448])).
% 1.90/0.62  fof(f1448,plain,(
% 1.90/0.62    ~spl7_1 | spl7_3 | ~spl7_10),
% 1.90/0.62    inference(avatar_contradiction_clause,[],[f1446])).
% 1.90/0.62  fof(f1446,plain,(
% 1.90/0.62    $false | (~spl7_1 | spl7_3 | ~spl7_10)),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f61,f1362,f548,f458,f1381,f84])).
% 1.90/0.62  fof(f84,plain,(
% 1.90/0.62    ( ! [X2,X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f46])).
% 1.90/0.62  fof(f46,plain,(
% 1.90/0.62    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.90/0.62    inference(flattening,[],[f45])).
% 1.90/0.62  fof(f45,plain,(
% 1.90/0.62    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.90/0.62    inference(ennf_transformation,[],[f22])).
% 1.90/0.62  fof(f22,axiom,(
% 1.90/0.62    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 1.90/0.62  fof(f1381,plain,(
% 1.90/0.62    ~v1_partfun1(k1_xboole_0,k1_xboole_0) | (~spl7_1 | spl7_3 | ~spl7_10)),
% 1.90/0.62    inference(backward_demodulation,[],[f1328,f1367])).
% 1.90/0.62  fof(f1367,plain,(
% 1.90/0.62    k1_xboole_0 = sK1 | (~spl7_1 | spl7_3 | ~spl7_10)),
% 1.90/0.62    inference(forward_demodulation,[],[f1331,f510])).
% 1.90/0.62  fof(f510,plain,(
% 1.90/0.62    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.90/0.62    inference(backward_demodulation,[],[f477,f505])).
% 1.90/0.62  fof(f505,plain,(
% 1.90/0.62    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f422,f473,f70])).
% 1.90/0.62  fof(f70,plain,(
% 1.90/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.90/0.62    inference(cnf_transformation,[],[f4])).
% 1.90/0.62  fof(f4,axiom,(
% 1.90/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.90/0.62  fof(f473,plain,(
% 1.90/0.62    ( ! [X0] : (r1_tarski(k7_relat_1(k1_xboole_0,X0),k1_xboole_0)) )),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f464,f73])).
% 1.90/0.62  fof(f73,plain,(
% 1.90/0.62    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k7_relat_1(X1,X0),X1)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f38])).
% 1.90/0.62  fof(f38,plain,(
% 1.90/0.62    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 1.90/0.62    inference(ennf_transformation,[],[f13])).
% 1.90/0.62  fof(f13,axiom,(
% 1.90/0.62    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 1.90/0.62  fof(f464,plain,(
% 1.90/0.62    v1_relat_1(k1_xboole_0)),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f422,f284])).
% 1.90/0.62  fof(f284,plain,(
% 1.90/0.62    ( ! [X0] : (v1_relat_1(X0) | ~r1_tarski(X0,sK4)) )),
% 1.90/0.62    inference(resolution,[],[f151,f66])).
% 1.90/0.62  fof(f66,plain,(
% 1.90/0.62    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f6])).
% 1.90/0.62  fof(f6,axiom,(
% 1.90/0.62    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.90/0.62  fof(f151,plain,(
% 1.90/0.62    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(sK4)) | v1_relat_1(X2)) )),
% 1.90/0.62    inference(resolution,[],[f130,f75])).
% 1.90/0.62  fof(f75,plain,(
% 1.90/0.62    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f40])).
% 1.90/0.62  fof(f40,plain,(
% 1.90/0.62    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.90/0.62    inference(ennf_transformation,[],[f8])).
% 1.90/0.62  fof(f8,axiom,(
% 1.90/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.90/0.62  fof(f130,plain,(
% 1.90/0.62    v1_relat_1(sK4)),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f76,f58,f75])).
% 1.90/0.62  fof(f58,plain,(
% 1.90/0.62    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 1.90/0.62    inference(cnf_transformation,[],[f29])).
% 1.90/0.62  fof(f29,plain,(
% 1.90/0.62    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3))),
% 1.90/0.62    inference(flattening,[],[f28])).
% 1.90/0.62  fof(f28,plain,(
% 1.90/0.62    ? [X0,X1,X2,X3] : (? [X4] : (((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & (r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4))) & ~v1_xboole_0(X3))),
% 1.90/0.62    inference(ennf_transformation,[],[f27])).
% 1.90/0.62  fof(f27,negated_conjecture,(
% 1.90/0.62    ~! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 1.90/0.62    inference(negated_conjecture,[],[f26])).
% 1.90/0.62  fof(f26,conjecture,(
% 1.90/0.62    ! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_funct_2)).
% 1.90/0.62  fof(f76,plain,(
% 1.90/0.62    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.90/0.62    inference(cnf_transformation,[],[f10])).
% 1.90/0.62  fof(f10,axiom,(
% 1.90/0.62    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.90/0.62  fof(f422,plain,(
% 1.90/0.62    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f419,f94])).
% 1.90/0.62  fof(f94,plain,(
% 1.90/0.62    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK6(X0,X1),X0)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f52])).
% 1.90/0.62  fof(f52,plain,(
% 1.90/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.90/0.62    inference(ennf_transformation,[],[f2])).
% 1.90/0.62  fof(f2,axiom,(
% 1.90/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.90/0.62  fof(f419,plain,(
% 1.90/0.62    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.90/0.62    inference(forward_demodulation,[],[f408,f273])).
% 1.90/0.62  fof(f273,plain,(
% 1.90/0.62    k1_xboole_0 = k1_relat_1(k7_relat_1(sK4,k1_xboole_0))),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f147,f92])).
% 1.90/0.62  fof(f92,plain,(
% 1.90/0.62    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.90/0.62    inference(cnf_transformation,[],[f51])).
% 1.90/0.62  fof(f51,plain,(
% 1.90/0.62    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.90/0.62    inference(ennf_transformation,[],[f5])).
% 1.90/0.62  fof(f5,axiom,(
% 1.90/0.62    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.90/0.62  fof(f147,plain,(
% 1.90/0.62    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),X0)) )),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f130,f72])).
% 1.90/0.62  fof(f72,plain,(
% 1.90/0.62    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f37])).
% 1.90/0.62  fof(f37,plain,(
% 1.90/0.62    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.90/0.62    inference(ennf_transformation,[],[f12])).
% 1.90/0.62  fof(f12,axiom,(
% 1.90/0.62    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 1.90/0.62  fof(f408,plain,(
% 1.90/0.62    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(sK4,k1_xboole_0)))) )),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f89,f270,f85])).
% 1.90/0.62  fof(f85,plain,(
% 1.90/0.62    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f47])).
% 1.90/0.62  fof(f47,plain,(
% 1.90/0.62    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.90/0.62    inference(ennf_transformation,[],[f7])).
% 1.90/0.62  fof(f7,axiom,(
% 1.90/0.62    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.90/0.62  fof(f270,plain,(
% 1.90/0.62    ( ! [X0] : (m1_subset_1(k1_relat_1(k7_relat_1(sK4,X0)),k1_zfmisc_1(X0))) )),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f147,f66])).
% 1.90/0.62  fof(f89,plain,(
% 1.90/0.62    v1_xboole_0(k1_xboole_0)),
% 1.90/0.62    inference(cnf_transformation,[],[f3])).
% 1.90/0.62  fof(f3,axiom,(
% 1.90/0.62    v1_xboole_0(k1_xboole_0)),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.90/0.62  fof(f477,plain,(
% 1.90/0.62    k1_xboole_0 = k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0))),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f422,f464,f71])).
% 1.90/0.62  fof(f71,plain,(
% 1.90/0.62    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 1.90/0.62    inference(cnf_transformation,[],[f36])).
% 1.90/0.62  fof(f36,plain,(
% 1.90/0.62    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.90/0.62    inference(flattening,[],[f35])).
% 1.90/0.62  fof(f35,plain,(
% 1.90/0.62    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.90/0.62    inference(ennf_transformation,[],[f14])).
% 1.90/0.62  fof(f14,axiom,(
% 1.90/0.62    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 1.90/0.62  fof(f1331,plain,(
% 1.90/0.62    sK1 = k1_relat_1(k1_xboole_0) | (~spl7_1 | spl7_3 | ~spl7_10)),
% 1.90/0.62    inference(backward_demodulation,[],[f1124,f1327])).
% 1.90/0.62  fof(f1327,plain,(
% 1.90/0.62    k1_xboole_0 = k7_relat_1(sK4,sK1) | (~spl7_1 | spl7_3 | ~spl7_10)),
% 1.90/0.62    inference(forward_demodulation,[],[f1326,f510])).
% 1.90/0.62  fof(f1326,plain,(
% 1.90/0.62    k7_relat_1(sK4,sK1) = k1_relat_1(k1_xboole_0) | (~spl7_1 | spl7_3 | ~spl7_10)),
% 1.90/0.62    inference(forward_demodulation,[],[f1308,f505])).
% 1.90/0.62  fof(f1308,plain,(
% 1.90/0.62    k7_relat_1(sK4,sK1) = k1_relat_1(k7_relat_1(k1_xboole_0,k7_relat_1(sK4,sK1))) | (~spl7_1 | spl7_3 | ~spl7_10)),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f464,f1271,f71])).
% 1.90/0.62  fof(f1271,plain,(
% 1.90/0.62    ( ! [X0] : (r1_tarski(k7_relat_1(sK4,sK1),X0)) ) | (~spl7_1 | spl7_3 | ~spl7_10)),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f1257,f94])).
% 1.90/0.62  fof(f1257,plain,(
% 1.90/0.62    ( ! [X0] : (~r2_hidden(X0,k7_relat_1(sK4,sK1))) ) | (~spl7_1 | spl7_3 | ~spl7_10)),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f1234,f88])).
% 1.90/0.62  fof(f88,plain,(
% 1.90/0.62    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f1])).
% 1.90/0.62  fof(f1,axiom,(
% 1.90/0.62    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.90/0.62  fof(f1234,plain,(
% 1.90/0.62    v1_xboole_0(k7_relat_1(sK4,sK1)) | (~spl7_1 | spl7_3 | ~spl7_10)),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f89,f1155,f86])).
% 1.90/0.62  fof(f86,plain,(
% 1.90/0.62    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f48])).
% 1.90/0.62  fof(f48,plain,(
% 1.90/0.62    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 1.90/0.62    inference(ennf_transformation,[],[f17])).
% 1.90/0.62  fof(f17,axiom,(
% 1.90/0.62    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 1.90/0.62  fof(f1155,plain,(
% 1.90/0.62    m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | (~spl7_1 | spl7_3 | ~spl7_10)),
% 1.90/0.62    inference(backward_demodulation,[],[f167,f1150])).
% 1.90/0.62  fof(f1150,plain,(
% 1.90/0.62    k1_xboole_0 = sK2 | (~spl7_1 | spl7_3 | ~spl7_10)),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f176,f167,f1135,f82])).
% 1.90/0.62  fof(f82,plain,(
% 1.90/0.62    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(X2,X0,X1)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f44])).
% 1.90/0.62  fof(f44,plain,(
% 1.90/0.62    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.90/0.62    inference(flattening,[],[f43])).
% 1.90/0.62  fof(f43,plain,(
% 1.90/0.62    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.90/0.62    inference(ennf_transformation,[],[f23])).
% 1.90/0.62  fof(f23,axiom,(
% 1.90/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.90/0.62  fof(f1135,plain,(
% 1.90/0.62    sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | (~spl7_1 | ~spl7_10)),
% 1.90/0.62    inference(backward_demodulation,[],[f370,f1124])).
% 1.90/0.62  fof(f370,plain,(
% 1.90/0.62    k1_relat_1(k7_relat_1(sK4,sK1)) = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | ~spl7_1),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f167,f91])).
% 1.90/0.62  fof(f91,plain,(
% 1.90/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f50])).
% 1.90/0.62  fof(f50,plain,(
% 1.90/0.62    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.90/0.62    inference(ennf_transformation,[],[f18])).
% 1.90/0.62  fof(f18,axiom,(
% 1.90/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.90/0.62  fof(f176,plain,(
% 1.90/0.62    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | spl7_3),
% 1.90/0.62    inference(avatar_component_clause,[],[f174])).
% 1.90/0.62  fof(f174,plain,(
% 1.90/0.62    spl7_3 <=> v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.90/0.62  fof(f167,plain,(
% 1.90/0.62    m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl7_1),
% 1.90/0.62    inference(avatar_component_clause,[],[f166])).
% 1.90/0.62  fof(f166,plain,(
% 1.90/0.62    spl7_1 <=> m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.90/0.62  fof(f1124,plain,(
% 1.90/0.62    sK1 = k1_relat_1(k7_relat_1(sK4,sK1)) | ~spl7_10),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f59,f709])).
% 1.90/0.62  fof(f709,plain,(
% 1.90/0.62    ( ! [X5] : (~r1_tarski(X5,sK0) | k1_relat_1(k7_relat_1(sK4,X5)) = X5) ) | ~spl7_10),
% 1.90/0.62    inference(backward_demodulation,[],[f154,f638])).
% 1.90/0.62  fof(f638,plain,(
% 1.90/0.62    sK0 = k1_relat_1(sK4) | ~spl7_10),
% 1.90/0.62    inference(avatar_component_clause,[],[f636])).
% 1.90/0.62  fof(f636,plain,(
% 1.90/0.62    spl7_10 <=> sK0 = k1_relat_1(sK4)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.90/0.62  fof(f154,plain,(
% 1.90/0.62    ( ! [X5] : (~r1_tarski(X5,k1_relat_1(sK4)) | k1_relat_1(k7_relat_1(sK4,X5)) = X5) )),
% 1.90/0.62    inference(resolution,[],[f130,f71])).
% 1.90/0.62  fof(f59,plain,(
% 1.90/0.62    r1_tarski(sK1,sK0)),
% 1.90/0.62    inference(cnf_transformation,[],[f29])).
% 1.90/0.62  fof(f1328,plain,(
% 1.90/0.62    ~v1_partfun1(k1_xboole_0,sK1) | (~spl7_1 | spl7_3 | ~spl7_10)),
% 1.90/0.62    inference(backward_demodulation,[],[f369,f1327])).
% 1.90/0.62  fof(f369,plain,(
% 1.90/0.62    ~v1_partfun1(k7_relat_1(sK4,sK1),sK1) | (~spl7_1 | spl7_3)),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f140,f176,f167,f77])).
% 1.90/0.62  fof(f77,plain,(
% 1.90/0.62    ( ! [X2,X0,X1] : (~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(X2,X0,X1)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f42])).
% 1.90/0.62  fof(f42,plain,(
% 1.90/0.62    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.90/0.62    inference(flattening,[],[f41])).
% 1.90/0.62  fof(f41,plain,(
% 1.90/0.62    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.90/0.62    inference(ennf_transformation,[],[f21])).
% 1.90/0.62  fof(f21,axiom,(
% 1.90/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).
% 1.90/0.62  fof(f140,plain,(
% 1.90/0.62    ( ! [X0] : (v1_funct_1(k7_relat_1(sK4,X0))) )),
% 1.90/0.62    inference(forward_demodulation,[],[f123,f125])).
% 1.90/0.62  fof(f125,plain,(
% 1.90/0.62    ( ! [X0] : (k7_relat_1(sK4,X0) = k2_partfun1(sK0,sK3,sK4,X0)) )),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f56,f58,f64])).
% 1.90/0.62  fof(f64,plain,(
% 1.90/0.62    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f33])).
% 1.90/0.62  fof(f33,plain,(
% 1.90/0.62    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.90/0.62    inference(flattening,[],[f32])).
% 1.90/0.62  fof(f32,plain,(
% 1.90/0.62    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.90/0.62    inference(ennf_transformation,[],[f25])).
% 1.90/0.62  fof(f25,axiom,(
% 1.90/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.90/0.62  fof(f56,plain,(
% 1.90/0.62    v1_funct_1(sK4)),
% 1.90/0.62    inference(cnf_transformation,[],[f29])).
% 1.90/0.62  fof(f123,plain,(
% 1.90/0.62    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0))) )),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f56,f58,f62])).
% 1.90/0.62  fof(f62,plain,(
% 1.90/0.62    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f31])).
% 1.90/0.62  fof(f31,plain,(
% 1.90/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.90/0.62    inference(flattening,[],[f30])).
% 1.90/0.62  fof(f30,plain,(
% 1.90/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.90/0.62    inference(ennf_transformation,[],[f24])).
% 1.90/0.62  fof(f24,axiom,(
% 1.90/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 1.90/0.62  fof(f458,plain,(
% 1.90/0.62    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f422,f66])).
% 1.90/0.62  fof(f548,plain,(
% 1.90/0.62    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f458,f517,f100])).
% 1.90/0.62  fof(f100,plain,(
% 1.90/0.62    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.90/0.62    inference(equality_resolution,[],[f80])).
% 1.90/0.62  fof(f80,plain,(
% 1.90/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f44])).
% 1.90/0.62  fof(f517,plain,(
% 1.90/0.62    ( ! [X0,X1] : (k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)) )),
% 1.90/0.62    inference(backward_demodulation,[],[f491,f510])).
% 1.90/0.62  fof(f491,plain,(
% 1.90/0.62    ( ! [X0,X1] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0)) )),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f458,f91])).
% 1.90/0.62  fof(f1362,plain,(
% 1.90/0.62    v1_funct_1(k1_xboole_0) | (~spl7_1 | spl7_3 | ~spl7_10)),
% 1.90/0.62    inference(forward_demodulation,[],[f1329,f505])).
% 1.90/0.62  fof(f1329,plain,(
% 1.90/0.62    ( ! [X0] : (v1_funct_1(k7_relat_1(k1_xboole_0,X0))) ) | (~spl7_1 | spl7_3 | ~spl7_10)),
% 1.90/0.62    inference(backward_demodulation,[],[f376,f1327])).
% 1.90/0.62  fof(f376,plain,(
% 1.90/0.62    ( ! [X0] : (v1_funct_1(k7_relat_1(k7_relat_1(sK4,sK1),X0))) ) | ~spl7_1),
% 1.90/0.62    inference(forward_demodulation,[],[f364,f366])).
% 1.90/0.62  fof(f366,plain,(
% 1.90/0.62    ( ! [X0] : (k2_partfun1(sK1,sK2,k7_relat_1(sK4,sK1),X0) = k7_relat_1(k7_relat_1(sK4,sK1),X0)) ) | ~spl7_1),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f140,f167,f64])).
% 1.90/0.62  fof(f364,plain,(
% 1.90/0.62    ( ! [X0] : (v1_funct_1(k2_partfun1(sK1,sK2,k7_relat_1(sK4,sK1),X0))) ) | ~spl7_1),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f140,f167,f62])).
% 1.90/0.62  fof(f61,plain,(
% 1.90/0.62    ~v1_xboole_0(sK3)),
% 1.90/0.62    inference(cnf_transformation,[],[f29])).
% 1.90/0.62  fof(f707,plain,(
% 1.90/0.62    ~spl7_9),
% 1.90/0.62    inference(avatar_contradiction_clause,[],[f699])).
% 1.90/0.62  fof(f699,plain,(
% 1.90/0.62    $false | ~spl7_9),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f89,f458,f650,f86])).
% 1.90/0.62  fof(f650,plain,(
% 1.90/0.62    ~v1_xboole_0(k1_xboole_0) | ~spl7_9),
% 1.90/0.62    inference(backward_demodulation,[],[f61,f634])).
% 1.90/0.62  fof(f634,plain,(
% 1.90/0.62    k1_xboole_0 = sK3 | ~spl7_9),
% 1.90/0.62    inference(avatar_component_clause,[],[f632])).
% 1.90/0.62  fof(f632,plain,(
% 1.90/0.62    spl7_9 <=> k1_xboole_0 = sK3),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.90/0.62  fof(f647,plain,(
% 1.90/0.62    spl7_8),
% 1.90/0.62    inference(avatar_contradiction_clause,[],[f642])).
% 1.90/0.62  fof(f642,plain,(
% 1.90/0.62    $false | spl7_8),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f131,f630,f66])).
% 1.90/0.62  fof(f630,plain,(
% 1.90/0.62    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | spl7_8),
% 1.90/0.62    inference(avatar_component_clause,[],[f628])).
% 1.90/0.62  fof(f628,plain,(
% 1.90/0.62    spl7_8 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.90/0.62  fof(f131,plain,(
% 1.90/0.62    r1_tarski(sK4,k2_zfmisc_1(sK0,sK3))),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f58,f67])).
% 1.90/0.62  fof(f67,plain,(
% 1.90/0.62    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.90/0.62    inference(cnf_transformation,[],[f6])).
% 1.90/0.62  fof(f639,plain,(
% 1.90/0.62    ~spl7_8 | spl7_9 | spl7_10),
% 1.90/0.62    inference(avatar_split_clause,[],[f134,f636,f632,f628])).
% 1.90/0.62  fof(f134,plain,(
% 1.90/0.62    sK0 = k1_relat_1(sK4) | k1_xboole_0 = sK3 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 1.90/0.62    inference(backward_demodulation,[],[f112,f129])).
% 1.90/0.62  fof(f129,plain,(
% 1.90/0.62    k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4)),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f58,f91])).
% 1.90/0.62  fof(f112,plain,(
% 1.90/0.62    k1_xboole_0 = sK3 | sK0 = k1_relset_1(sK0,sK3,sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 1.90/0.62    inference(resolution,[],[f57,f83])).
% 1.90/0.62  fof(f83,plain,(
% 1.90/0.62    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.90/0.62    inference(cnf_transformation,[],[f44])).
% 1.90/0.62  fof(f57,plain,(
% 1.90/0.62    v1_funct_2(sK4,sK0,sK3)),
% 1.90/0.62    inference(cnf_transformation,[],[f29])).
% 1.90/0.62  fof(f349,plain,(
% 1.90/0.62    spl7_2),
% 1.90/0.62    inference(avatar_contradiction_clause,[],[f346])).
% 1.90/0.62  fof(f346,plain,(
% 1.90/0.62    $false | spl7_2),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f140,f172])).
% 1.90/0.62  fof(f172,plain,(
% 1.90/0.62    ~v1_funct_1(k7_relat_1(sK4,sK1)) | spl7_2),
% 1.90/0.62    inference(avatar_component_clause,[],[f170])).
% 1.90/0.62  fof(f170,plain,(
% 1.90/0.62    spl7_2 <=> v1_funct_1(k7_relat_1(sK4,sK1))),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.90/0.62  fof(f345,plain,(
% 1.90/0.62    spl7_1),
% 1.90/0.62    inference(avatar_contradiction_clause,[],[f339])).
% 1.90/0.62  fof(f339,plain,(
% 1.90/0.62    $false | spl7_1),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f163,f312,f67])).
% 1.90/0.62  fof(f312,plain,(
% 1.90/0.62    ~r1_tarski(k9_relat_1(sK4,sK1),sK2) | spl7_1),
% 1.90/0.62    inference(forward_demodulation,[],[f300,f145])).
% 1.90/0.62  fof(f145,plain,(
% 1.90/0.62    ( ! [X0] : (k9_relat_1(sK4,X0) = k2_relat_1(k7_relat_1(sK4,X0))) )),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f130,f90])).
% 1.90/0.62  fof(f90,plain,(
% 1.90/0.62    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f49])).
% 1.90/0.62  fof(f49,plain,(
% 1.90/0.62    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.90/0.62    inference(ennf_transformation,[],[f11])).
% 1.90/0.62  fof(f11,axiom,(
% 1.90/0.62    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.90/0.62  fof(f300,plain,(
% 1.90/0.62    ~r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) | spl7_1),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f147,f168,f288,f96])).
% 1.90/0.62  fof(f96,plain,(
% 1.90/0.62    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.90/0.62    inference(cnf_transformation,[],[f54])).
% 1.90/0.62  fof(f54,plain,(
% 1.90/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.90/0.62    inference(flattening,[],[f53])).
% 1.90/0.62  fof(f53,plain,(
% 1.90/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.90/0.62    inference(ennf_transformation,[],[f20])).
% 1.90/0.62  fof(f20,axiom,(
% 1.90/0.62    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 1.90/0.62  fof(f288,plain,(
% 1.90/0.62    ( ! [X0] : (v1_relat_1(k7_relat_1(sK4,X0))) )),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f146,f284])).
% 1.90/0.62  fof(f146,plain,(
% 1.90/0.62    ( ! [X0] : (r1_tarski(k7_relat_1(sK4,X0),sK4)) )),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f130,f73])).
% 1.90/0.62  fof(f168,plain,(
% 1.90/0.62    ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl7_1),
% 1.90/0.62    inference(avatar_component_clause,[],[f166])).
% 1.90/0.62  fof(f163,plain,(
% 1.90/0.62    m1_subset_1(k9_relat_1(sK4,sK1),k1_zfmisc_1(sK2))),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f135,f66])).
% 1.90/0.62  fof(f135,plain,(
% 1.90/0.62    r1_tarski(k9_relat_1(sK4,sK1),sK2)),
% 1.90/0.62    inference(backward_demodulation,[],[f60,f126])).
% 1.90/0.62  fof(f126,plain,(
% 1.90/0.62    ( ! [X0] : (k7_relset_1(sK0,sK3,sK4,X0) = k9_relat_1(sK4,X0)) )),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f58,f65])).
% 1.90/0.62  fof(f65,plain,(
% 1.90/0.62    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.90/0.62    inference(cnf_transformation,[],[f34])).
% 1.90/0.62  fof(f34,plain,(
% 1.90/0.62    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.90/0.62    inference(ennf_transformation,[],[f19])).
% 1.90/0.62  fof(f19,axiom,(
% 1.90/0.62    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.90/0.62  fof(f60,plain,(
% 1.90/0.62    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)),
% 1.90/0.62    inference(cnf_transformation,[],[f29])).
% 1.90/0.62  fof(f177,plain,(
% 1.90/0.62    ~spl7_1 | ~spl7_2 | ~spl7_3),
% 1.90/0.62    inference(avatar_split_clause,[],[f138,f174,f170,f166])).
% 1.90/0.62  fof(f138,plain,(
% 1.90/0.62    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | ~v1_funct_1(k7_relat_1(sK4,sK1)) | ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.90/0.62    inference(forward_demodulation,[],[f137,f125])).
% 1.90/0.62  fof(f137,plain,(
% 1.90/0.62    ~v1_funct_1(k7_relat_1(sK4,sK1)) | ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)),
% 1.90/0.62    inference(forward_demodulation,[],[f136,f125])).
% 1.90/0.62  fof(f136,plain,(
% 1.90/0.62    ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)),
% 1.90/0.62    inference(backward_demodulation,[],[f55,f125])).
% 1.90/0.62  fof(f55,plain,(
% 1.90/0.62    ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.90/0.62    inference(cnf_transformation,[],[f29])).
% 1.90/0.62  % SZS output end Proof for theBenchmark
% 1.90/0.62  % (20494)------------------------------
% 1.90/0.62  % (20494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.62  % (20494)Termination reason: Refutation
% 1.90/0.62  
% 1.90/0.62  % (20494)Memory used [KB]: 6908
% 1.90/0.62  % (20494)Time elapsed: 0.170 s
% 1.90/0.62  % (20494)------------------------------
% 1.90/0.62  % (20494)------------------------------
% 1.90/0.62  % (20489)Success in time 0.258 s
%------------------------------------------------------------------------------
