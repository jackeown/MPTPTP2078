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
% DateTime   : Thu Dec  3 13:18:44 EST 2020

% Result     : Theorem 1.79s
% Output     : Refutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :  143 (15037 expanded)
%              Number of leaves         :   14 (3056 expanded)
%              Depth                    :   28
%              Number of atoms          :  468 (211185 expanded)
%              Number of equality atoms :   57 (10912 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f612,plain,(
    $false ),
    inference(global_subsumption,[],[f608,f607])).

fof(f607,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_xboole_0,sK2),k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f600])).

fof(f600,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_xboole_0,sK2),k1_xboole_0)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_xboole_0,sK2),k1_xboole_0) ),
    inference(backward_demodulation,[],[f546,f570])).

fof(f570,plain,(
    k1_xboole_0 = sK6 ),
    inference(duplicate_literal_removal,[],[f566])).

fof(f566,plain,
    ( k1_xboole_0 = sK6
    | k1_xboole_0 = sK6 ),
    inference(resolution,[],[f565,f143])).

fof(f143,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f65,f57])).

fof(f57,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f565,plain,
    ( r1_tarski(sK6,k1_xboole_0)
    | k1_xboole_0 = sK6 ),
    inference(resolution,[],[f564,f412])).

fof(f412,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | k1_xboole_0 = sK6 ),
    inference(backward_demodulation,[],[f297,f389])).

fof(f389,plain,(
    k1_xboole_0 = sK4 ),
    inference(global_subsumption,[],[f388,f387])).

fof(f387,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | k1_xboole_0 = sK4 ),
    inference(duplicate_literal_removal,[],[f386])).

fof(f386,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | k1_xboole_0 = sK4 ),
    inference(superposition,[],[f321,f366])).

fof(f366,plain,
    ( sK4 = sK6
    | k1_xboole_0 = sK4 ),
    inference(resolution,[],[f365,f143])).

fof(f365,plain,
    ( r1_tarski(sK4,k1_xboole_0)
    | sK4 = sK6 ),
    inference(resolution,[],[f363,f297])).

fof(f363,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | r1_tarski(sK4,k1_xboole_0) ),
    inference(forward_demodulation,[],[f362,f83])).

fof(f83,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f362,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0))
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(superposition,[],[f350,f258])).

fof(f258,plain,
    ( k1_xboole_0 = k2_relat_1(sK4)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f244,f143])).

fof(f244,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(sK4),X0)
      | ~ v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f237,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f237,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK4))
      | ~ v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f223,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f223,plain,(
    m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unit_resulting_resolution,[],[f210,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f210,plain,(
    r1_tarski(k2_relat_1(sK4),u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f113,f197,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f197,plain,(
    v5_relat_1(sK4,u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f46,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f46,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                              <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                              <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ! [X6] :
                                ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                  & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                                  & v1_funct_1(X6) )
                               => ( ( r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                                    & X0 = X3 )
                                 => ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                                  <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                         => ! [X6] :
                              ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                                & v1_funct_1(X6) )
                             => ( ( r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                                  & X0 = X3 )
                               => ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                                <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_tmap_1)).

fof(f113,plain,(
    v1_relat_1(sK4) ),
    inference(unit_resulting_resolution,[],[f46,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f350,plain,(
    r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))) ),
    inference(unit_resulting_resolution,[],[f264,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f264,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))) ),
    inference(unit_resulting_resolution,[],[f113,f81,f81,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f81,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f321,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK6,sK2),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(backward_demodulation,[],[f92,f319])).

fof(f319,plain,(
    k3_tmap_1(sK0,sK1,sK0,sK2,sK6) = k2_tmap_1(sK0,sK1,sK6,sK2) ),
    inference(forward_demodulation,[],[f310,f306])).

fof(f306,plain,(
    k2_tmap_1(sK0,sK1,sK6,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK6,u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f54,f50,f55,f56,f36,f53,f52,f51,f91,f90,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f90,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f38,f39])).

fof(f39,plain,(
    sK0 = sK3 ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f18])).

fof(f91,plain,(
    v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f37,f39])).

fof(f37,plain,(
    v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f51,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f52,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f53,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f18])).

fof(f56,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f55,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f50,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f54,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f310,plain,(
    k3_tmap_1(sK0,sK1,sK0,sK2,sK6) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK6,u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f54,f36,f55,f56,f50,f50,f89,f53,f52,f51,f91,f90,f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f89,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(backward_demodulation,[],[f48,f39])).

fof(f48,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f92,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK6),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(forward_demodulation,[],[f35,f39])).

fof(f35,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) ),
    inference(cnf_transformation,[],[f18])).

fof(f388,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | k1_xboole_0 = sK4 ),
    inference(duplicate_literal_removal,[],[f385])).

fof(f385,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | k1_xboole_0 = sK4 ),
    inference(superposition,[],[f320,f366])).

fof(f320,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK6,sK2),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(backward_demodulation,[],[f93,f319])).

fof(f93,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK6),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(forward_demodulation,[],[f34,f39])).

fof(f34,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) ),
    inference(cnf_transformation,[],[f18])).

fof(f297,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | sK4 = sK6 ),
    inference(global_subsumption,[],[f46,f45,f44,f90,f91,f36,f296])).

fof(f296,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | sK4 = sK6 ),
    inference(duplicate_literal_removal,[],[f293])).

fof(f293,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | sK4 = sK6
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f80,f87])).

fof(f87,plain,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6) ),
    inference(backward_demodulation,[],[f40,f39])).

fof(f40,plain,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6) ),
    inference(cnf_transformation,[],[f18])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
      | v1_xboole_0(X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | X4 = X5
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

fof(f44,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f18])).

fof(f45,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f564,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | r1_tarski(sK6,k1_xboole_0) ),
    inference(forward_demodulation,[],[f563,f83])).

fof(f563,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(k1_relat_1(sK6),k1_xboole_0))
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(superposition,[],[f551,f279])).

fof(f279,plain,
    ( k1_xboole_0 = k2_relat_1(sK6)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f245,f143])).

fof(f245,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(sK6),X0)
      | ~ v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f240,f67])).

fof(f240,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK6))
      | ~ v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f227,f78])).

fof(f227,plain,(
    m1_subset_1(k2_relat_1(sK6),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unit_resulting_resolution,[],[f211,f69])).

fof(f211,plain,(
    r1_tarski(k2_relat_1(sK6),u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f114,f198,f62])).

fof(f198,plain,(
    v5_relat_1(sK6,u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f90,f77])).

fof(f114,plain,(
    v1_relat_1(sK6) ),
    inference(unit_resulting_resolution,[],[f90,f75])).

fof(f551,plain,(
    r1_tarski(sK6,k2_zfmisc_1(k1_relat_1(sK6),k2_relat_1(sK6))) ),
    inference(unit_resulting_resolution,[],[f266,f70])).

fof(f266,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),k2_relat_1(sK6)))) ),
    inference(unit_resulting_resolution,[],[f114,f81,f81,f74])).

fof(f546,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_xboole_0,sK2),k1_xboole_0)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK6,sK2),k1_xboole_0) ),
    inference(forward_demodulation,[],[f534,f509])).

fof(f509,plain,(
    k1_xboole_0 = sK5 ),
    inference(global_subsumption,[],[f508,f507])).

fof(f507,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_xboole_0,sK2),sK5)
    | k1_xboole_0 = sK5 ),
    inference(duplicate_literal_removal,[],[f506])).

fof(f506,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_xboole_0,sK2),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_xboole_0,sK2),sK5)
    | k1_xboole_0 = sK5 ),
    inference(superposition,[],[f422,f486])).

fof(f486,plain,
    ( k1_xboole_0 = sK6
    | k1_xboole_0 = sK5 ),
    inference(resolution,[],[f485,f143])).

fof(f485,plain,
    ( r1_tarski(sK5,k1_xboole_0)
    | k1_xboole_0 = sK6 ),
    inference(resolution,[],[f484,f412])).

fof(f484,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | r1_tarski(sK5,k1_xboole_0) ),
    inference(forward_demodulation,[],[f483,f83])).

fof(f483,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(k1_relat_1(sK5),k1_xboole_0))
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(superposition,[],[f471,f248])).

fof(f248,plain,
    ( k1_xboole_0 = k2_relat_1(sK5)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f242,f143])).

fof(f242,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(sK5),X0)
      | ~ v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f234,f67])).

fof(f234,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK5))
      | ~ v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f219,f78])).

fof(f219,plain,(
    m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unit_resulting_resolution,[],[f209,f69])).

fof(f209,plain,(
    r1_tarski(k2_relat_1(sK5),u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f112,f196,f62])).

fof(f196,plain,(
    v5_relat_1(sK5,u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f43,f77])).

fof(f43,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f18])).

fof(f112,plain,(
    v1_relat_1(sK5) ),
    inference(unit_resulting_resolution,[],[f43,f75])).

fof(f471,plain,(
    r1_tarski(sK5,k2_zfmisc_1(k1_relat_1(sK5),k2_relat_1(sK5))) ),
    inference(unit_resulting_resolution,[],[f265,f70])).

fof(f265,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),k2_relat_1(sK5)))) ),
    inference(unit_resulting_resolution,[],[f112,f81,f81,f74])).

fof(f422,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK6,sK2),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_xboole_0,sK2),sK5) ),
    inference(backward_demodulation,[],[f321,f389])).

fof(f508,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_xboole_0,sK2),sK5)
    | k1_xboole_0 = sK5 ),
    inference(duplicate_literal_removal,[],[f505])).

fof(f505,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_xboole_0,sK2),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_xboole_0,sK2),sK5)
    | k1_xboole_0 = sK5 ),
    inference(superposition,[],[f421,f486])).

fof(f421,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK6,sK2),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_xboole_0,sK2),sK5) ),
    inference(backward_demodulation,[],[f320,f389])).

fof(f534,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK6,sK2),k1_xboole_0)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_xboole_0,sK2),sK5) ),
    inference(backward_demodulation,[],[f422,f509])).

fof(f608,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_xboole_0,sK2),k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f599])).

fof(f599,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_xboole_0,sK2),k1_xboole_0)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_xboole_0,sK2),k1_xboole_0) ),
    inference(backward_demodulation,[],[f545,f570])).

fof(f545,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK6,sK2),k1_xboole_0)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_xboole_0,sK2),k1_xboole_0) ),
    inference(forward_demodulation,[],[f533,f509])).

fof(f533,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK6,sK2),k1_xboole_0)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_xboole_0,sK2),sK5) ),
    inference(backward_demodulation,[],[f421,f509])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:13:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.51  % (4953)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (4971)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.52  % (4960)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (4978)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.53  % (4956)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (4968)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.53  % (4955)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (4960)Refutation not found, incomplete strategy% (4960)------------------------------
% 0.22/0.54  % (4960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (4963)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (4962)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (4952)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (4960)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (4960)Memory used [KB]: 10874
% 0.22/0.54  % (4960)Time elapsed: 0.128 s
% 0.22/0.54  % (4960)------------------------------
% 0.22/0.54  % (4960)------------------------------
% 0.22/0.55  % (4976)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (4974)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (4958)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (4972)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (4978)Refutation not found, incomplete strategy% (4978)------------------------------
% 0.22/0.55  % (4978)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (4978)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (4978)Memory used [KB]: 10874
% 0.22/0.55  % (4978)Time elapsed: 0.145 s
% 0.22/0.55  % (4978)------------------------------
% 0.22/0.55  % (4978)------------------------------
% 0.22/0.55  % (4966)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (4969)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (4977)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (4975)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (4973)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (4969)Refutation not found, incomplete strategy% (4969)------------------------------
% 0.22/0.55  % (4969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (4969)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (4969)Memory used [KB]: 10746
% 0.22/0.55  % (4969)Time elapsed: 0.149 s
% 0.22/0.55  % (4969)------------------------------
% 0.22/0.55  % (4969)------------------------------
% 0.22/0.55  % (4954)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.56  % (4970)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.56  % (4967)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.56  % (4961)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.56  % (4965)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % (4957)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.56  % (4979)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.57  % (4959)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.57  % (4981)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.57  % (4974)Refutation not found, incomplete strategy% (4974)------------------------------
% 0.22/0.57  % (4974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (4974)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (4974)Memory used [KB]: 11001
% 0.22/0.57  % (4974)Time elapsed: 0.166 s
% 0.22/0.57  % (4974)------------------------------
% 0.22/0.57  % (4974)------------------------------
% 0.22/0.58  % (4980)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.58  % (4964)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.79/0.60  % (4976)Refutation found. Thanks to Tanya!
% 1.79/0.60  % SZS status Theorem for theBenchmark
% 1.79/0.60  % SZS output start Proof for theBenchmark
% 1.79/0.60  fof(f612,plain,(
% 1.79/0.60    $false),
% 1.79/0.60    inference(global_subsumption,[],[f608,f607])).
% 1.79/0.60  fof(f607,plain,(
% 1.79/0.60    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_xboole_0,sK2),k1_xboole_0)),
% 1.79/0.60    inference(duplicate_literal_removal,[],[f600])).
% 1.79/0.60  fof(f600,plain,(
% 1.79/0.60    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_xboole_0,sK2),k1_xboole_0) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_xboole_0,sK2),k1_xboole_0)),
% 1.79/0.60    inference(backward_demodulation,[],[f546,f570])).
% 1.79/0.60  fof(f570,plain,(
% 1.79/0.60    k1_xboole_0 = sK6),
% 1.79/0.60    inference(duplicate_literal_removal,[],[f566])).
% 1.79/0.60  fof(f566,plain,(
% 1.79/0.60    k1_xboole_0 = sK6 | k1_xboole_0 = sK6),
% 1.79/0.60    inference(resolution,[],[f565,f143])).
% 1.79/0.60  fof(f143,plain,(
% 1.79/0.60    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.79/0.60    inference(resolution,[],[f65,f57])).
% 1.79/0.60  fof(f57,plain,(
% 1.79/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f3])).
% 1.79/0.60  fof(f3,axiom,(
% 1.79/0.60    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.79/0.60  fof(f65,plain,(
% 1.79/0.60    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.79/0.60    inference(cnf_transformation,[],[f2])).
% 1.79/0.60  fof(f2,axiom,(
% 1.79/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.79/0.60  fof(f565,plain,(
% 1.79/0.60    r1_tarski(sK6,k1_xboole_0) | k1_xboole_0 = sK6),
% 1.79/0.60    inference(resolution,[],[f564,f412])).
% 1.79/0.60  fof(f412,plain,(
% 1.79/0.60    v1_xboole_0(u1_struct_0(sK1)) | k1_xboole_0 = sK6),
% 1.79/0.60    inference(backward_demodulation,[],[f297,f389])).
% 1.79/0.60  fof(f389,plain,(
% 1.79/0.60    k1_xboole_0 = sK4),
% 1.79/0.60    inference(global_subsumption,[],[f388,f387])).
% 1.79/0.60  fof(f387,plain,(
% 1.79/0.60    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | k1_xboole_0 = sK4),
% 1.79/0.60    inference(duplicate_literal_removal,[],[f386])).
% 1.79/0.60  fof(f386,plain,(
% 1.79/0.60    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | k1_xboole_0 = sK4),
% 1.79/0.60    inference(superposition,[],[f321,f366])).
% 1.79/0.60  fof(f366,plain,(
% 1.79/0.60    sK4 = sK6 | k1_xboole_0 = sK4),
% 1.79/0.60    inference(resolution,[],[f365,f143])).
% 1.79/0.60  fof(f365,plain,(
% 1.79/0.60    r1_tarski(sK4,k1_xboole_0) | sK4 = sK6),
% 1.79/0.60    inference(resolution,[],[f363,f297])).
% 1.79/0.60  fof(f363,plain,(
% 1.79/0.60    ~v1_xboole_0(u1_struct_0(sK1)) | r1_tarski(sK4,k1_xboole_0)),
% 1.79/0.60    inference(forward_demodulation,[],[f362,f83])).
% 1.79/0.60  fof(f83,plain,(
% 1.79/0.60    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.79/0.60    inference(equality_resolution,[],[f73])).
% 1.79/0.60  fof(f73,plain,(
% 1.79/0.60    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f4])).
% 1.79/0.60  fof(f4,axiom,(
% 1.79/0.60    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.79/0.60  fof(f362,plain,(
% 1.79/0.60    r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0)) | ~v1_xboole_0(u1_struct_0(sK1))),
% 1.79/0.60    inference(superposition,[],[f350,f258])).
% 1.79/0.60  fof(f258,plain,(
% 1.79/0.60    k1_xboole_0 = k2_relat_1(sK4) | ~v1_xboole_0(u1_struct_0(sK1))),
% 1.79/0.60    inference(resolution,[],[f244,f143])).
% 1.79/0.60  fof(f244,plain,(
% 1.79/0.60    ( ! [X0] : (r1_tarski(k2_relat_1(sK4),X0) | ~v1_xboole_0(u1_struct_0(sK1))) )),
% 1.79/0.60    inference(resolution,[],[f237,f67])).
% 1.79/0.60  fof(f67,plain,(
% 1.79/0.60    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f26])).
% 1.79/0.60  fof(f26,plain,(
% 1.79/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.79/0.60    inference(ennf_transformation,[],[f1])).
% 1.79/0.60  fof(f1,axiom,(
% 1.79/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.79/0.60  fof(f237,plain,(
% 1.79/0.60    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK4)) | ~v1_xboole_0(u1_struct_0(sK1))) )),
% 1.79/0.60    inference(resolution,[],[f223,f78])).
% 1.79/0.60  fof(f78,plain,(
% 1.79/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | ~v1_xboole_0(X2)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f31])).
% 1.79/0.60  fof(f31,plain,(
% 1.79/0.60    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.79/0.60    inference(ennf_transformation,[],[f6])).
% 1.79/0.60  fof(f6,axiom,(
% 1.79/0.60    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.79/0.60  fof(f223,plain,(
% 1.79/0.60    m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f210,f69])).
% 1.79/0.60  fof(f69,plain,(
% 1.79/0.60    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f5])).
% 1.79/0.60  fof(f5,axiom,(
% 1.79/0.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.79/0.60  fof(f210,plain,(
% 1.79/0.60    r1_tarski(k2_relat_1(sK4),u1_struct_0(sK1))),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f113,f197,f62])).
% 1.79/0.60  fof(f62,plain,(
% 1.79/0.60    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f25])).
% 1.79/0.60  fof(f25,plain,(
% 1.79/0.60    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.79/0.60    inference(ennf_transformation,[],[f7])).
% 1.79/0.60  fof(f7,axiom,(
% 1.79/0.60    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.79/0.60  fof(f197,plain,(
% 1.79/0.60    v5_relat_1(sK4,u1_struct_0(sK1))),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f46,f77])).
% 1.79/0.60  fof(f77,plain,(
% 1.79/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f30])).
% 1.79/0.60  fof(f30,plain,(
% 1.79/0.60    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.79/0.60    inference(ennf_transformation,[],[f9])).
% 1.79/0.60  fof(f9,axiom,(
% 1.79/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.79/0.60  fof(f46,plain,(
% 1.79/0.60    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.79/0.60    inference(cnf_transformation,[],[f18])).
% 1.79/0.60  fof(f18,plain,(
% 1.79/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.79/0.60    inference(flattening,[],[f17])).
% 1.79/0.60  fof(f17,plain,(
% 1.79/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & (r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3)) & (m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.79/0.60    inference(ennf_transformation,[],[f16])).
% 1.79/0.60  fof(f16,negated_conjecture,(
% 1.79/0.60    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 1.79/0.60    inference(negated_conjecture,[],[f15])).
% 1.79/0.60  fof(f15,conjecture,(
% 1.79/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_tmap_1)).
% 1.79/0.60  fof(f113,plain,(
% 1.79/0.60    v1_relat_1(sK4)),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f46,f75])).
% 1.79/0.60  fof(f75,plain,(
% 1.79/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f29])).
% 1.79/0.60  fof(f29,plain,(
% 1.79/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.79/0.60    inference(ennf_transformation,[],[f8])).
% 1.79/0.60  fof(f8,axiom,(
% 1.79/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.79/0.60  fof(f350,plain,(
% 1.79/0.60    r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4)))),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f264,f70])).
% 1.79/0.60  fof(f70,plain,(
% 1.79/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f5])).
% 1.79/0.60  fof(f264,plain,(
% 1.79/0.60    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))))),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f113,f81,f81,f74])).
% 1.79/0.60  fof(f74,plain,(
% 1.79/0.60    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | ~v1_relat_1(X2)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f28])).
% 1.79/0.60  fof(f28,plain,(
% 1.79/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.79/0.60    inference(flattening,[],[f27])).
% 1.79/0.60  fof(f27,plain,(
% 1.79/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.79/0.60    inference(ennf_transformation,[],[f10])).
% 1.79/0.60  fof(f10,axiom,(
% 1.79/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 1.79/0.60  fof(f81,plain,(
% 1.79/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.79/0.60    inference(equality_resolution,[],[f64])).
% 1.79/0.60  fof(f64,plain,(
% 1.79/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.79/0.60    inference(cnf_transformation,[],[f2])).
% 1.79/0.60  fof(f321,plain,(
% 1.79/0.60    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK6,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)),
% 1.79/0.60    inference(backward_demodulation,[],[f92,f319])).
% 1.79/0.60  fof(f319,plain,(
% 1.79/0.60    k3_tmap_1(sK0,sK1,sK0,sK2,sK6) = k2_tmap_1(sK0,sK1,sK6,sK2)),
% 1.79/0.60    inference(forward_demodulation,[],[f310,f306])).
% 1.79/0.60  fof(f306,plain,(
% 1.79/0.60    k2_tmap_1(sK0,sK1,sK6,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK6,u1_struct_0(sK2))),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f54,f50,f55,f56,f36,f53,f52,f51,f91,f90,f59])).
% 1.79/0.60  fof(f59,plain,(
% 1.79/0.60    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | v2_struct_0(X0)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f22])).
% 1.79/0.60  fof(f22,plain,(
% 1.79/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.79/0.60    inference(flattening,[],[f21])).
% 1.79/0.60  fof(f21,plain,(
% 1.79/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.79/0.60    inference(ennf_transformation,[],[f12])).
% 1.79/0.60  fof(f12,axiom,(
% 1.79/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 1.79/0.60  fof(f90,plain,(
% 1.79/0.60    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.79/0.60    inference(forward_demodulation,[],[f38,f39])).
% 1.79/0.60  fof(f39,plain,(
% 1.79/0.60    sK0 = sK3),
% 1.79/0.60    inference(cnf_transformation,[],[f18])).
% 1.79/0.60  fof(f38,plain,(
% 1.79/0.60    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.79/0.60    inference(cnf_transformation,[],[f18])).
% 1.79/0.60  fof(f91,plain,(
% 1.79/0.60    v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.79/0.60    inference(forward_demodulation,[],[f37,f39])).
% 1.79/0.60  fof(f37,plain,(
% 1.79/0.60    v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.79/0.60    inference(cnf_transformation,[],[f18])).
% 1.79/0.60  fof(f51,plain,(
% 1.79/0.60    ~v2_struct_0(sK1)),
% 1.79/0.60    inference(cnf_transformation,[],[f18])).
% 1.79/0.60  fof(f52,plain,(
% 1.79/0.60    v2_pre_topc(sK1)),
% 1.79/0.60    inference(cnf_transformation,[],[f18])).
% 1.79/0.60  fof(f53,plain,(
% 1.79/0.60    l1_pre_topc(sK1)),
% 1.79/0.60    inference(cnf_transformation,[],[f18])).
% 1.79/0.60  fof(f36,plain,(
% 1.79/0.60    v1_funct_1(sK6)),
% 1.79/0.60    inference(cnf_transformation,[],[f18])).
% 1.79/0.60  fof(f56,plain,(
% 1.79/0.60    l1_pre_topc(sK0)),
% 1.79/0.60    inference(cnf_transformation,[],[f18])).
% 1.79/0.60  fof(f55,plain,(
% 1.79/0.60    v2_pre_topc(sK0)),
% 1.79/0.60    inference(cnf_transformation,[],[f18])).
% 1.79/0.60  fof(f50,plain,(
% 1.79/0.60    m1_pre_topc(sK2,sK0)),
% 1.79/0.60    inference(cnf_transformation,[],[f18])).
% 1.79/0.60  fof(f54,plain,(
% 1.79/0.60    ~v2_struct_0(sK0)),
% 1.79/0.60    inference(cnf_transformation,[],[f18])).
% 1.79/0.60  fof(f310,plain,(
% 1.79/0.60    k3_tmap_1(sK0,sK1,sK0,sK2,sK6) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK6,u1_struct_0(sK2))),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f54,f36,f55,f56,f50,f50,f89,f53,f52,f51,f91,f90,f58])).
% 1.79/0.60  fof(f58,plain,(
% 1.79/0.60    ( ! [X4,X2,X0,X3,X1] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | v2_struct_0(X0)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f20])).
% 1.79/0.60  fof(f20,plain,(
% 1.79/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.79/0.60    inference(flattening,[],[f19])).
% 1.79/0.60  fof(f19,plain,(
% 1.79/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.79/0.60    inference(ennf_transformation,[],[f13])).
% 1.79/0.60  fof(f13,axiom,(
% 1.79/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 1.79/0.60  fof(f89,plain,(
% 1.79/0.60    m1_pre_topc(sK0,sK0)),
% 1.79/0.60    inference(backward_demodulation,[],[f48,f39])).
% 1.79/0.60  fof(f48,plain,(
% 1.79/0.60    m1_pre_topc(sK3,sK0)),
% 1.79/0.60    inference(cnf_transformation,[],[f18])).
% 1.79/0.60  fof(f92,plain,(
% 1.79/0.60    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK6),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)),
% 1.79/0.60    inference(forward_demodulation,[],[f35,f39])).
% 1.79/0.60  fof(f35,plain,(
% 1.79/0.60    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)),
% 1.79/0.60    inference(cnf_transformation,[],[f18])).
% 1.79/0.60  fof(f388,plain,(
% 1.79/0.60    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | k1_xboole_0 = sK4),
% 1.79/0.60    inference(duplicate_literal_removal,[],[f385])).
% 1.79/0.60  fof(f385,plain,(
% 1.79/0.60    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | k1_xboole_0 = sK4),
% 1.79/0.60    inference(superposition,[],[f320,f366])).
% 1.79/0.60  fof(f320,plain,(
% 1.79/0.60    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK6,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)),
% 1.79/0.60    inference(backward_demodulation,[],[f93,f319])).
% 1.79/0.60  fof(f93,plain,(
% 1.79/0.60    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK6),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)),
% 1.79/0.60    inference(forward_demodulation,[],[f34,f39])).
% 1.79/0.60  fof(f34,plain,(
% 1.79/0.60    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)),
% 1.79/0.60    inference(cnf_transformation,[],[f18])).
% 1.79/0.60  fof(f297,plain,(
% 1.79/0.60    v1_xboole_0(u1_struct_0(sK1)) | sK4 = sK6),
% 1.79/0.60    inference(global_subsumption,[],[f46,f45,f44,f90,f91,f36,f296])).
% 1.79/0.60  fof(f296,plain,(
% 1.79/0.60    v1_xboole_0(u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(sK6) | ~v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | sK4 = sK6),
% 1.79/0.60    inference(duplicate_literal_removal,[],[f293])).
% 1.79/0.60  fof(f293,plain,(
% 1.79/0.60    v1_xboole_0(u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(sK6) | ~v1_funct_2(sK6,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | sK4 = sK6 | v1_xboole_0(u1_struct_0(sK1))),
% 1.79/0.60    inference(resolution,[],[f80,f87])).
% 1.79/0.60  fof(f87,plain,(
% 1.79/0.60    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK6)),
% 1.79/0.60    inference(backward_demodulation,[],[f40,f39])).
% 1.79/0.60  fof(f40,plain,(
% 1.79/0.60    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6)),
% 1.79/0.60    inference(cnf_transformation,[],[f18])).
% 1.79/0.60  fof(f80,plain,(
% 1.79/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_funct_2(X0,X1,X2,X3,X4,X5) | v1_xboole_0(X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X0,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | X4 = X5 | v1_xboole_0(X1)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f33])).
% 1.79/0.60  fof(f33,plain,(
% 1.79/0.60    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 1.79/0.60    inference(flattening,[],[f32])).
% 1.79/0.60  fof(f32,plain,(
% 1.79/0.60    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 1.79/0.60    inference(ennf_transformation,[],[f11])).
% 1.79/0.60  fof(f11,axiom,(
% 1.79/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).
% 1.79/0.60  fof(f44,plain,(
% 1.79/0.60    v1_funct_1(sK4)),
% 1.79/0.60    inference(cnf_transformation,[],[f18])).
% 1.79/0.60  fof(f45,plain,(
% 1.79/0.60    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.79/0.60    inference(cnf_transformation,[],[f18])).
% 1.79/0.60  fof(f564,plain,(
% 1.79/0.60    ~v1_xboole_0(u1_struct_0(sK1)) | r1_tarski(sK6,k1_xboole_0)),
% 1.79/0.60    inference(forward_demodulation,[],[f563,f83])).
% 1.79/0.60  fof(f563,plain,(
% 1.79/0.60    r1_tarski(sK6,k2_zfmisc_1(k1_relat_1(sK6),k1_xboole_0)) | ~v1_xboole_0(u1_struct_0(sK1))),
% 1.79/0.60    inference(superposition,[],[f551,f279])).
% 1.79/0.60  fof(f279,plain,(
% 1.79/0.60    k1_xboole_0 = k2_relat_1(sK6) | ~v1_xboole_0(u1_struct_0(sK1))),
% 1.79/0.60    inference(resolution,[],[f245,f143])).
% 1.79/0.60  fof(f245,plain,(
% 1.79/0.60    ( ! [X0] : (r1_tarski(k2_relat_1(sK6),X0) | ~v1_xboole_0(u1_struct_0(sK1))) )),
% 1.79/0.60    inference(resolution,[],[f240,f67])).
% 1.79/0.60  fof(f240,plain,(
% 1.79/0.60    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK6)) | ~v1_xboole_0(u1_struct_0(sK1))) )),
% 1.79/0.60    inference(resolution,[],[f227,f78])).
% 1.79/0.60  fof(f227,plain,(
% 1.79/0.60    m1_subset_1(k2_relat_1(sK6),k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f211,f69])).
% 1.79/0.60  fof(f211,plain,(
% 1.79/0.60    r1_tarski(k2_relat_1(sK6),u1_struct_0(sK1))),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f114,f198,f62])).
% 1.79/0.60  fof(f198,plain,(
% 1.79/0.60    v5_relat_1(sK6,u1_struct_0(sK1))),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f90,f77])).
% 1.79/0.60  fof(f114,plain,(
% 1.79/0.60    v1_relat_1(sK6)),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f90,f75])).
% 1.79/0.60  fof(f551,plain,(
% 1.79/0.60    r1_tarski(sK6,k2_zfmisc_1(k1_relat_1(sK6),k2_relat_1(sK6)))),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f266,f70])).
% 1.79/0.60  fof(f266,plain,(
% 1.79/0.60    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),k2_relat_1(sK6))))),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f114,f81,f81,f74])).
% 1.79/0.60  fof(f546,plain,(
% 1.79/0.60    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_xboole_0,sK2),k1_xboole_0) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK6,sK2),k1_xboole_0)),
% 1.79/0.60    inference(forward_demodulation,[],[f534,f509])).
% 1.79/0.60  fof(f509,plain,(
% 1.79/0.60    k1_xboole_0 = sK5),
% 1.79/0.60    inference(global_subsumption,[],[f508,f507])).
% 1.79/0.60  fof(f507,plain,(
% 1.79/0.60    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_xboole_0,sK2),sK5) | k1_xboole_0 = sK5),
% 1.79/0.60    inference(duplicate_literal_removal,[],[f506])).
% 1.79/0.60  fof(f506,plain,(
% 1.79/0.60    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_xboole_0,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_xboole_0,sK2),sK5) | k1_xboole_0 = sK5),
% 1.79/0.60    inference(superposition,[],[f422,f486])).
% 1.79/0.60  fof(f486,plain,(
% 1.79/0.60    k1_xboole_0 = sK6 | k1_xboole_0 = sK5),
% 1.79/0.60    inference(resolution,[],[f485,f143])).
% 1.79/0.60  fof(f485,plain,(
% 1.79/0.60    r1_tarski(sK5,k1_xboole_0) | k1_xboole_0 = sK6),
% 1.79/0.60    inference(resolution,[],[f484,f412])).
% 1.79/0.60  fof(f484,plain,(
% 1.79/0.60    ~v1_xboole_0(u1_struct_0(sK1)) | r1_tarski(sK5,k1_xboole_0)),
% 1.79/0.60    inference(forward_demodulation,[],[f483,f83])).
% 1.79/0.60  fof(f483,plain,(
% 1.79/0.60    r1_tarski(sK5,k2_zfmisc_1(k1_relat_1(sK5),k1_xboole_0)) | ~v1_xboole_0(u1_struct_0(sK1))),
% 1.79/0.60    inference(superposition,[],[f471,f248])).
% 1.79/0.60  fof(f248,plain,(
% 1.79/0.60    k1_xboole_0 = k2_relat_1(sK5) | ~v1_xboole_0(u1_struct_0(sK1))),
% 1.79/0.60    inference(resolution,[],[f242,f143])).
% 1.79/0.60  fof(f242,plain,(
% 1.79/0.60    ( ! [X0] : (r1_tarski(k2_relat_1(sK5),X0) | ~v1_xboole_0(u1_struct_0(sK1))) )),
% 1.79/0.60    inference(resolution,[],[f234,f67])).
% 1.79/0.60  fof(f234,plain,(
% 1.79/0.60    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK5)) | ~v1_xboole_0(u1_struct_0(sK1))) )),
% 1.79/0.60    inference(resolution,[],[f219,f78])).
% 1.79/0.60  fof(f219,plain,(
% 1.79/0.60    m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f209,f69])).
% 1.79/0.60  fof(f209,plain,(
% 1.79/0.60    r1_tarski(k2_relat_1(sK5),u1_struct_0(sK1))),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f112,f196,f62])).
% 1.79/0.60  fof(f196,plain,(
% 1.79/0.60    v5_relat_1(sK5,u1_struct_0(sK1))),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f43,f77])).
% 1.79/0.60  fof(f43,plain,(
% 1.79/0.60    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 1.79/0.60    inference(cnf_transformation,[],[f18])).
% 1.79/0.60  fof(f112,plain,(
% 1.79/0.60    v1_relat_1(sK5)),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f43,f75])).
% 1.79/0.60  fof(f471,plain,(
% 1.79/0.60    r1_tarski(sK5,k2_zfmisc_1(k1_relat_1(sK5),k2_relat_1(sK5)))),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f265,f70])).
% 1.79/0.60  fof(f265,plain,(
% 1.79/0.60    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),k2_relat_1(sK5))))),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f112,f81,f81,f74])).
% 1.79/0.60  fof(f422,plain,(
% 1.79/0.60    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK6,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_xboole_0,sK2),sK5)),
% 1.79/0.60    inference(backward_demodulation,[],[f321,f389])).
% 1.79/0.60  fof(f508,plain,(
% 1.79/0.60    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_xboole_0,sK2),sK5) | k1_xboole_0 = sK5),
% 1.79/0.60    inference(duplicate_literal_removal,[],[f505])).
% 1.79/0.60  fof(f505,plain,(
% 1.79/0.60    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_xboole_0,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_xboole_0,sK2),sK5) | k1_xboole_0 = sK5),
% 1.79/0.60    inference(superposition,[],[f421,f486])).
% 1.79/0.60  fof(f421,plain,(
% 1.79/0.60    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK6,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_xboole_0,sK2),sK5)),
% 1.79/0.60    inference(backward_demodulation,[],[f320,f389])).
% 1.79/0.60  fof(f534,plain,(
% 1.79/0.60    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK6,sK2),k1_xboole_0) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_xboole_0,sK2),sK5)),
% 1.79/0.60    inference(backward_demodulation,[],[f422,f509])).
% 1.79/0.60  fof(f608,plain,(
% 1.79/0.60    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_xboole_0,sK2),k1_xboole_0)),
% 1.79/0.60    inference(duplicate_literal_removal,[],[f599])).
% 1.79/0.60  fof(f599,plain,(
% 1.79/0.60    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_xboole_0,sK2),k1_xboole_0) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_xboole_0,sK2),k1_xboole_0)),
% 1.79/0.60    inference(backward_demodulation,[],[f545,f570])).
% 1.79/0.60  fof(f545,plain,(
% 1.79/0.60    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK6,sK2),k1_xboole_0) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_xboole_0,sK2),k1_xboole_0)),
% 1.79/0.60    inference(forward_demodulation,[],[f533,f509])).
% 1.79/0.60  fof(f533,plain,(
% 1.79/0.60    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK6,sK2),k1_xboole_0) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,k1_xboole_0,sK2),sK5)),
% 1.79/0.60    inference(backward_demodulation,[],[f421,f509])).
% 1.79/0.60  % SZS output end Proof for theBenchmark
% 1.79/0.60  % (4976)------------------------------
% 1.79/0.60  % (4976)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.79/0.60  % (4976)Termination reason: Refutation
% 1.79/0.60  
% 1.79/0.60  % (4976)Memory used [KB]: 6780
% 1.79/0.60  % (4976)Time elapsed: 0.173 s
% 1.79/0.60  % (4976)------------------------------
% 1.79/0.60  % (4976)------------------------------
% 1.79/0.60  % (4948)Success in time 0.234 s
%------------------------------------------------------------------------------
