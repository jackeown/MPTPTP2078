%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:19 EST 2020

% Result     : Theorem 2.40s
% Output     : Refutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :  372 (377374796 expanded)
%              Number of leaves         :   12 (69271106 expanded)
%              Depth                    :  103
%              Number of atoms          : 1478 (2766108467 expanded)
%              Number of equality atoms :  519 (376608054 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2304,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f2264])).

fof(f2264,plain,(
    k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k1_xboole_0,k1_xboole_0)) != k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f1950,f2253])).

fof(f2253,plain,(
    k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f2250,f2243])).

fof(f2243,plain,
    ( r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f2242,f2191])).

fof(f2191,plain,
    ( sK4(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f2189,f2099])).

fof(f2099,plain,
    ( r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | sK4(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) ),
    inference(resolution,[],[f2074,f1960])).

fof(f1960,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_xboole_0)
      | k1_funct_1(k1_xboole_0,X3) = X3 ) ),
    inference(backward_demodulation,[],[f1811,f1921])).

fof(f1921,plain,(
    k1_xboole_0 = u1_struct_0(sK1) ),
    inference(trivial_inequality_removal,[],[f1816])).

fof(f1816,plain,
    ( k1_funct_1(k1_xboole_0,sK3(u1_struct_0(sK1),k1_xboole_0,k1_xboole_0)) != k1_funct_1(k1_xboole_0,sK3(u1_struct_0(sK1),k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(backward_demodulation,[],[f809,f1791])).

fof(f1791,plain,(
    k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f1664])).

fof(f1664,plain,
    ( k1_funct_1(sK2,sK3(u1_struct_0(sK1),sK2,sK2)) != k1_funct_1(sK2,sK3(u1_struct_0(sK1),sK2,sK2))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f194,f1622])).

fof(f1622,plain,
    ( sK2 = k4_tmap_1(sK0,sK1)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f1617,f1594])).

fof(f1594,plain,
    ( r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1592,f1086])).

fof(f1086,plain,
    ( r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2
    | sK4(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) ),
    inference(duplicate_literal_removal,[],[f1083])).

fof(f1083,plain,
    ( r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2
    | sK4(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f1080,f787])).

fof(f787,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k1_xboole_0)
      | k1_funct_1(sK2,X5) = X5
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f727,f741])).

fof(f741,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f737,f702])).

fof(f702,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0))) ),
    inference(backward_demodulation,[],[f36,f699])).

fof(f699,plain,(
    k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f593,f149])).

fof(f149,plain,(
    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2) ),
    inference(subsumption_resolution,[],[f148,f36])).

fof(f148,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2) ),
    inference(subsumption_resolution,[],[f147,f34])).

fof(f34,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X2) )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_hidden(X3,u1_struct_0(X1))
                       => k1_funct_1(X2,X3) = X3 ) )
                 => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,u1_struct_0(X1))
                     => k1_funct_1(X2,X3) = X3 ) )
               => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_tmap_1)).

fof(f147,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2) ),
    inference(trivial_inequality_removal,[],[f144])).

fof(f144,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k1_funct_1(sK2,sK3(u1_struct_0(sK1),sK2,sK2)) != k1_funct_1(sK2,sK3(u1_struct_0(sK1),sK2,sK2))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2) ),
    inference(resolution,[],[f104,f35])).

fof(f35,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f104,plain,(
    ! [X1] :
      ( ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | k1_funct_1(sK2,sK3(u1_struct_0(sK1),sK2,X1)) != k1_funct_1(X1,sK3(u1_struct_0(sK1),sK2,X1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X1) ) ),
    inference(subsumption_resolution,[],[f103,f36])).

fof(f103,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | k1_funct_1(sK2,sK3(u1_struct_0(sK1),sK2,X1)) != k1_funct_1(X1,sK3(u1_struct_0(sK1),sK2,X1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X1) ) ),
    inference(subsumption_resolution,[],[f99,f34])).

fof(f99,plain,(
    ! [X1] :
      ( ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | k1_funct_1(sK2,sK3(u1_struct_0(sK1),sK2,X1)) != k1_funct_1(X1,sK3(u1_struct_0(sK1),sK2,X1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X1) ) ),
    inference(resolution,[],[f35,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_funct_1(X2,sK3(X0,X2,X3)) != k1_funct_1(X3,sK3(X0,X2,X3))
      | r2_funct_2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_2)).

fof(f593,plain,
    ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(superposition,[],[f37,f582])).

fof(f582,plain,
    ( sK2 = k4_tmap_1(sK0,sK1)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f576,f581])).

fof(f581,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK2 = k4_tmap_1(sK0,sK1)
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f580,f408])).

fof(f408,plain,
    ( k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f407,f34])).

fof(f407,plain,
    ( ~ v1_funct_1(sK2)
    | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f399,f114])).

fof(f114,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f110,f57])).

fof(f57,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f110,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f36,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f399,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(resolution,[],[f282,f70])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f282,plain,(
    ! [X3] :
      ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X3))
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X3)
      | k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),X3)) != k1_funct_1(X3,sK4(k4_tmap_1(sK0,sK1),X3))
      | r1_tarski(k4_tmap_1(sK0,sK1),X3)
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f281,f128])).

fof(f128,plain,(
    v1_relat_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f125,f57])).

fof(f125,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | v1_relat_1(k4_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f96,f62])).

fof(f96,plain,(
    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f95,f40])).

fof(f40,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f95,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f94,f42])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f94,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f82,f41])).

fof(f41,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f82,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f39,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_tmap_1)).

fof(f39,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f281,plain,(
    ! [X3] :
      ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X3))
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),X3)) != k1_funct_1(X3,sK4(k4_tmap_1(sK0,sK1),X3))
      | r1_tarski(k4_tmap_1(sK0,sK1),X3)
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f271,f90])).

fof(f90,plain,(
    v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f89,f40])).

fof(f89,plain,
    ( v2_struct_0(sK0)
    | v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f88,f42])).

fof(f88,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f80,f41])).

fof(f80,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f39,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_funct_1(k4_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f271,plain,(
    ! [X3] :
      ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X3))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),X3)) != k1_funct_1(X3,sK4(k4_tmap_1(sK0,sK1),X3))
      | r1_tarski(k4_tmap_1(sK0,sK1),X3)
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(superposition,[],[f51,f264])).

fof(f264,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f261])).

fof(f261,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(superposition,[],[f221,f222])).

fof(f222,plain,
    ( k1_relat_1(k4_tmap_1(sK0,sK1)) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(superposition,[],[f124,f113])).

fof(f113,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK2)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(backward_demodulation,[],[f100,f109])).

fof(f109,plain,(
    k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f36,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f100,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) ),
    inference(subsumption_resolution,[],[f97,f36])).

fof(f97,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f35,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f124,plain,(
    k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1)) = k1_relat_1(k4_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f96,f58])).

fof(f221,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f220,f140])).

fof(f140,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK0))))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(superposition,[],[f96,f113])).

fof(f220,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK0)))) ),
    inference(duplicate_literal_removal,[],[f217])).

fof(f217,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK0)
    | k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f139,f68])).

fof(f139,plain,
    ( v1_funct_2(k4_tmap_1(sK0,sK1),k1_relat_1(sK2),u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(superposition,[],[f93,f113])).

fof(f93,plain,(
    v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f92,f40])).

fof(f92,plain,
    ( v2_struct_0(sK0)
    | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f91,f42])).

fof(f91,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f81,f41])).

fof(f81,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f39,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
          <=> ( ! [X2] :
                  ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                  | ~ r2_hidden(X2,k1_relat_1(X0)) )
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
          <=> ( ! [X2] :
                  ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                  | ~ r2_hidden(X2,k1_relat_1(X0)) )
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( r1_tarski(X0,X1)
          <=> ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_grfunc_1)).

fof(f580,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK2 = k4_tmap_1(sK0,sK1)
    | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f579,f90])).

fof(f579,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f578,f128])).

fof(f578,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(duplicate_literal_removal,[],[f572])).

fof(f572,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK2 = k4_tmap_1(sK0,sK1)
    | k1_xboole_0 = u1_struct_0(sK0)
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(resolution,[],[f571,f380])).

fof(f380,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,X0)
      | k1_xboole_0 = u1_struct_0(sK0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(X0,sK4(k4_tmap_1(sK0,sK1),sK2))
      | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ) ),
    inference(subsumption_resolution,[],[f379,f114])).

fof(f379,plain,(
    ! [X0] :
      ( r1_tarski(k4_tmap_1(sK0,sK1),sK2)
      | k1_xboole_0 = u1_struct_0(sK0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(sK2)
      | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(X0,sK4(k4_tmap_1(sK0,sK1),sK2))
      | ~ r1_tarski(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f376,f34])).

fof(f376,plain,(
    ! [X0] :
      ( r1_tarski(k4_tmap_1(sK0,sK1),sK2)
      | k1_xboole_0 = u1_struct_0(sK0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(sK2)
      | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(X0,sK4(k4_tmap_1(sK0,sK1),sK2))
      | ~ r1_tarski(sK2,X0) ) ),
    inference(resolution,[],[f374,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f374,plain,
    ( r2_hidden(sK4(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f373,f34])).

fof(f373,plain,
    ( ~ v1_funct_1(sK2)
    | r2_hidden(sK4(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f367,f114])).

fof(f367,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | r2_hidden(sK4(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(resolution,[],[f278,f70])).

fof(f278,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | r2_hidden(sK4(k4_tmap_1(sK0,sK1),X1),k1_relat_1(sK2))
      | r1_tarski(k4_tmap_1(sK0,sK1),X1)
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f277,f128])).

fof(f277,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
      | r2_hidden(sK4(k4_tmap_1(sK0,sK1),X1),k1_relat_1(sK2))
      | r1_tarski(k4_tmap_1(sK0,sK1),X1)
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f269,f90])).

fof(f269,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(X1))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
      | r2_hidden(sK4(k4_tmap_1(sK0,sK1),X1),k1_relat_1(sK2))
      | r1_tarski(k4_tmap_1(sK0,sK1),X1)
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(superposition,[],[f50,f264])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f571,plain,
    ( r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f570,f431])).

fof(f431,plain,
    ( r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f430,f334])).

fof(f334,plain,
    ( r2_hidden(sK4(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f333,f114])).

fof(f333,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(sK4(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f327,f34])).

fof(f327,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | r2_hidden(sK4(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(resolution,[],[f276,f70])).

fof(f276,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_relat_1(sK2))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK4(X0,k4_tmap_1(sK0,sK1)),k1_relat_1(X0))
      | r1_tarski(X0,k4_tmap_1(sK0,sK1))
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f275,f90])).

fof(f275,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_relat_1(sK2))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_relat_1(X0)
      | r2_hidden(sK4(X0,k4_tmap_1(sK0,sK1)),k1_relat_1(X0))
      | r1_tarski(X0,k4_tmap_1(sK0,sK1))
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f268,f128])).

fof(f268,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_relat_1(sK2))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_relat_1(X0)
      | r2_hidden(sK4(X0,k4_tmap_1(sK0,sK1)),k1_relat_1(X0))
      | r1_tarski(X0,k4_tmap_1(sK0,sK1))
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(superposition,[],[f50,f264])).

fof(f430,plain,
    ( ~ r2_hidden(sK4(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(duplicate_literal_removal,[],[f429])).

fof(f429,plain,
    ( ~ r2_hidden(sK4(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(superposition,[],[f365,f113])).

fof(f365,plain,
    ( ~ r2_hidden(sK4(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f346,f33])).

fof(f33,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(X3,u1_struct_0(sK1))
      | k1_funct_1(sK2,X3) = X3 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f346,plain,
    ( m1_subset_1(sK4(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK0)
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f343])).

fof(f343,plain,
    ( r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | m1_subset_1(sK4(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(resolution,[],[f334,f142])).

fof(f142,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK2))
      | m1_subset_1(X1,u1_struct_0(sK0))
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(superposition,[],[f106,f113])).

fof(f106,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(sK1))
      | m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f83,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f83,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f78,f42])).

fof(f78,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f39,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f570,plain,
    ( sK4(sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f569])).

fof(f569,plain,
    ( sK4(sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(superposition,[],[f395,f488])).

fof(f488,plain,
    ( sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f481,f487])).

fof(f487,plain,
    ( r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f486,f408])).

fof(f486,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1)))
    | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f485,f90])).

fof(f485,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f484,f128])).

fof(f484,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1)))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(duplicate_literal_removal,[],[f479])).

fof(f479,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = u1_struct_0(sK0)
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(resolution,[],[f451,f380])).

fof(f451,plain,
    ( r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f450,f334])).

fof(f450,plain,
    ( ~ r2_hidden(sK4(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(duplicate_literal_removal,[],[f449])).

fof(f449,plain,
    ( ~ r2_hidden(sK4(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(superposition,[],[f364,f113])).

fof(f364,plain,
    ( ~ r2_hidden(sK4(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0)
    | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f346,f87])).

fof(f87,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(subsumption_resolution,[],[f86,f40])).

fof(f86,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(subsumption_resolution,[],[f85,f38])).

fof(f38,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f85,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(subsumption_resolution,[],[f84,f42])).

fof(f84,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(subsumption_resolution,[],[f79,f41])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(resolution,[],[f39,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,u1_struct_0(X1))
      | k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
              | ~ r2_hidden(X2,u1_struct_0(X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
              | ~ r2_hidden(X2,u1_struct_0(X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_pre_topc(X1,X0)
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
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,u1_struct_0(X1))
               => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_tmap_1)).

fof(f481,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1)))
    | ~ r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f451,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f395,plain,
    ( k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f394,f114])).

fof(f394,plain,
    ( ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f386,f34])).

fof(f386,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(resolution,[],[f280,f70])).

fof(f280,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_relat_1(X2),k1_relat_1(sK2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,sK4(X2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(X2,k4_tmap_1(sK0,sK1)))
      | r1_tarski(X2,k4_tmap_1(sK0,sK1))
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f279,f90])).

fof(f279,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_relat_1(X2),k1_relat_1(sK2))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,sK4(X2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(X2,k4_tmap_1(sK0,sK1)))
      | r1_tarski(X2,k4_tmap_1(sK0,sK1))
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f270,f128])).

fof(f270,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_relat_1(X2),k1_relat_1(sK2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,sK4(X2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(X2,k4_tmap_1(sK0,sK1)))
      | r1_tarski(X2,k4_tmap_1(sK0,sK1))
      | k1_xboole_0 = u1_struct_0(sK0) ) ),
    inference(superposition,[],[f51,f264])).

fof(f576,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(duplicate_literal_removal,[],[f574])).

fof(f574,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f571,f61])).

fof(f37,plain,(
    ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f16])).

fof(f737,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0))) ),
    inference(resolution,[],[f701,f73])).

fof(f73,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f701,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),k1_xboole_0) ),
    inference(backward_demodulation,[],[f35,f699])).

fof(f727,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,u1_struct_0(sK1))
      | k1_funct_1(sK2,X3) = X3 ) ),
    inference(global_subsumption,[],[f33,f106])).

fof(f1080,plain,
    ( r2_hidden(sK4(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0)
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f1079,f128])).

fof(f1079,plain,
    ( ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK4(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0)
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f1078,f90])).

fof(f1078,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK4(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0)
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f1076,f70])).

fof(f1076,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK4(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0)
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f1075])).

fof(f1075,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK4(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0)
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f890,f932])).

fof(f932,plain,
    ( k1_xboole_0 = k1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f929])).

fof(f929,plain,
    ( k1_xboole_0 = k1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f849,f819])).

fof(f819,plain,
    ( k1_relat_1(k4_tmap_1(sK0,sK1)) = k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f718,f741])).

fof(f718,plain,(
    k1_relat_1(k4_tmap_1(sK0,sK1)) = k1_relset_1(u1_struct_0(sK1),k1_xboole_0,k4_tmap_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f124,f699])).

fof(f849,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f843,f782])).

fof(f782,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f707,f741])).

fof(f707,plain,(
    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0))) ),
    inference(backward_demodulation,[],[f96,f699])).

fof(f843,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f781,f71])).

fof(f71,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f781,plain,
    ( v1_funct_2(k4_tmap_1(sK0,sK1),k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f706,f741])).

fof(f706,plain,(
    v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),k1_xboole_0) ),
    inference(backward_demodulation,[],[f93,f699])).

fof(f890,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(X1),k1_xboole_0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r2_hidden(sK4(X1,sK2),k1_relat_1(X1))
      | r1_tarski(X1,sK2)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f889,f34])).

fof(f889,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(X1),k1_xboole_0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(X1)
      | r2_hidden(sK4(X1,sK2),k1_relat_1(X1))
      | r1_tarski(X1,sK2)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f883,f114])).

fof(f883,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(X1),k1_xboole_0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(X1)
      | r2_hidden(sK4(X1,sK2),k1_relat_1(X1))
      | r1_tarski(X1,sK2)
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f50,f875])).

fof(f875,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f872])).

fof(f872,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f830,f804])).

fof(f804,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f713,f741])).

fof(f713,plain,(
    k1_relat_1(sK2) = k1_relset_1(u1_struct_0(sK1),k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f109,f699])).

fof(f830,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f824,f778])).

fof(f778,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f702,f741])).

fof(f824,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f777,f71])).

fof(f777,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f701,f741])).

fof(f1592,plain,
    ( sK4(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f1591])).

fof(f1591,plain,
    ( sK4(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(superposition,[],[f1137,f1406])).

fof(f1406,plain,
    ( sK4(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1401,f1087])).

fof(f1087,plain,
    ( r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2
    | sK4(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2)) ),
    inference(duplicate_literal_removal,[],[f1082])).

fof(f1082,plain,
    ( r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2
    | sK4(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f1080,f788])).

fof(f788,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,k1_xboole_0)
      | k1_funct_1(k4_tmap_1(sK0,sK1),X6) = X6
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f728,f741])).

fof(f728,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(global_subsumption,[],[f87,f106])).

fof(f1401,plain,
    ( k1_xboole_0 = sK2
    | sK4(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2))
    | ~ r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f1311,f61])).

fof(f1311,plain,
    ( r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | sK4(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f1310,f1122])).

fof(f1122,plain,
    ( k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f1121,f90])).

fof(f1121,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f1120,f128])).

fof(f1120,plain,
    ( ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f1117,f70])).

fof(f1117,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f1116])).

fof(f1116,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f892,f932])).

fof(f892,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(sK2,sK4(sK2,X2)) != k1_funct_1(X2,sK4(sK2,X2))
      | r1_tarski(sK2,X2)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f891,f114])).

fof(f891,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(sK2)
      | k1_funct_1(sK2,sK4(sK2,X2)) != k1_funct_1(X2,sK4(sK2,X2))
      | r1_tarski(sK2,X2)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f884,f34])).

fof(f884,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X2))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(sK2)
      | k1_funct_1(sK2,sK4(sK2,X2)) != k1_funct_1(X2,sK4(sK2,X2))
      | r1_tarski(sK2,X2)
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f51,f875])).

fof(f1310,plain,
    ( k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = sK2
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | sK4(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f1309,f114])).

fof(f1309,plain,
    ( k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1)))
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | sK4(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f1307,f34])).

fof(f1307,plain,
    ( ~ v1_funct_1(sK2)
    | k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1)))
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | sK4(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2)) ),
    inference(duplicate_literal_removal,[],[f1301])).

fof(f1301,plain,
    ( ~ v1_funct_1(sK2)
    | k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1)))
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | sK4(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2)) ),
    inference(resolution,[],[f1114,f1087])).

fof(f1114,plain,(
    ! [X0] :
      ( ~ r1_tarski(k4_tmap_1(sK0,sK1),X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK4(sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1)))
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = sK2
      | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) ) ),
    inference(duplicate_literal_removal,[],[f1111])).

fof(f1111,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK4(sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1)))
      | ~ r1_tarski(k4_tmap_1(sK0,sK1),X0)
      | k1_xboole_0 = sK2
      | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
      | k1_xboole_0 = sK2 ) ),
    inference(resolution,[],[f952,f1008])).

fof(f1008,plain,
    ( r2_hidden(sK4(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0)
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f1007,f90])).

fof(f1007,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK4(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0)
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f1006,f128])).

fof(f1006,plain,
    ( ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK4(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0)
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f1004,f70])).

fof(f1004,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK4(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0)
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f1003])).

fof(f1003,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK4(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0)
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f888,f932])).

fof(f888,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK4(sK2,X0),k1_xboole_0)
      | r1_tarski(sK2,X0)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f887,f114])).

fof(f887,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(sK2)
      | r2_hidden(sK4(sK2,X0),k1_xboole_0)
      | r1_tarski(sK2,X0)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f882,f34])).

fof(f882,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(sK2)
      | r2_hidden(sK4(sK2,X0),k1_xboole_0)
      | r1_tarski(sK2,X0)
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f50,f875])).

fof(f952,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(X5)
      | k1_funct_1(k4_tmap_1(sK0,sK1),X4) = k1_funct_1(X5,X4)
      | ~ r1_tarski(k4_tmap_1(sK0,sK1),X5)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f951,f128])).

fof(f951,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X4) = k1_funct_1(X5,X4)
      | ~ r1_tarski(k4_tmap_1(sK0,sK1),X5)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f942,f90])).

fof(f942,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X4) = k1_funct_1(X5,X4)
      | ~ r1_tarski(k4_tmap_1(sK0,sK1),X5)
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f52,f932])).

fof(f1137,plain,
    ( k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f1136,f128])).

fof(f1136,plain,
    ( ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f1135,f90])).

fof(f1135,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f1132,f70])).

fof(f1132,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f1131])).

fof(f1131,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2))
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f894,f932])).

fof(f894,plain,(
    ! [X3] :
      ( ~ r1_tarski(k1_relat_1(X3),k1_xboole_0)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | k1_funct_1(X3,sK4(X3,sK2)) != k1_funct_1(sK2,sK4(X3,sK2))
      | r1_tarski(X3,sK2)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f893,f34])).

fof(f893,plain,(
    ! [X3] :
      ( ~ r1_tarski(k1_relat_1(X3),k1_xboole_0)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(X3)
      | k1_funct_1(X3,sK4(X3,sK2)) != k1_funct_1(sK2,sK4(X3,sK2))
      | r1_tarski(X3,sK2)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f885,f114])).

fof(f885,plain,(
    ! [X3] :
      ( ~ r1_tarski(k1_relat_1(X3),k1_xboole_0)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(X3)
      | k1_funct_1(X3,sK4(X3,sK2)) != k1_funct_1(sK2,sK4(X3,sK2))
      | r1_tarski(X3,sK2)
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f51,f875])).

fof(f1617,plain,
    ( k1_xboole_0 = sK2
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ r1_tarski(k4_tmap_1(sK0,sK1),sK2) ),
    inference(duplicate_literal_removal,[],[f1613])).

fof(f1613,plain,
    ( k1_xboole_0 = sK2
    | sK2 = k4_tmap_1(sK0,sK1)
    | ~ r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f1589,f61])).

fof(f1589,plain,
    ( r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1587,f1033])).

fof(f1033,plain,
    ( r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(duplicate_literal_removal,[],[f1030])).

fof(f1030,plain,
    ( r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f1008,f787])).

fof(f1587,plain,
    ( sK4(sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f1586])).

fof(f1586,plain,
    ( sK4(sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1)))
    | r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(superposition,[],[f1122,f1394])).

fof(f1394,plain,
    ( sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = sK2
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1389,f1034])).

fof(f1034,plain,
    ( r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(duplicate_literal_removal,[],[f1029])).

fof(f1029,plain,
    ( r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f1008,f788])).

fof(f1389,plain,
    ( k1_xboole_0 = sK2
    | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1)))
    | ~ r1_tarski(sK2,k4_tmap_1(sK0,sK1))
    | sK2 = k4_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f1273,f61])).

fof(f1273,plain,
    ( r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2
    | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f1272,f1137])).

fof(f1272,plain,
    ( k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f1271,f128])).

fof(f1271,plain,
    ( k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f1270,f90])).

fof(f1270,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(duplicate_literal_removal,[],[f1265])).

fof(f1265,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
    | k1_xboole_0 = sK2
    | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f1090,f1034])).

fof(f1090,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK2,X1)
      | ~ v1_funct_1(X1)
      | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(X1,sK4(k4_tmap_1(sK0,sK1),sK2))
      | ~ v1_relat_1(X1)
      | k1_xboole_0 = sK2
      | r1_tarski(k4_tmap_1(sK0,sK1),sK2) ) ),
    inference(duplicate_literal_removal,[],[f1089])).

fof(f1089,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(X1,sK4(k4_tmap_1(sK0,sK1),sK2))
      | ~ r1_tarski(sK2,X1)
      | k1_xboole_0 = sK2
      | r1_tarski(k4_tmap_1(sK0,sK1),sK2)
      | k1_xboole_0 = sK2 ) ),
    inference(resolution,[],[f896,f1080])).

fof(f896,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(X5)
      | k1_funct_1(X5,X4) = k1_funct_1(sK2,X4)
      | ~ r1_tarski(sK2,X5)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f895,f114])).

fof(f895,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(sK2)
      | k1_funct_1(X5,X4) = k1_funct_1(sK2,X4)
      | ~ r1_tarski(sK2,X5)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f886,f34])).

fof(f886,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(sK2)
      | k1_funct_1(X5,X4) = k1_funct_1(sK2,X4)
      | ~ r1_tarski(sK2,X5)
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f52,f875])).

fof(f194,plain,(
    k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) ),
    inference(subsumption_resolution,[],[f193,f37])).

fof(f193,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f192,f36])).

fof(f192,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f188,f34])).

fof(f188,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) ),
    inference(resolution,[],[f122,f35])).

fof(f122,plain,(
    ! [X1] :
      ( ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),X1)) != k1_funct_1(X1,sK3(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),X1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X1) ) ),
    inference(subsumption_resolution,[],[f121,f96])).

fof(f121,plain,(
    ! [X1] :
      ( ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),X1)) != k1_funct_1(X1,sK3(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),X1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X1) ) ),
    inference(subsumption_resolution,[],[f117,f90])).

fof(f117,plain,(
    ! [X1] :
      ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),X1)) != k1_funct_1(X1,sK3(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),X1))
      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X1) ) ),
    inference(resolution,[],[f93,f45])).

fof(f809,plain,
    ( k1_funct_1(k1_xboole_0,sK3(u1_struct_0(sK1),k1_xboole_0,sK2)) != k1_funct_1(sK2,sK3(u1_struct_0(sK1),k1_xboole_0,sK2))
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(superposition,[],[f194,f754])).

fof(f754,plain,
    ( k1_xboole_0 = k4_tmap_1(sK0,sK1)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f750,f707])).

fof(f750,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | k1_xboole_0 = k4_tmap_1(sK0,sK1)
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0))) ),
    inference(resolution,[],[f706,f73])).

fof(f1811,plain,(
    ! [X3] :
      ( k1_funct_1(k1_xboole_0,X3) = X3
      | ~ r2_hidden(X3,u1_struct_0(sK1)) ) ),
    inference(backward_demodulation,[],[f727,f1791])).

fof(f2074,plain,
    ( r2_hidden(sK4(k4_tmap_1(sK0,sK1),k1_xboole_0),k1_xboole_0)
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f2073,f128])).

fof(f2073,plain,
    ( ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK4(k4_tmap_1(sK0,sK1),k1_xboole_0),k1_xboole_0)
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f2072,f90])).

fof(f2072,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK4(k4_tmap_1(sK0,sK1),k1_xboole_0),k1_xboole_0)
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f2071,f70])).

fof(f2071,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK4(k4_tmap_1(sK0,sK1),k1_xboole_0),k1_xboole_0)
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) ),
    inference(superposition,[],[f2032,f2007])).

fof(f2007,plain,(
    k1_xboole_0 = k1_relat_1(k4_tmap_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f1934,f2006])).

fof(f2006,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f2001,f1930])).

fof(f1930,plain,(
    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f707,f1921])).

fof(f2001,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f1929,f71])).

fof(f1929,plain,(
    v1_funct_2(k4_tmap_1(sK0,sK1),k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f706,f1921])).

fof(f1934,plain,(
    k1_relat_1(k4_tmap_1(sK0,sK1)) = k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f718,f1921])).

fof(f2032,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(X1),k1_xboole_0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r2_hidden(sK4(X1,k1_xboole_0),k1_relat_1(X1))
      | r1_tarski(X1,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f2031,f1793])).

fof(f1793,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f34,f1791])).

fof(f2031,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(X1),k1_xboole_0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(X1)
      | r2_hidden(sK4(X1,k1_xboole_0),k1_relat_1(X1))
      | r1_tarski(X1,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f2025,f1794])).

fof(f1794,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f114,f1791])).

fof(f2025,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(X1),k1_xboole_0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(X1)
      | r2_hidden(sK4(X1,k1_xboole_0),k1_relat_1(X1))
      | r1_tarski(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f50,f1989])).

fof(f1989,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f1956,f1988])).

fof(f1988,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1982,f1954])).

fof(f1954,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f1803,f1921])).

fof(f1803,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0))) ),
    inference(backward_demodulation,[],[f702,f1791])).

fof(f1982,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f1953,f71])).

fof(f1953,plain,(
    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f1802,f1921])).

fof(f1802,plain,(
    v1_funct_2(k1_xboole_0,u1_struct_0(sK1),k1_xboole_0) ),
    inference(backward_demodulation,[],[f701,f1791])).

fof(f1956,plain,(
    k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f1805,f1921])).

fof(f1805,plain,(
    k1_relat_1(k1_xboole_0) = k1_relset_1(u1_struct_0(sK1),k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f713,f1791])).

fof(f2189,plain,
    ( sK4(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | ~ r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f2170,f61])).

fof(f2170,plain,
    ( r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | sK4(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f2169,f2089])).

fof(f2089,plain,
    ( k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f2088,f90])).

fof(f2088,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f2087,f128])).

fof(f2087,plain,
    ( ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f2086,f70])).

fof(f2086,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) ),
    inference(superposition,[],[f2034,f2007])).

fof(f2034,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,X2)) != k1_funct_1(X2,sK4(k1_xboole_0,X2))
      | r1_tarski(k1_xboole_0,X2) ) ),
    inference(subsumption_resolution,[],[f2033,f1794])).

fof(f2033,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(k1_xboole_0)
      | k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,X2)) != k1_funct_1(X2,sK4(k1_xboole_0,X2))
      | r1_tarski(k1_xboole_0,X2) ) ),
    inference(subsumption_resolution,[],[f2026,f1793])).

fof(f2026,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X2))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(k1_xboole_0)
      | k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,X2)) != k1_funct_1(X2,sK4(k1_xboole_0,X2))
      | r1_tarski(k1_xboole_0,X2) ) ),
    inference(superposition,[],[f51,f1989])).

fof(f2169,plain,
    ( k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | sK4(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f2168,f1794])).

fof(f2168,plain,
    ( k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | ~ v1_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | sK4(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f2162,f1793])).

fof(f2162,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | ~ v1_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | sK4(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) ),
    inference(resolution,[],[f2084,f2099])).

fof(f2084,plain,(
    ! [X0] :
      ( ~ r1_tarski(k4_tmap_1(sK0,sK1),X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(X0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)))
      | ~ v1_relat_1(X0)
      | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) ) ),
    inference(resolution,[],[f2061,f2069])).

fof(f2069,plain,
    ( r2_hidden(sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)),k1_xboole_0)
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f2068,f90])).

fof(f2068,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)),k1_xboole_0)
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f2067,f128])).

fof(f2067,plain,
    ( ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)),k1_xboole_0)
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f2066,f70])).

fof(f2066,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | r2_hidden(sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)),k1_xboole_0)
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) ),
    inference(superposition,[],[f2030,f2007])).

fof(f2030,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK4(k1_xboole_0,X0),k1_xboole_0)
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f2029,f1794])).

fof(f2029,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(k1_xboole_0)
      | r2_hidden(sK4(k1_xboole_0,X0),k1_xboole_0)
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f2024,f1793])).

fof(f2024,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(k1_xboole_0)
      | r2_hidden(sK4(k1_xboole_0,X0),k1_xboole_0)
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f50,f1989])).

fof(f2061,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(X5)
      | k1_funct_1(k4_tmap_1(sK0,sK1),X4) = k1_funct_1(X5,X4)
      | ~ r1_tarski(k4_tmap_1(sK0,sK1),X5) ) ),
    inference(subsumption_resolution,[],[f2060,f128])).

fof(f2060,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X4) = k1_funct_1(X5,X4)
      | ~ r1_tarski(k4_tmap_1(sK0,sK1),X5) ) ),
    inference(subsumption_resolution,[],[f2051,f90])).

fof(f2051,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
      | k1_funct_1(k4_tmap_1(sK0,sK1),X4) = k1_funct_1(X5,X4)
      | ~ r1_tarski(k4_tmap_1(sK0,sK1),X5) ) ),
    inference(superposition,[],[f52,f2007])).

fof(f2242,plain,
    ( sK4(k4_tmap_1(sK0,sK1),k1_xboole_0) != k1_funct_1(k1_xboole_0,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(superposition,[],[f2094,f2214])).

fof(f2214,plain,
    ( sK4(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f2212,f2097])).

fof(f2097,plain,
    ( r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | sK4(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) ),
    inference(resolution,[],[f2074,f1939])).

fof(f1939,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0 ) ),
    inference(backward_demodulation,[],[f728,f1921])).

fof(f2212,plain,
    ( sK4(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | ~ r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f2167,f61])).

fof(f2167,plain,
    ( r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | sK4(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f2166,f2089])).

fof(f2166,plain,
    ( k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | sK4(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f2165,f1794])).

fof(f2165,plain,
    ( k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | ~ v1_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | sK4(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f2161,f1793])).

fof(f2161,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | ~ v1_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | sK4(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) ),
    inference(resolution,[],[f2084,f2097])).

fof(f2094,plain,
    ( k1_funct_1(k1_xboole_0,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f2093,f128])).

fof(f2093,plain,
    ( ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(k1_xboole_0,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f2092,f90])).

fof(f2092,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(k1_xboole_0,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f2091,f70])).

fof(f2091,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(k1_xboole_0,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) ),
    inference(superposition,[],[f2036,f2007])).

fof(f2036,plain,(
    ! [X3] :
      ( ~ r1_tarski(k1_relat_1(X3),k1_xboole_0)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | k1_funct_1(X3,sK4(X3,k1_xboole_0)) != k1_funct_1(k1_xboole_0,sK4(X3,k1_xboole_0))
      | r1_tarski(X3,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f2035,f1793])).

fof(f2035,plain,(
    ! [X3] :
      ( ~ r1_tarski(k1_relat_1(X3),k1_xboole_0)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(X3)
      | k1_funct_1(X3,sK4(X3,k1_xboole_0)) != k1_funct_1(k1_xboole_0,sK4(X3,k1_xboole_0))
      | r1_tarski(X3,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f2027,f1794])).

fof(f2027,plain,(
    ! [X3] :
      ( ~ r1_tarski(k1_relat_1(X3),k1_xboole_0)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(X3)
      | k1_funct_1(X3,sK4(X3,k1_xboole_0)) != k1_funct_1(k1_xboole_0,sK4(X3,k1_xboole_0))
      | r1_tarski(X3,k1_xboole_0) ) ),
    inference(superposition,[],[f51,f1989])).

fof(f2250,plain,
    ( k1_xboole_0 = k4_tmap_1(sK0,sK1)
    | ~ r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f2248])).

fof(f2248,plain,
    ( k1_xboole_0 = k4_tmap_1(sK0,sK1)
    | ~ r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f2241,f61])).

fof(f2241,plain,
    ( r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f2240,f2180])).

fof(f2180,plain,
    ( sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f2175])).

fof(f2175,plain,
    ( sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f2160,f2113])).

fof(f2113,plain,
    ( ~ r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f2080,f61])).

fof(f2080,plain,
    ( r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f2069,f1960])).

fof(f2160,plain,
    ( r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f2159,f2094])).

fof(f2159,plain,
    ( k1_funct_1(k1_xboole_0,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f2158,f90])).

fof(f2158,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(k1_xboole_0,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f2152,f128])).

fof(f2152,plain,
    ( ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(k1_xboole_0,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f2096,f2080])).

fof(f2096,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_xboole_0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_funct_1(k1_xboole_0,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(X1,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0))
      | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) ) ),
    inference(resolution,[],[f2074,f2038])).

fof(f2038,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(X5)
      | k1_funct_1(X5,X4) = k1_funct_1(k1_xboole_0,X4)
      | ~ r1_tarski(k1_xboole_0,X5) ) ),
    inference(subsumption_resolution,[],[f2037,f1794])).

fof(f2037,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(k1_xboole_0)
      | k1_funct_1(X5,X4) = k1_funct_1(k1_xboole_0,X4)
      | ~ r1_tarski(k1_xboole_0,X5) ) ),
    inference(subsumption_resolution,[],[f2028,f1793])).

fof(f2028,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(k1_xboole_0)
      | k1_funct_1(X5,X4) = k1_funct_1(k1_xboole_0,X4)
      | ~ r1_tarski(k1_xboole_0,X5) ) ),
    inference(superposition,[],[f52,f1989])).

fof(f2240,plain,
    ( sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)) != k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(superposition,[],[f2089,f2203])).

fof(f2203,plain,
    ( sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f2201,f2078])).

fof(f2078,plain,
    ( r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f2069,f1939])).

fof(f2201,plain,
    ( sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)))
    | ~ r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))
    | k1_xboole_0 = k4_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f2157,f61])).

fof(f2157,plain,
    ( r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f2156,f2094])).

fof(f2156,plain,
    ( k1_funct_1(k1_xboole_0,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f2155,f90])).

fof(f2155,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(k1_xboole_0,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f2151,f128])).

fof(f2151,plain,
    ( ~ v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k1_funct_1(k1_xboole_0,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),k1_xboole_0))
    | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)
    | sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f2096,f2078])).

fof(f1950,plain,(
    k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1),k1_xboole_0)) != k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1),k1_xboole_0)) ),
    inference(backward_demodulation,[],[f1799,f1921])).

fof(f1799,plain,(
    k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),k1_xboole_0)) != k1_funct_1(k1_xboole_0,sK3(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),k1_xboole_0)) ),
    inference(backward_demodulation,[],[f194,f1791])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:38:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.51  % (32023)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.51  % (32017)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.52  % (32015)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.53  % (32020)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.53  % (32025)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.53  % (32016)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (32019)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.54  % (32036)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.54  % (32015)Refutation not found, incomplete strategy% (32015)------------------------------
% 0.20/0.54  % (32015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (32015)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (32015)Memory used [KB]: 10618
% 0.20/0.54  % (32015)Time elapsed: 0.098 s
% 0.20/0.54  % (32015)------------------------------
% 0.20/0.54  % (32015)------------------------------
% 0.20/0.55  % (32032)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.55  % (32027)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.55  % (32021)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.55  % (32028)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.55  % (32035)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.46/0.56  % (32024)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.46/0.56  % (32039)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.46/0.57  % (32018)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.67/0.58  % (32016)Refutation not found, incomplete strategy% (32016)------------------------------
% 1.67/0.58  % (32016)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.58  % (32038)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.67/0.58  % (32022)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.67/0.59  % (32026)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.67/0.59  % (32016)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.59  
% 1.67/0.59  % (32016)Memory used [KB]: 11001
% 1.67/0.59  % (32016)Time elapsed: 0.139 s
% 1.67/0.59  % (32016)------------------------------
% 1.67/0.59  % (32016)------------------------------
% 1.67/0.59  % (32037)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.67/0.59  % (32030)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.67/0.60  % (32034)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.67/0.60  % (32029)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.67/0.61  % (32022)Refutation not found, incomplete strategy% (32022)------------------------------
% 1.67/0.61  % (32022)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.61  % (32022)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.61  
% 1.67/0.61  % (32022)Memory used [KB]: 1791
% 1.67/0.61  % (32022)Time elapsed: 0.124 s
% 1.67/0.61  % (32022)------------------------------
% 1.67/0.61  % (32022)------------------------------
% 1.67/0.61  % (32033)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.67/0.62  % (32040)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.67/0.62  % (32031)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 2.40/0.67  % (32020)Refutation found. Thanks to Tanya!
% 2.40/0.67  % SZS status Theorem for theBenchmark
% 2.40/0.67  % (32021)Refutation not found, incomplete strategy% (32021)------------------------------
% 2.40/0.67  % (32021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.40/0.67  % (32021)Termination reason: Refutation not found, incomplete strategy
% 2.40/0.67  
% 2.40/0.67  % (32021)Memory used [KB]: 11001
% 2.40/0.67  % (32021)Time elapsed: 0.247 s
% 2.40/0.67  % (32021)------------------------------
% 2.40/0.67  % (32021)------------------------------
% 2.40/0.67  % SZS output start Proof for theBenchmark
% 2.40/0.67  fof(f2304,plain,(
% 2.40/0.67    $false),
% 2.40/0.67    inference(trivial_inequality_removal,[],[f2264])).
% 2.40/0.67  fof(f2264,plain,(
% 2.40/0.67    k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k1_xboole_0,k1_xboole_0)) != k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k1_xboole_0,k1_xboole_0))),
% 2.40/0.67    inference(backward_demodulation,[],[f1950,f2253])).
% 2.40/0.67  fof(f2253,plain,(
% 2.40/0.67    k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 2.40/0.67    inference(subsumption_resolution,[],[f2250,f2243])).
% 2.40/0.67  fof(f2243,plain,(
% 2.40/0.67    r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 2.40/0.67    inference(subsumption_resolution,[],[f2242,f2191])).
% 2.40/0.67  fof(f2191,plain,(
% 2.40/0.67    sK4(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 2.40/0.67    inference(subsumption_resolution,[],[f2189,f2099])).
% 2.40/0.67  fof(f2099,plain,(
% 2.40/0.67    r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | sK4(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0))),
% 2.40/0.67    inference(resolution,[],[f2074,f1960])).
% 2.40/0.67  fof(f1960,plain,(
% 2.40/0.67    ( ! [X3] : (~r2_hidden(X3,k1_xboole_0) | k1_funct_1(k1_xboole_0,X3) = X3) )),
% 2.40/0.67    inference(backward_demodulation,[],[f1811,f1921])).
% 2.40/0.67  fof(f1921,plain,(
% 2.40/0.67    k1_xboole_0 = u1_struct_0(sK1)),
% 2.40/0.67    inference(trivial_inequality_removal,[],[f1816])).
% 2.40/0.67  fof(f1816,plain,(
% 2.40/0.67    k1_funct_1(k1_xboole_0,sK3(u1_struct_0(sK1),k1_xboole_0,k1_xboole_0)) != k1_funct_1(k1_xboole_0,sK3(u1_struct_0(sK1),k1_xboole_0,k1_xboole_0)) | k1_xboole_0 = u1_struct_0(sK1)),
% 2.40/0.67    inference(backward_demodulation,[],[f809,f1791])).
% 2.40/0.67  fof(f1791,plain,(
% 2.40/0.67    k1_xboole_0 = sK2),
% 2.40/0.67    inference(trivial_inequality_removal,[],[f1664])).
% 2.40/0.67  fof(f1664,plain,(
% 2.40/0.67    k1_funct_1(sK2,sK3(u1_struct_0(sK1),sK2,sK2)) != k1_funct_1(sK2,sK3(u1_struct_0(sK1),sK2,sK2)) | k1_xboole_0 = sK2),
% 2.40/0.67    inference(superposition,[],[f194,f1622])).
% 2.40/0.67  fof(f1622,plain,(
% 2.40/0.67    sK2 = k4_tmap_1(sK0,sK1) | k1_xboole_0 = sK2),
% 2.40/0.67    inference(subsumption_resolution,[],[f1617,f1594])).
% 2.40/0.67  fof(f1594,plain,(
% 2.40/0.67    r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2 | sK2 = k4_tmap_1(sK0,sK1)),
% 2.40/0.67    inference(subsumption_resolution,[],[f1592,f1086])).
% 2.40/0.67  fof(f1086,plain,(
% 2.40/0.67    r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2 | sK4(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2))),
% 2.40/0.67    inference(duplicate_literal_removal,[],[f1083])).
% 2.40/0.67  fof(f1083,plain,(
% 2.40/0.67    r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2 | sK4(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2),
% 2.40/0.67    inference(resolution,[],[f1080,f787])).
% 2.40/0.67  fof(f787,plain,(
% 2.40/0.67    ( ! [X5] : (~r2_hidden(X5,k1_xboole_0) | k1_funct_1(sK2,X5) = X5 | k1_xboole_0 = sK2) )),
% 2.40/0.67    inference(superposition,[],[f727,f741])).
% 2.40/0.67  fof(f741,plain,(
% 2.40/0.67    k1_xboole_0 = u1_struct_0(sK1) | k1_xboole_0 = sK2),
% 2.40/0.67    inference(subsumption_resolution,[],[f737,f702])).
% 2.40/0.67  fof(f702,plain,(
% 2.40/0.67    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0)))),
% 2.40/0.67    inference(backward_demodulation,[],[f36,f699])).
% 2.40/0.67  fof(f699,plain,(
% 2.40/0.67    k1_xboole_0 = u1_struct_0(sK0)),
% 2.40/0.67    inference(subsumption_resolution,[],[f593,f149])).
% 2.40/0.67  fof(f149,plain,(
% 2.40/0.67    r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2)),
% 2.40/0.67    inference(subsumption_resolution,[],[f148,f36])).
% 2.40/0.67  fof(f148,plain,(
% 2.40/0.67    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2)),
% 2.40/0.67    inference(subsumption_resolution,[],[f147,f34])).
% 2.40/0.67  fof(f34,plain,(
% 2.40/0.67    v1_funct_1(sK2)),
% 2.40/0.67    inference(cnf_transformation,[],[f16])).
% 2.40/0.67  fof(f16,plain,(
% 2.40/0.67    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.40/0.67    inference(flattening,[],[f15])).
% 2.40/0.67  fof(f15,plain,(
% 2.40/0.67    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : ((k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.40/0.67    inference(ennf_transformation,[],[f14])).
% 2.40/0.67  fof(f14,negated_conjecture,(
% 2.40/0.67    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 2.40/0.67    inference(negated_conjecture,[],[f13])).
% 2.40/0.67  fof(f13,conjecture,(
% 2.40/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 2.40/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_tmap_1)).
% 2.40/0.67  fof(f147,plain,(
% 2.40/0.67    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2)),
% 2.40/0.67    inference(trivial_inequality_removal,[],[f144])).
% 2.40/0.67  fof(f144,plain,(
% 2.40/0.67    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k1_funct_1(sK2,sK3(u1_struct_0(sK1),sK2,sK2)) != k1_funct_1(sK2,sK3(u1_struct_0(sK1),sK2,sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2)),
% 2.40/0.67    inference(resolution,[],[f104,f35])).
% 2.40/0.67  fof(f35,plain,(
% 2.40/0.67    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.40/0.67    inference(cnf_transformation,[],[f16])).
% 2.40/0.67  fof(f104,plain,(
% 2.40/0.67    ( ! [X1] : (~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k1_funct_1(sK2,sK3(u1_struct_0(sK1),sK2,X1)) != k1_funct_1(X1,sK3(u1_struct_0(sK1),sK2,X1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X1)) )),
% 2.40/0.67    inference(subsumption_resolution,[],[f103,f36])).
% 2.40/0.67  fof(f103,plain,(
% 2.40/0.67    ( ! [X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k1_funct_1(sK2,sK3(u1_struct_0(sK1),sK2,X1)) != k1_funct_1(X1,sK3(u1_struct_0(sK1),sK2,X1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X1)) )),
% 2.40/0.67    inference(subsumption_resolution,[],[f99,f34])).
% 2.40/0.67  fof(f99,plain,(
% 2.40/0.67    ( ! [X1] : (~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k1_funct_1(sK2,sK3(u1_struct_0(sK1),sK2,X1)) != k1_funct_1(X1,sK3(u1_struct_0(sK1),sK2,X1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X1)) )),
% 2.40/0.67    inference(resolution,[],[f35,f45])).
% 2.40/0.67  fof(f45,plain,(
% 2.40/0.67    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_funct_1(X2,sK3(X0,X2,X3)) != k1_funct_1(X3,sK3(X0,X2,X3)) | r2_funct_2(X0,X1,X2,X3)) )),
% 2.40/0.67    inference(cnf_transformation,[],[f18])).
% 2.40/0.67  fof(f18,plain,(
% 2.40/0.67    ! [X0,X1,X2] : (! [X3] : ((r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.40/0.67    inference(flattening,[],[f17])).
% 2.40/0.68  fof(f17,plain,(
% 2.40/0.68    ! [X0,X1,X2] : (! [X3] : ((r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.40/0.68    inference(ennf_transformation,[],[f8])).
% 2.40/0.68  fof(f8,axiom,(
% 2.40/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)))))),
% 2.40/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_2)).
% 2.40/0.68  fof(f593,plain,(
% 2.40/0.68    ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2) | k1_xboole_0 = u1_struct_0(sK0)),
% 2.40/0.68    inference(superposition,[],[f37,f582])).
% 2.40/0.68  fof(f582,plain,(
% 2.40/0.68    sK2 = k4_tmap_1(sK0,sK1) | k1_xboole_0 = u1_struct_0(sK0)),
% 2.40/0.68    inference(subsumption_resolution,[],[f576,f581])).
% 2.40/0.68  fof(f581,plain,(
% 2.40/0.68    k1_xboole_0 = u1_struct_0(sK0) | sK2 = k4_tmap_1(sK0,sK1) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 2.40/0.68    inference(subsumption_resolution,[],[f580,f408])).
% 2.40/0.68  fof(f408,plain,(
% 2.40/0.68    k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = u1_struct_0(sK0)),
% 2.40/0.68    inference(subsumption_resolution,[],[f407,f34])).
% 2.40/0.68  fof(f407,plain,(
% 2.40/0.68    ~v1_funct_1(sK2) | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = u1_struct_0(sK0)),
% 2.40/0.68    inference(subsumption_resolution,[],[f399,f114])).
% 2.40/0.68  fof(f114,plain,(
% 2.40/0.68    v1_relat_1(sK2)),
% 2.40/0.68    inference(subsumption_resolution,[],[f110,f57])).
% 2.40/0.68  fof(f57,plain,(
% 2.40/0.68    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.40/0.68    inference(cnf_transformation,[],[f5])).
% 2.40/0.68  fof(f5,axiom,(
% 2.40/0.68    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.40/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.40/0.68  fof(f110,plain,(
% 2.40/0.68    ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) | v1_relat_1(sK2)),
% 2.40/0.68    inference(resolution,[],[f36,f62])).
% 2.40/0.68  fof(f62,plain,(
% 2.40/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 2.40/0.68    inference(cnf_transformation,[],[f30])).
% 2.40/0.68  fof(f30,plain,(
% 2.40/0.68    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.40/0.68    inference(ennf_transformation,[],[f4])).
% 2.40/0.68  fof(f4,axiom,(
% 2.40/0.68    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.40/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.40/0.68  fof(f399,plain,(
% 2.40/0.68    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = u1_struct_0(sK0)),
% 2.40/0.68    inference(resolution,[],[f282,f70])).
% 2.40/0.68  fof(f70,plain,(
% 2.40/0.68    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.40/0.68    inference(equality_resolution,[],[f59])).
% 2.40/0.68  fof(f59,plain,(
% 2.40/0.68    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.40/0.68    inference(cnf_transformation,[],[f1])).
% 2.40/0.68  fof(f1,axiom,(
% 2.40/0.68    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.40/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.40/0.68  fof(f282,plain,(
% 2.40/0.68    ( ! [X3] : (~r1_tarski(k1_relat_1(sK2),k1_relat_1(X3)) | ~v1_relat_1(X3) | ~v1_funct_1(X3) | k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),X3)) != k1_funct_1(X3,sK4(k4_tmap_1(sK0,sK1),X3)) | r1_tarski(k4_tmap_1(sK0,sK1),X3) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 2.40/0.68    inference(subsumption_resolution,[],[f281,f128])).
% 2.40/0.68  fof(f128,plain,(
% 2.40/0.68    v1_relat_1(k4_tmap_1(sK0,sK1))),
% 2.40/0.68    inference(subsumption_resolution,[],[f125,f57])).
% 2.40/0.68  fof(f125,plain,(
% 2.40/0.68    ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) | v1_relat_1(k4_tmap_1(sK0,sK1))),
% 2.40/0.68    inference(resolution,[],[f96,f62])).
% 2.40/0.68  fof(f96,plain,(
% 2.40/0.68    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.40/0.68    inference(subsumption_resolution,[],[f95,f40])).
% 2.40/0.68  fof(f40,plain,(
% 2.40/0.68    ~v2_struct_0(sK0)),
% 2.40/0.68    inference(cnf_transformation,[],[f16])).
% 2.40/0.68  fof(f95,plain,(
% 2.40/0.68    v2_struct_0(sK0) | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.40/0.68    inference(subsumption_resolution,[],[f94,f42])).
% 2.40/0.68  fof(f42,plain,(
% 2.40/0.68    l1_pre_topc(sK0)),
% 2.40/0.68    inference(cnf_transformation,[],[f16])).
% 2.40/0.68  fof(f94,plain,(
% 2.40/0.68    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.40/0.68    inference(subsumption_resolution,[],[f82,f41])).
% 2.40/0.68  fof(f41,plain,(
% 2.40/0.68    v2_pre_topc(sK0)),
% 2.40/0.68    inference(cnf_transformation,[],[f16])).
% 2.40/0.68  fof(f82,plain,(
% 2.40/0.68    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.40/0.68    inference(resolution,[],[f39,f48])).
% 2.40/0.68  fof(f48,plain,(
% 2.40/0.68    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))) )),
% 2.40/0.68    inference(cnf_transformation,[],[f20])).
% 2.40/0.68  fof(f20,plain,(
% 2.40/0.68    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.40/0.68    inference(flattening,[],[f19])).
% 2.40/0.68  fof(f19,plain,(
% 2.40/0.68    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.40/0.68    inference(ennf_transformation,[],[f10])).
% 2.40/0.68  fof(f10,axiom,(
% 2.40/0.68    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))))),
% 2.40/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_tmap_1)).
% 2.40/0.68  fof(f39,plain,(
% 2.40/0.68    m1_pre_topc(sK1,sK0)),
% 2.40/0.68    inference(cnf_transformation,[],[f16])).
% 2.40/0.68  fof(f281,plain,(
% 2.40/0.68    ( ! [X3] : (~r1_tarski(k1_relat_1(sK2),k1_relat_1(X3)) | ~v1_relat_1(X3) | ~v1_funct_1(X3) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),X3)) != k1_funct_1(X3,sK4(k4_tmap_1(sK0,sK1),X3)) | r1_tarski(k4_tmap_1(sK0,sK1),X3) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 2.40/0.68    inference(subsumption_resolution,[],[f271,f90])).
% 2.40/0.68  fof(f90,plain,(
% 2.40/0.68    v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.40/0.68    inference(subsumption_resolution,[],[f89,f40])).
% 2.40/0.68  fof(f89,plain,(
% 2.40/0.68    v2_struct_0(sK0) | v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.40/0.68    inference(subsumption_resolution,[],[f88,f42])).
% 2.40/0.68  fof(f88,plain,(
% 2.40/0.68    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.40/0.68    inference(subsumption_resolution,[],[f80,f41])).
% 2.40/0.68  fof(f80,plain,(
% 2.40/0.68    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_1(k4_tmap_1(sK0,sK1))),
% 2.40/0.68    inference(resolution,[],[f39,f46])).
% 2.40/0.68  fof(f46,plain,(
% 2.40/0.68    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_funct_1(k4_tmap_1(X0,X1))) )),
% 2.40/0.68    inference(cnf_transformation,[],[f20])).
% 2.40/0.68  fof(f271,plain,(
% 2.40/0.68    ( ! [X3] : (~r1_tarski(k1_relat_1(sK2),k1_relat_1(X3)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(X3) | ~v1_funct_1(X3) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),X3)) != k1_funct_1(X3,sK4(k4_tmap_1(sK0,sK1),X3)) | r1_tarski(k4_tmap_1(sK0,sK1),X3) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 2.40/0.68    inference(superposition,[],[f51,f264])).
% 2.40/0.68  fof(f264,plain,(
% 2.40/0.68    k1_relat_1(sK2) = k1_relat_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 2.40/0.68    inference(duplicate_literal_removal,[],[f261])).
% 2.40/0.68  fof(f261,plain,(
% 2.40/0.68    k1_relat_1(sK2) = k1_relat_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | k1_xboole_0 = u1_struct_0(sK0)),
% 2.40/0.68    inference(superposition,[],[f221,f222])).
% 2.40/0.68  fof(f222,plain,(
% 2.40/0.68    k1_relat_1(k4_tmap_1(sK0,sK1)) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 2.40/0.68    inference(superposition,[],[f124,f113])).
% 2.40/0.68  fof(f113,plain,(
% 2.40/0.68    u1_struct_0(sK1) = k1_relat_1(sK2) | k1_xboole_0 = u1_struct_0(sK0)),
% 2.40/0.68    inference(backward_demodulation,[],[f100,f109])).
% 2.40/0.68  fof(f109,plain,(
% 2.40/0.68    k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) = k1_relat_1(sK2)),
% 2.40/0.68    inference(resolution,[],[f36,f58])).
% 2.40/0.68  fof(f58,plain,(
% 2.40/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 2.40/0.68    inference(cnf_transformation,[],[f29])).
% 2.40/0.68  fof(f29,plain,(
% 2.40/0.68    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.40/0.68    inference(ennf_transformation,[],[f6])).
% 2.40/0.68  fof(f6,axiom,(
% 2.40/0.68    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.40/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.40/0.68  fof(f100,plain,(
% 2.40/0.68    k1_xboole_0 = u1_struct_0(sK0) | u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2)),
% 2.40/0.68    inference(subsumption_resolution,[],[f97,f36])).
% 2.40/0.68  fof(f97,plain,(
% 2.40/0.68    k1_xboole_0 = u1_struct_0(sK0) | u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.40/0.68    inference(resolution,[],[f35,f68])).
% 2.40/0.68  fof(f68,plain,(
% 2.40/0.68    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.40/0.68    inference(cnf_transformation,[],[f32])).
% 2.40/0.68  fof(f32,plain,(
% 2.40/0.68    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.40/0.68    inference(flattening,[],[f31])).
% 2.40/0.68  fof(f31,plain,(
% 2.40/0.68    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.40/0.68    inference(ennf_transformation,[],[f7])).
% 2.40/0.68  fof(f7,axiom,(
% 2.40/0.68    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.40/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 2.40/0.68  fof(f124,plain,(
% 2.40/0.68    k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1)) = k1_relat_1(k4_tmap_1(sK0,sK1))),
% 2.40/0.68    inference(resolution,[],[f96,f58])).
% 2.40/0.68  fof(f221,plain,(
% 2.40/0.68    k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 2.40/0.68    inference(subsumption_resolution,[],[f220,f140])).
% 2.40/0.68  fof(f140,plain,(
% 2.40/0.68    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK0)))) | k1_xboole_0 = u1_struct_0(sK0)),
% 2.40/0.68    inference(superposition,[],[f96,f113])).
% 2.40/0.68  fof(f220,plain,(
% 2.40/0.68    k1_xboole_0 = u1_struct_0(sK0) | k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK1)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK0))))),
% 2.40/0.68    inference(duplicate_literal_removal,[],[f217])).
% 2.40/0.68  fof(f217,plain,(
% 2.40/0.68    k1_xboole_0 = u1_struct_0(sK0) | k1_xboole_0 = u1_struct_0(sK0) | k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK0),k4_tmap_1(sK0,sK1)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK0))))),
% 2.40/0.68    inference(resolution,[],[f139,f68])).
% 2.40/0.68  fof(f139,plain,(
% 2.40/0.68    v1_funct_2(k4_tmap_1(sK0,sK1),k1_relat_1(sK2),u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK0)),
% 2.40/0.68    inference(superposition,[],[f93,f113])).
% 2.40/0.68  fof(f93,plain,(
% 2.40/0.68    v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.40/0.68    inference(subsumption_resolution,[],[f92,f40])).
% 2.40/0.68  fof(f92,plain,(
% 2.40/0.68    v2_struct_0(sK0) | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.40/0.68    inference(subsumption_resolution,[],[f91,f42])).
% 2.40/0.68  fof(f91,plain,(
% 2.40/0.68    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.40/0.68    inference(subsumption_resolution,[],[f81,f41])).
% 2.40/0.68  fof(f81,plain,(
% 2.40/0.68    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 2.40/0.68    inference(resolution,[],[f39,f47])).
% 2.40/0.68  fof(f47,plain,(
% 2.40/0.68    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))) )),
% 2.40/0.68    inference(cnf_transformation,[],[f20])).
% 2.40/0.68  fof(f51,plain,(
% 2.40/0.68    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | r1_tarski(X0,X1)) )),
% 2.40/0.68    inference(cnf_transformation,[],[f24])).
% 2.40/0.68  fof(f24,plain,(
% 2.40/0.68    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) <=> (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.40/0.68    inference(flattening,[],[f23])).
% 2.40/0.68  fof(f23,plain,(
% 2.40/0.68    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) <=> (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.40/0.68    inference(ennf_transformation,[],[f9])).
% 2.40/0.68  fof(f9,axiom,(
% 2.40/0.68    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,X1) <=> (! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 2.40/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_grfunc_1)).
% 2.40/0.68  fof(f580,plain,(
% 2.40/0.68    k1_xboole_0 = u1_struct_0(sK0) | sK2 = k4_tmap_1(sK0,sK1) | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 2.40/0.68    inference(subsumption_resolution,[],[f579,f90])).
% 2.40/0.68  fof(f579,plain,(
% 2.40/0.68    k1_xboole_0 = u1_struct_0(sK0) | sK2 = k4_tmap_1(sK0,sK1) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 2.40/0.68    inference(subsumption_resolution,[],[f578,f128])).
% 2.40/0.68  fof(f578,plain,(
% 2.40/0.68    k1_xboole_0 = u1_struct_0(sK0) | sK2 = k4_tmap_1(sK0,sK1) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 2.40/0.68    inference(duplicate_literal_removal,[],[f572])).
% 2.40/0.68  fof(f572,plain,(
% 2.40/0.68    k1_xboole_0 = u1_struct_0(sK0) | sK2 = k4_tmap_1(sK0,sK1) | k1_xboole_0 = u1_struct_0(sK0) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 2.40/0.68    inference(resolution,[],[f571,f380])).
% 2.40/0.68  fof(f380,plain,(
% 2.40/0.68    ( ! [X0] : (~r1_tarski(sK2,X0) | k1_xboole_0 = u1_struct_0(sK0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(X0,sK4(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)) )),
% 2.40/0.68    inference(subsumption_resolution,[],[f379,f114])).
% 2.40/0.68  fof(f379,plain,(
% 2.40/0.68    ( ! [X0] : (r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = u1_struct_0(sK0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK2) | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(X0,sK4(k4_tmap_1(sK0,sK1),sK2)) | ~r1_tarski(sK2,X0)) )),
% 2.40/0.68    inference(subsumption_resolution,[],[f376,f34])).
% 2.40/0.68  fof(f376,plain,(
% 2.40/0.68    ( ! [X0] : (r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = u1_struct_0(sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK2) | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(X0,sK4(k4_tmap_1(sK0,sK1),sK2)) | ~r1_tarski(sK2,X0)) )),
% 2.40/0.68    inference(resolution,[],[f374,f52])).
% 2.40/0.68  fof(f52,plain,(
% 2.40/0.68    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.40/0.68    inference(cnf_transformation,[],[f24])).
% 2.40/0.68  fof(f374,plain,(
% 2.40/0.68    r2_hidden(sK4(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = u1_struct_0(sK0)),
% 2.40/0.68    inference(subsumption_resolution,[],[f373,f34])).
% 2.40/0.68  fof(f373,plain,(
% 2.40/0.68    ~v1_funct_1(sK2) | r2_hidden(sK4(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = u1_struct_0(sK0)),
% 2.40/0.68    inference(subsumption_resolution,[],[f367,f114])).
% 2.40/0.68  fof(f367,plain,(
% 2.40/0.68    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | r2_hidden(sK4(k4_tmap_1(sK0,sK1),sK2),k1_relat_1(sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = u1_struct_0(sK0)),
% 2.40/0.68    inference(resolution,[],[f278,f70])).
% 2.40/0.68  fof(f278,plain,(
% 2.40/0.68    ( ! [X1] : (~r1_tarski(k1_relat_1(sK2),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | r2_hidden(sK4(k4_tmap_1(sK0,sK1),X1),k1_relat_1(sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),X1) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 2.40/0.68    inference(subsumption_resolution,[],[f277,f128])).
% 2.40/0.68  fof(f277,plain,(
% 2.40/0.68    ( ! [X1] : (~r1_tarski(k1_relat_1(sK2),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK4(k4_tmap_1(sK0,sK1),X1),k1_relat_1(sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),X1) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 2.40/0.68    inference(subsumption_resolution,[],[f269,f90])).
% 2.40/0.68  fof(f269,plain,(
% 2.40/0.68    ( ! [X1] : (~r1_tarski(k1_relat_1(sK2),k1_relat_1(X1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK4(k4_tmap_1(sK0,sK1),X1),k1_relat_1(sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),X1) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 2.40/0.68    inference(superposition,[],[f50,f264])).
% 2.40/0.68  fof(f50,plain,(
% 2.40/0.68    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | r1_tarski(X0,X1)) )),
% 2.40/0.68    inference(cnf_transformation,[],[f24])).
% 2.40/0.68  fof(f571,plain,(
% 2.40/0.68    r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK2 = k4_tmap_1(sK0,sK1)),
% 2.40/0.68    inference(subsumption_resolution,[],[f570,f431])).
% 2.40/0.68  fof(f431,plain,(
% 2.40/0.68    r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1)))),
% 2.40/0.68    inference(subsumption_resolution,[],[f430,f334])).
% 2.40/0.68  fof(f334,plain,(
% 2.40/0.68    r2_hidden(sK4(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 2.40/0.68    inference(subsumption_resolution,[],[f333,f114])).
% 2.40/0.68  fof(f333,plain,(
% 2.40/0.68    ~v1_relat_1(sK2) | r2_hidden(sK4(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 2.40/0.68    inference(subsumption_resolution,[],[f327,f34])).
% 2.40/0.68  fof(f327,plain,(
% 2.40/0.68    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | r2_hidden(sK4(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 2.40/0.68    inference(resolution,[],[f276,f70])).
% 2.40/0.68  fof(f276,plain,(
% 2.40/0.68    ( ! [X0] : (~r1_tarski(k1_relat_1(X0),k1_relat_1(sK2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK4(X0,k4_tmap_1(sK0,sK1)),k1_relat_1(X0)) | r1_tarski(X0,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 2.40/0.68    inference(subsumption_resolution,[],[f275,f90])).
% 2.40/0.68  fof(f275,plain,(
% 2.40/0.68    ( ! [X0] : (~r1_tarski(k1_relat_1(X0),k1_relat_1(sK2)) | ~v1_funct_1(X0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(X0) | r2_hidden(sK4(X0,k4_tmap_1(sK0,sK1)),k1_relat_1(X0)) | r1_tarski(X0,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 2.40/0.68    inference(subsumption_resolution,[],[f268,f128])).
% 2.40/0.68  fof(f268,plain,(
% 2.40/0.68    ( ! [X0] : (~r1_tarski(k1_relat_1(X0),k1_relat_1(sK2)) | ~v1_funct_1(X0) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(X0) | r2_hidden(sK4(X0,k4_tmap_1(sK0,sK1)),k1_relat_1(X0)) | r1_tarski(X0,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 2.40/0.68    inference(superposition,[],[f50,f264])).
% 2.40/0.68  fof(f430,plain,(
% 2.40/0.68    ~r2_hidden(sK4(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1)))),
% 2.40/0.68    inference(duplicate_literal_removal,[],[f429])).
% 2.40/0.68  fof(f429,plain,(
% 2.40/0.68    ~r2_hidden(sK4(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = u1_struct_0(sK0)),
% 2.40/0.68    inference(superposition,[],[f365,f113])).
% 2.40/0.68  fof(f365,plain,(
% 2.40/0.68    ~r2_hidden(sK4(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1)))),
% 2.40/0.68    inference(resolution,[],[f346,f33])).
% 2.40/0.68  fof(f33,plain,(
% 2.40/0.68    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X3,u1_struct_0(sK1)) | k1_funct_1(sK2,X3) = X3) )),
% 2.40/0.68    inference(cnf_transformation,[],[f16])).
% 2.40/0.68  fof(f346,plain,(
% 2.40/0.68    m1_subset_1(sK4(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK0) | r1_tarski(sK2,k4_tmap_1(sK0,sK1))),
% 2.40/0.68    inference(duplicate_literal_removal,[],[f343])).
% 2.40/0.68  fof(f343,plain,(
% 2.40/0.68    r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | m1_subset_1(sK4(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK0)),
% 2.40/0.68    inference(resolution,[],[f334,f142])).
% 2.40/0.68  fof(f142,plain,(
% 2.40/0.68    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK2)) | m1_subset_1(X1,u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 2.40/0.68    inference(superposition,[],[f106,f113])).
% 2.40/0.68  fof(f106,plain,(
% 2.40/0.68    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK1)) | m1_subset_1(X0,u1_struct_0(sK0))) )),
% 2.40/0.68    inference(resolution,[],[f83,f54])).
% 2.40/0.68  fof(f54,plain,(
% 2.40/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 2.40/0.68    inference(cnf_transformation,[],[f26])).
% 2.40/0.68  fof(f26,plain,(
% 2.40/0.68    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.40/0.68    inference(flattening,[],[f25])).
% 2.40/0.68  fof(f25,plain,(
% 2.40/0.68    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.40/0.68    inference(ennf_transformation,[],[f3])).
% 2.40/0.68  fof(f3,axiom,(
% 2.40/0.68    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.40/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 2.40/0.68  fof(f83,plain,(
% 2.40/0.68    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.40/0.68    inference(subsumption_resolution,[],[f78,f42])).
% 2.40/0.68  fof(f78,plain,(
% 2.40/0.68    ~l1_pre_topc(sK0) | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.40/0.68    inference(resolution,[],[f39,f56])).
% 2.40/0.68  fof(f56,plain,(
% 2.40/0.68    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 2.40/0.68    inference(cnf_transformation,[],[f28])).
% 2.40/0.68  fof(f28,plain,(
% 2.40/0.68    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.40/0.68    inference(ennf_transformation,[],[f11])).
% 2.40/0.68  fof(f11,axiom,(
% 2.40/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.40/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 2.40/0.68  fof(f570,plain,(
% 2.40/0.68    sK4(sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK2 = k4_tmap_1(sK0,sK1)),
% 2.40/0.68    inference(duplicate_literal_removal,[],[f569])).
% 2.40/0.68  fof(f569,plain,(
% 2.40/0.68    sK4(sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | k1_xboole_0 = u1_struct_0(sK0) | sK2 = k4_tmap_1(sK0,sK1)),
% 2.40/0.68    inference(superposition,[],[f395,f488])).
% 2.40/0.68  fof(f488,plain,(
% 2.40/0.68    sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = u1_struct_0(sK0) | sK2 = k4_tmap_1(sK0,sK1)),
% 2.40/0.68    inference(subsumption_resolution,[],[f481,f487])).
% 2.40/0.68  fof(f487,plain,(
% 2.40/0.68    r1_tarski(k4_tmap_1(sK0,sK1),sK2) | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = u1_struct_0(sK0)),
% 2.40/0.68    inference(subsumption_resolution,[],[f486,f408])).
% 2.40/0.68  fof(f486,plain,(
% 2.40/0.68    k1_xboole_0 = u1_struct_0(sK0) | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1))) | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 2.40/0.68    inference(subsumption_resolution,[],[f485,f90])).
% 2.40/0.68  fof(f485,plain,(
% 2.40/0.68    k1_xboole_0 = u1_struct_0(sK0) | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1))) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 2.40/0.68    inference(subsumption_resolution,[],[f484,f128])).
% 2.40/0.68  fof(f484,plain,(
% 2.40/0.68    k1_xboole_0 = u1_struct_0(sK0) | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1))) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 2.40/0.68    inference(duplicate_literal_removal,[],[f479])).
% 2.40/0.68  fof(f479,plain,(
% 2.40/0.68    k1_xboole_0 = u1_struct_0(sK0) | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = u1_struct_0(sK0) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 2.40/0.68    inference(resolution,[],[f451,f380])).
% 2.40/0.68  fof(f451,plain,(
% 2.40/0.68    r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1)))),
% 2.40/0.68    inference(subsumption_resolution,[],[f450,f334])).
% 2.40/0.68  fof(f450,plain,(
% 2.40/0.68    ~r2_hidden(sK4(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1)))),
% 2.40/0.68    inference(duplicate_literal_removal,[],[f449])).
% 2.40/0.68  fof(f449,plain,(
% 2.40/0.68    ~r2_hidden(sK4(sK2,k4_tmap_1(sK0,sK1)),k1_relat_1(sK2)) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = u1_struct_0(sK0)),
% 2.40/0.68    inference(superposition,[],[f364,f113])).
% 2.40/0.68  fof(f364,plain,(
% 2.40/0.68    ~r2_hidden(sK4(sK2,k4_tmap_1(sK0,sK1)),u1_struct_0(sK1)) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0) | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1)))),
% 2.40/0.68    inference(resolution,[],[f346,f87])).
% 2.40/0.68  fof(f87,plain,(
% 2.40/0.68    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 2.40/0.68    inference(subsumption_resolution,[],[f86,f40])).
% 2.40/0.68  fof(f86,plain,(
% 2.40/0.68    ( ! [X0] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 2.40/0.68    inference(subsumption_resolution,[],[f85,f38])).
% 2.40/0.68  fof(f38,plain,(
% 2.40/0.68    ~v2_struct_0(sK1)),
% 2.40/0.68    inference(cnf_transformation,[],[f16])).
% 2.40/0.68  fof(f85,plain,(
% 2.40/0.68    ( ! [X0] : (v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 2.40/0.68    inference(subsumption_resolution,[],[f84,f42])).
% 2.40/0.68  fof(f84,plain,(
% 2.40/0.68    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 2.40/0.68    inference(subsumption_resolution,[],[f79,f41])).
% 2.40/0.68  fof(f79,plain,(
% 2.40/0.68    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 2.40/0.68    inference(resolution,[],[f39,f49])).
% 2.40/0.68  fof(f49,plain,(
% 2.40/0.68    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,u1_struct_0(X1)) | k1_funct_1(k4_tmap_1(X0,X1),X2) = X2) )),
% 2.40/0.68    inference(cnf_transformation,[],[f22])).
% 2.40/0.68  fof(f22,plain,(
% 2.40/0.68    ! [X0] : (! [X1] : (! [X2] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.40/0.68    inference(flattening,[],[f21])).
% 2.40/0.68  fof(f21,plain,(
% 2.40/0.68    ! [X0] : (! [X1] : (! [X2] : ((k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.40/0.68    inference(ennf_transformation,[],[f12])).
% 2.40/0.68  fof(f12,axiom,(
% 2.40/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,u1_struct_0(X1)) => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2))))),
% 2.40/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_tmap_1)).
% 2.40/0.68  fof(f481,plain,(
% 2.40/0.68    k1_xboole_0 = u1_struct_0(sK0) | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1))) | ~r1_tarski(k4_tmap_1(sK0,sK1),sK2) | sK2 = k4_tmap_1(sK0,sK1)),
% 2.40/0.68    inference(resolution,[],[f451,f61])).
% 2.40/0.68  fof(f61,plain,(
% 2.40/0.68    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 2.40/0.68    inference(cnf_transformation,[],[f1])).
% 2.40/0.68  fof(f395,plain,(
% 2.40/0.68    k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 2.40/0.68    inference(subsumption_resolution,[],[f394,f114])).
% 2.40/0.68  fof(f394,plain,(
% 2.40/0.68    ~v1_relat_1(sK2) | k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 2.40/0.68    inference(subsumption_resolution,[],[f386,f34])).
% 2.40/0.68  fof(f386,plain,(
% 2.40/0.68    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)),
% 2.40/0.68    inference(resolution,[],[f280,f70])).
% 2.40/0.68  fof(f280,plain,(
% 2.40/0.68    ( ! [X2] : (~r1_tarski(k1_relat_1(X2),k1_relat_1(sK2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | k1_funct_1(X2,sK4(X2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(X2,k4_tmap_1(sK0,sK1))) | r1_tarski(X2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 2.40/0.68    inference(subsumption_resolution,[],[f279,f90])).
% 2.40/0.68  fof(f279,plain,(
% 2.40/0.68    ( ! [X2] : (~r1_tarski(k1_relat_1(X2),k1_relat_1(sK2)) | ~v1_funct_1(X2) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(X2) | k1_funct_1(X2,sK4(X2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(X2,k4_tmap_1(sK0,sK1))) | r1_tarski(X2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 2.40/0.68    inference(subsumption_resolution,[],[f270,f128])).
% 2.40/0.68  fof(f270,plain,(
% 2.40/0.68    ( ! [X2] : (~r1_tarski(k1_relat_1(X2),k1_relat_1(sK2)) | ~v1_funct_1(X2) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(X2) | k1_funct_1(X2,sK4(X2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(X2,k4_tmap_1(sK0,sK1))) | r1_tarski(X2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = u1_struct_0(sK0)) )),
% 2.40/0.68    inference(superposition,[],[f51,f264])).
% 2.40/0.68  fof(f576,plain,(
% 2.40/0.68    k1_xboole_0 = u1_struct_0(sK0) | sK2 = k4_tmap_1(sK0,sK1) | ~r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 2.40/0.68    inference(duplicate_literal_removal,[],[f574])).
% 2.40/0.68  fof(f574,plain,(
% 2.40/0.68    k1_xboole_0 = u1_struct_0(sK0) | sK2 = k4_tmap_1(sK0,sK1) | ~r1_tarski(k4_tmap_1(sK0,sK1),sK2) | sK2 = k4_tmap_1(sK0,sK1)),
% 2.40/0.68    inference(resolution,[],[f571,f61])).
% 2.40/0.68  fof(f37,plain,(
% 2.40/0.68    ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)),
% 2.40/0.68    inference(cnf_transformation,[],[f16])).
% 2.40/0.68  fof(f36,plain,(
% 2.40/0.68    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 2.40/0.68    inference(cnf_transformation,[],[f16])).
% 2.40/0.68  fof(f737,plain,(
% 2.40/0.68    k1_xboole_0 = u1_struct_0(sK1) | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0)))),
% 2.40/0.68    inference(resolution,[],[f701,f73])).
% 2.40/0.68  fof(f73,plain,(
% 2.40/0.68    ( ! [X2,X0] : (~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.40/0.68    inference(equality_resolution,[],[f64])).
% 2.40/0.68  fof(f64,plain,(
% 2.40/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 2.40/0.68    inference(cnf_transformation,[],[f32])).
% 2.40/0.68  fof(f701,plain,(
% 2.40/0.68    v1_funct_2(sK2,u1_struct_0(sK1),k1_xboole_0)),
% 2.40/0.68    inference(backward_demodulation,[],[f35,f699])).
% 2.40/0.68  fof(f727,plain,(
% 2.40/0.68    ( ! [X3] : (~r2_hidden(X3,u1_struct_0(sK1)) | k1_funct_1(sK2,X3) = X3) )),
% 2.40/0.68    inference(global_subsumption,[],[f33,f106])).
% 2.40/0.68  fof(f1080,plain,(
% 2.40/0.68    r2_hidden(sK4(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2),
% 2.40/0.68    inference(subsumption_resolution,[],[f1079,f128])).
% 2.40/0.68  fof(f1079,plain,(
% 2.40/0.68    ~v1_relat_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK4(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2),
% 2.40/0.68    inference(subsumption_resolution,[],[f1078,f90])).
% 2.40/0.68  fof(f1078,plain,(
% 2.40/0.68    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK4(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2),
% 2.40/0.68    inference(subsumption_resolution,[],[f1076,f70])).
% 2.40/0.68  fof(f1076,plain,(
% 2.40/0.68    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK4(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2),
% 2.40/0.68    inference(duplicate_literal_removal,[],[f1075])).
% 2.40/0.68  fof(f1075,plain,(
% 2.40/0.68    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK4(k4_tmap_1(sK0,sK1),sK2),k1_xboole_0) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 2.40/0.68    inference(superposition,[],[f890,f932])).
% 2.40/0.68  fof(f932,plain,(
% 2.40/0.68    k1_xboole_0 = k1_relat_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2),
% 2.40/0.68    inference(duplicate_literal_removal,[],[f929])).
% 2.40/0.68  fof(f929,plain,(
% 2.40/0.68    k1_xboole_0 = k1_relat_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 2.40/0.68    inference(superposition,[],[f849,f819])).
% 2.40/0.68  fof(f819,plain,(
% 2.40/0.68    k1_relat_1(k4_tmap_1(sK0,sK1)) = k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2),
% 2.40/0.68    inference(superposition,[],[f718,f741])).
% 2.40/0.68  fof(f718,plain,(
% 2.40/0.68    k1_relat_1(k4_tmap_1(sK0,sK1)) = k1_relset_1(u1_struct_0(sK1),k1_xboole_0,k4_tmap_1(sK0,sK1))),
% 2.40/0.68    inference(backward_demodulation,[],[f124,f699])).
% 2.40/0.68  fof(f849,plain,(
% 2.40/0.68    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2),
% 2.40/0.68    inference(subsumption_resolution,[],[f843,f782])).
% 2.40/0.68  fof(f782,plain,(
% 2.40/0.68    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | k1_xboole_0 = sK2),
% 2.40/0.68    inference(superposition,[],[f707,f741])).
% 2.40/0.68  fof(f707,plain,(
% 2.40/0.68    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0)))),
% 2.40/0.68    inference(backward_demodulation,[],[f96,f699])).
% 2.40/0.68  fof(f843,plain,(
% 2.40/0.68    k1_xboole_0 = sK2 | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 2.40/0.68    inference(resolution,[],[f781,f71])).
% 2.40/0.68  fof(f71,plain,(
% 2.40/0.68    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.40/0.68    inference(equality_resolution,[],[f66])).
% 2.40/0.68  fof(f66,plain,(
% 2.40/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 2.40/0.68    inference(cnf_transformation,[],[f32])).
% 2.40/0.68  fof(f781,plain,(
% 2.40/0.68    v1_funct_2(k4_tmap_1(sK0,sK1),k1_xboole_0,k1_xboole_0) | k1_xboole_0 = sK2),
% 2.40/0.68    inference(superposition,[],[f706,f741])).
% 2.40/0.68  fof(f706,plain,(
% 2.40/0.68    v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),k1_xboole_0)),
% 2.40/0.68    inference(backward_demodulation,[],[f93,f699])).
% 2.40/0.68  fof(f890,plain,(
% 2.40/0.68    ( ! [X1] : (~r1_tarski(k1_relat_1(X1),k1_xboole_0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | r2_hidden(sK4(X1,sK2),k1_relat_1(X1)) | r1_tarski(X1,sK2) | k1_xboole_0 = sK2) )),
% 2.40/0.68    inference(subsumption_resolution,[],[f889,f34])).
% 2.40/0.68  fof(f889,plain,(
% 2.40/0.68    ( ! [X1] : (~r1_tarski(k1_relat_1(X1),k1_xboole_0) | ~v1_funct_1(X1) | ~v1_funct_1(sK2) | ~v1_relat_1(X1) | r2_hidden(sK4(X1,sK2),k1_relat_1(X1)) | r1_tarski(X1,sK2) | k1_xboole_0 = sK2) )),
% 2.40/0.68    inference(subsumption_resolution,[],[f883,f114])).
% 2.40/0.68  fof(f883,plain,(
% 2.40/0.68    ( ! [X1] : (~r1_tarski(k1_relat_1(X1),k1_xboole_0) | ~v1_funct_1(X1) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(X1) | r2_hidden(sK4(X1,sK2),k1_relat_1(X1)) | r1_tarski(X1,sK2) | k1_xboole_0 = sK2) )),
% 2.40/0.68    inference(superposition,[],[f50,f875])).
% 2.40/0.68  fof(f875,plain,(
% 2.40/0.68    k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 = sK2),
% 2.40/0.68    inference(duplicate_literal_removal,[],[f872])).
% 2.40/0.68  fof(f872,plain,(
% 2.40/0.68    k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 2.40/0.68    inference(superposition,[],[f830,f804])).
% 2.40/0.68  fof(f804,plain,(
% 2.40/0.68    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | k1_xboole_0 = sK2),
% 2.40/0.68    inference(superposition,[],[f713,f741])).
% 2.40/0.68  fof(f713,plain,(
% 2.40/0.68    k1_relat_1(sK2) = k1_relset_1(u1_struct_0(sK1),k1_xboole_0,sK2)),
% 2.40/0.68    inference(backward_demodulation,[],[f109,f699])).
% 2.40/0.68  fof(f830,plain,(
% 2.40/0.68    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | k1_xboole_0 = sK2),
% 2.40/0.68    inference(subsumption_resolution,[],[f824,f778])).
% 2.40/0.68  fof(f778,plain,(
% 2.40/0.68    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | k1_xboole_0 = sK2),
% 2.40/0.68    inference(superposition,[],[f702,f741])).
% 2.40/0.68  fof(f824,plain,(
% 2.40/0.68    k1_xboole_0 = sK2 | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 2.40/0.68    inference(resolution,[],[f777,f71])).
% 2.40/0.68  fof(f777,plain,(
% 2.40/0.68    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = sK2),
% 2.40/0.68    inference(superposition,[],[f701,f741])).
% 2.40/0.68  fof(f1592,plain,(
% 2.40/0.68    sK4(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2 | sK2 = k4_tmap_1(sK0,sK1)),
% 2.40/0.68    inference(duplicate_literal_removal,[],[f1591])).
% 2.40/0.68  fof(f1591,plain,(
% 2.40/0.68    sK4(k4_tmap_1(sK0,sK1),sK2) != k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2 | sK2 = k4_tmap_1(sK0,sK1)),
% 2.40/0.68    inference(superposition,[],[f1137,f1406])).
% 2.40/0.68  fof(f1406,plain,(
% 2.40/0.68    sK4(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | sK2 = k4_tmap_1(sK0,sK1)),
% 2.40/0.68    inference(subsumption_resolution,[],[f1401,f1087])).
% 2.40/0.68  fof(f1087,plain,(
% 2.40/0.68    r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2 | sK4(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2))),
% 2.40/0.68    inference(duplicate_literal_removal,[],[f1082])).
% 2.40/0.68  fof(f1082,plain,(
% 2.40/0.68    r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2 | sK4(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2),
% 2.40/0.68    inference(resolution,[],[f1080,f788])).
% 2.40/0.68  fof(f788,plain,(
% 2.40/0.68    ( ! [X6] : (~r2_hidden(X6,k1_xboole_0) | k1_funct_1(k4_tmap_1(sK0,sK1),X6) = X6 | k1_xboole_0 = sK2) )),
% 2.40/0.68    inference(superposition,[],[f728,f741])).
% 2.40/0.68  fof(f728,plain,(
% 2.40/0.68    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 2.40/0.68    inference(global_subsumption,[],[f87,f106])).
% 2.40/0.68  fof(f1401,plain,(
% 2.40/0.68    k1_xboole_0 = sK2 | sK4(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2)) | ~r1_tarski(k4_tmap_1(sK0,sK1),sK2) | sK2 = k4_tmap_1(sK0,sK1)),
% 2.40/0.68    inference(resolution,[],[f1311,f61])).
% 2.40/0.68  fof(f1311,plain,(
% 2.40/0.68    r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2 | sK4(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2))),
% 2.40/0.68    inference(subsumption_resolution,[],[f1310,f1122])).
% 2.40/0.68  fof(f1122,plain,(
% 2.40/0.68    k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2),
% 2.40/0.68    inference(subsumption_resolution,[],[f1121,f90])).
% 2.40/0.68  fof(f1121,plain,(
% 2.40/0.68    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2),
% 2.40/0.68    inference(subsumption_resolution,[],[f1120,f128])).
% 2.40/0.68  fof(f1120,plain,(
% 2.40/0.68    ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2),
% 2.40/0.68    inference(subsumption_resolution,[],[f1117,f70])).
% 2.40/0.68  fof(f1117,plain,(
% 2.40/0.68    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2),
% 2.40/0.68    inference(duplicate_literal_removal,[],[f1116])).
% 2.40/0.68  fof(f1116,plain,(
% 2.40/0.68    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 2.40/0.68    inference(superposition,[],[f892,f932])).
% 2.40/0.68  fof(f892,plain,(
% 2.40/0.68    ( ! [X2] : (~r1_tarski(k1_xboole_0,k1_relat_1(X2)) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_funct_1(sK2,sK4(sK2,X2)) != k1_funct_1(X2,sK4(sK2,X2)) | r1_tarski(sK2,X2) | k1_xboole_0 = sK2) )),
% 2.40/0.68    inference(subsumption_resolution,[],[f891,f114])).
% 2.40/0.68  fof(f891,plain,(
% 2.40/0.68    ( ! [X2] : (~r1_tarski(k1_xboole_0,k1_relat_1(X2)) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(sK2) | k1_funct_1(sK2,sK4(sK2,X2)) != k1_funct_1(X2,sK4(sK2,X2)) | r1_tarski(sK2,X2) | k1_xboole_0 = sK2) )),
% 2.40/0.68    inference(subsumption_resolution,[],[f884,f34])).
% 2.40/0.68  fof(f884,plain,(
% 2.40/0.68    ( ! [X2] : (~r1_tarski(k1_xboole_0,k1_relat_1(X2)) | ~v1_funct_1(sK2) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(sK2) | k1_funct_1(sK2,sK4(sK2,X2)) != k1_funct_1(X2,sK4(sK2,X2)) | r1_tarski(sK2,X2) | k1_xboole_0 = sK2) )),
% 2.40/0.68    inference(superposition,[],[f51,f875])).
% 2.40/0.68  fof(f1310,plain,(
% 2.40/0.68    k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = sK2 | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | sK4(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2))),
% 2.40/0.68    inference(subsumption_resolution,[],[f1309,f114])).
% 2.40/0.68  fof(f1309,plain,(
% 2.40/0.68    k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1))) | ~v1_relat_1(sK2) | k1_xboole_0 = sK2 | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | sK4(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2))),
% 2.40/0.68    inference(subsumption_resolution,[],[f1307,f34])).
% 2.40/0.68  fof(f1307,plain,(
% 2.40/0.68    ~v1_funct_1(sK2) | k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1))) | ~v1_relat_1(sK2) | k1_xboole_0 = sK2 | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | sK4(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2))),
% 2.40/0.68    inference(duplicate_literal_removal,[],[f1301])).
% 2.40/0.68  fof(f1301,plain,(
% 2.40/0.68    ~v1_funct_1(sK2) | k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1))) | ~v1_relat_1(sK2) | k1_xboole_0 = sK2 | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2 | sK4(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2))),
% 2.40/0.68    inference(resolution,[],[f1114,f1087])).
% 2.40/0.68  fof(f1114,plain,(
% 2.40/0.68    ( ! [X0] : (~r1_tarski(k4_tmap_1(sK0,sK1),X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK4(sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1))) | ~v1_relat_1(X0) | k1_xboole_0 = sK2 | r1_tarski(sK2,k4_tmap_1(sK0,sK1))) )),
% 2.40/0.68    inference(duplicate_literal_removal,[],[f1111])).
% 2.40/0.68  fof(f1111,plain,(
% 2.40/0.68    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK4(sK2,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1))) | ~r1_tarski(k4_tmap_1(sK0,sK1),X0) | k1_xboole_0 = sK2 | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2) )),
% 2.40/0.68    inference(resolution,[],[f952,f1008])).
% 2.40/0.68  fof(f1008,plain,(
% 2.40/0.68    r2_hidden(sK4(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2),
% 2.40/0.68    inference(subsumption_resolution,[],[f1007,f90])).
% 2.40/0.68  fof(f1007,plain,(
% 2.40/0.68    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK4(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2),
% 2.40/0.68    inference(subsumption_resolution,[],[f1006,f128])).
% 2.40/0.68  fof(f1006,plain,(
% 2.40/0.68    ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK4(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2),
% 2.40/0.68    inference(subsumption_resolution,[],[f1004,f70])).
% 2.40/0.68  fof(f1004,plain,(
% 2.40/0.68    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK4(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2),
% 2.40/0.68    inference(duplicate_literal_removal,[],[f1003])).
% 2.40/0.68  fof(f1003,plain,(
% 2.40/0.68    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK4(sK2,k4_tmap_1(sK0,sK1)),k1_xboole_0) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 2.40/0.68    inference(superposition,[],[f888,f932])).
% 2.40/0.68  fof(f888,plain,(
% 2.40/0.68    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK4(sK2,X0),k1_xboole_0) | r1_tarski(sK2,X0) | k1_xboole_0 = sK2) )),
% 2.40/0.68    inference(subsumption_resolution,[],[f887,f114])).
% 2.40/0.68  fof(f887,plain,(
% 2.40/0.68    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK2) | r2_hidden(sK4(sK2,X0),k1_xboole_0) | r1_tarski(sK2,X0) | k1_xboole_0 = sK2) )),
% 2.40/0.68    inference(subsumption_resolution,[],[f882,f34])).
% 2.40/0.68  fof(f882,plain,(
% 2.40/0.68    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | ~v1_funct_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK2) | r2_hidden(sK4(sK2,X0),k1_xboole_0) | r1_tarski(sK2,X0) | k1_xboole_0 = sK2) )),
% 2.40/0.68    inference(superposition,[],[f50,f875])).
% 2.40/0.68  fof(f952,plain,(
% 2.40/0.68    ( ! [X4,X5] : (~r2_hidden(X4,k1_xboole_0) | ~v1_relat_1(X5) | ~v1_funct_1(X5) | k1_funct_1(k4_tmap_1(sK0,sK1),X4) = k1_funct_1(X5,X4) | ~r1_tarski(k4_tmap_1(sK0,sK1),X5) | k1_xboole_0 = sK2) )),
% 2.40/0.68    inference(subsumption_resolution,[],[f951,f128])).
% 2.40/0.68  fof(f951,plain,(
% 2.40/0.68    ( ! [X4,X5] : (~r2_hidden(X4,k1_xboole_0) | ~v1_relat_1(X5) | ~v1_funct_1(X5) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X4) = k1_funct_1(X5,X4) | ~r1_tarski(k4_tmap_1(sK0,sK1),X5) | k1_xboole_0 = sK2) )),
% 2.40/0.68    inference(subsumption_resolution,[],[f942,f90])).
% 2.40/0.68  fof(f942,plain,(
% 2.40/0.68    ( ! [X4,X5] : (~r2_hidden(X4,k1_xboole_0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(X5) | ~v1_funct_1(X5) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X4) = k1_funct_1(X5,X4) | ~r1_tarski(k4_tmap_1(sK0,sK1),X5) | k1_xboole_0 = sK2) )),
% 2.40/0.68    inference(superposition,[],[f52,f932])).
% 2.40/0.68  fof(f1137,plain,(
% 2.40/0.68    k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2),
% 2.40/0.68    inference(subsumption_resolution,[],[f1136,f128])).
% 2.40/0.68  fof(f1136,plain,(
% 2.40/0.68    ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2),
% 2.40/0.68    inference(subsumption_resolution,[],[f1135,f90])).
% 2.40/0.68  fof(f1135,plain,(
% 2.40/0.68    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2),
% 2.40/0.68    inference(subsumption_resolution,[],[f1132,f70])).
% 2.40/0.68  fof(f1132,plain,(
% 2.40/0.68    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2),
% 2.40/0.68    inference(duplicate_literal_removal,[],[f1131])).
% 2.40/0.68  fof(f1131,plain,(
% 2.40/0.68    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2)) | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 2.40/0.68    inference(superposition,[],[f894,f932])).
% 2.40/0.68  fof(f894,plain,(
% 2.40/0.68    ( ! [X3] : (~r1_tarski(k1_relat_1(X3),k1_xboole_0) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | k1_funct_1(X3,sK4(X3,sK2)) != k1_funct_1(sK2,sK4(X3,sK2)) | r1_tarski(X3,sK2) | k1_xboole_0 = sK2) )),
% 2.40/0.68    inference(subsumption_resolution,[],[f893,f34])).
% 2.40/0.68  fof(f893,plain,(
% 2.40/0.68    ( ! [X3] : (~r1_tarski(k1_relat_1(X3),k1_xboole_0) | ~v1_funct_1(X3) | ~v1_funct_1(sK2) | ~v1_relat_1(X3) | k1_funct_1(X3,sK4(X3,sK2)) != k1_funct_1(sK2,sK4(X3,sK2)) | r1_tarski(X3,sK2) | k1_xboole_0 = sK2) )),
% 2.40/0.68    inference(subsumption_resolution,[],[f885,f114])).
% 2.40/0.68  fof(f885,plain,(
% 2.40/0.68    ( ! [X3] : (~r1_tarski(k1_relat_1(X3),k1_xboole_0) | ~v1_funct_1(X3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(X3) | k1_funct_1(X3,sK4(X3,sK2)) != k1_funct_1(sK2,sK4(X3,sK2)) | r1_tarski(X3,sK2) | k1_xboole_0 = sK2) )),
% 2.40/0.68    inference(superposition,[],[f51,f875])).
% 2.40/0.68  fof(f1617,plain,(
% 2.40/0.68    k1_xboole_0 = sK2 | sK2 = k4_tmap_1(sK0,sK1) | ~r1_tarski(k4_tmap_1(sK0,sK1),sK2)),
% 2.40/0.68    inference(duplicate_literal_removal,[],[f1613])).
% 2.40/0.68  fof(f1613,plain,(
% 2.40/0.68    k1_xboole_0 = sK2 | sK2 = k4_tmap_1(sK0,sK1) | ~r1_tarski(k4_tmap_1(sK0,sK1),sK2) | sK2 = k4_tmap_1(sK0,sK1)),
% 2.40/0.68    inference(resolution,[],[f1589,f61])).
% 2.40/0.68  fof(f1589,plain,(
% 2.40/0.68    r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2 | sK2 = k4_tmap_1(sK0,sK1)),
% 2.40/0.68    inference(subsumption_resolution,[],[f1587,f1033])).
% 2.40/0.68  fof(f1033,plain,(
% 2.40/0.68    r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2 | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1)))),
% 2.40/0.68    inference(duplicate_literal_removal,[],[f1030])).
% 2.40/0.68  fof(f1030,plain,(
% 2.40/0.68    r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2 | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = sK2),
% 2.40/0.68    inference(resolution,[],[f1008,f787])).
% 2.40/0.68  fof(f1587,plain,(
% 2.40/0.68    sK4(sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2 | sK2 = k4_tmap_1(sK0,sK1)),
% 2.40/0.68    inference(duplicate_literal_removal,[],[f1586])).
% 2.40/0.68  fof(f1586,plain,(
% 2.40/0.68    sK4(sK2,k4_tmap_1(sK0,sK1)) != k1_funct_1(sK2,sK4(sK2,k4_tmap_1(sK0,sK1))) | r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2 | sK2 = k4_tmap_1(sK0,sK1)),
% 2.40/0.68    inference(superposition,[],[f1122,f1394])).
% 2.40/0.68  fof(f1394,plain,(
% 2.40/0.68    sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = sK2 | sK2 = k4_tmap_1(sK0,sK1)),
% 2.40/0.68    inference(subsumption_resolution,[],[f1389,f1034])).
% 2.40/0.68  fof(f1034,plain,(
% 2.40/0.68    r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2 | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1)))),
% 2.40/0.68    inference(duplicate_literal_removal,[],[f1029])).
% 2.40/0.68  fof(f1029,plain,(
% 2.40/0.68    r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2 | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = sK2),
% 2.40/0.68    inference(resolution,[],[f1008,f788])).
% 2.40/0.68  fof(f1389,plain,(
% 2.40/0.68    k1_xboole_0 = sK2 | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1))) | ~r1_tarski(sK2,k4_tmap_1(sK0,sK1)) | sK2 = k4_tmap_1(sK0,sK1)),
% 2.40/0.68    inference(resolution,[],[f1273,f61])).
% 2.40/0.68  fof(f1273,plain,(
% 2.40/0.68    r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2 | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1)))),
% 2.40/0.68    inference(subsumption_resolution,[],[f1272,f1137])).
% 2.40/0.68  fof(f1272,plain,(
% 2.40/0.68    k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1)))),
% 2.40/0.68    inference(subsumption_resolution,[],[f1271,f128])).
% 2.40/0.68  fof(f1271,plain,(
% 2.40/0.68    k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2 | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1)))),
% 2.40/0.68    inference(subsumption_resolution,[],[f1270,f90])).
% 2.40/0.68  fof(f1270,plain,(
% 2.40/0.68    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2 | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1)))),
% 2.40/0.68    inference(duplicate_literal_removal,[],[f1265])).
% 2.40/0.68  fof(f1265,plain,(
% 2.40/0.68    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),sK2)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_xboole_0 = sK2 | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2 | sK4(sK2,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK2,k4_tmap_1(sK0,sK1)))),
% 2.40/0.68    inference(resolution,[],[f1090,f1034])).
% 2.40/0.68  fof(f1090,plain,(
% 2.40/0.68    ( ! [X1] : (~r1_tarski(sK2,X1) | ~v1_funct_1(X1) | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(X1,sK4(k4_tmap_1(sK0,sK1),sK2)) | ~v1_relat_1(X1) | k1_xboole_0 = sK2 | r1_tarski(k4_tmap_1(sK0,sK1),sK2)) )),
% 2.40/0.68    inference(duplicate_literal_removal,[],[f1089])).
% 2.40/0.68  fof(f1089,plain,(
% 2.40/0.68    ( ! [X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_funct_1(sK2,sK4(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(X1,sK4(k4_tmap_1(sK0,sK1),sK2)) | ~r1_tarski(sK2,X1) | k1_xboole_0 = sK2 | r1_tarski(k4_tmap_1(sK0,sK1),sK2) | k1_xboole_0 = sK2) )),
% 2.40/0.68    inference(resolution,[],[f896,f1080])).
% 2.40/0.68  fof(f896,plain,(
% 2.40/0.68    ( ! [X4,X5] : (~r2_hidden(X4,k1_xboole_0) | ~v1_relat_1(X5) | ~v1_funct_1(X5) | k1_funct_1(X5,X4) = k1_funct_1(sK2,X4) | ~r1_tarski(sK2,X5) | k1_xboole_0 = sK2) )),
% 2.40/0.68    inference(subsumption_resolution,[],[f895,f114])).
% 2.40/0.68  fof(f895,plain,(
% 2.40/0.68    ( ! [X4,X5] : (~r2_hidden(X4,k1_xboole_0) | ~v1_relat_1(X5) | ~v1_funct_1(X5) | ~v1_relat_1(sK2) | k1_funct_1(X5,X4) = k1_funct_1(sK2,X4) | ~r1_tarski(sK2,X5) | k1_xboole_0 = sK2) )),
% 2.40/0.68    inference(subsumption_resolution,[],[f886,f34])).
% 2.40/0.68  fof(f886,plain,(
% 2.40/0.68    ( ! [X4,X5] : (~r2_hidden(X4,k1_xboole_0) | ~v1_funct_1(sK2) | ~v1_relat_1(X5) | ~v1_funct_1(X5) | ~v1_relat_1(sK2) | k1_funct_1(X5,X4) = k1_funct_1(sK2,X4) | ~r1_tarski(sK2,X5) | k1_xboole_0 = sK2) )),
% 2.40/0.68    inference(superposition,[],[f52,f875])).
% 2.40/0.68  fof(f194,plain,(
% 2.40/0.68    k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2))),
% 2.40/0.68    inference(subsumption_resolution,[],[f193,f37])).
% 2.40/0.68  fof(f193,plain,(
% 2.40/0.68    k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)),
% 2.40/0.68    inference(subsumption_resolution,[],[f192,f36])).
% 2.40/0.68  fof(f192,plain,(
% 2.40/0.68    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)),
% 2.40/0.68    inference(subsumption_resolution,[],[f188,f34])).
% 2.40/0.68  fof(f188,plain,(
% 2.40/0.68    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) != k1_funct_1(sK2,sK3(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),sK2)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)),
% 2.40/0.68    inference(resolution,[],[f122,f35])).
% 2.40/0.68  fof(f122,plain,(
% 2.40/0.68    ( ! [X1] : (~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),X1)) != k1_funct_1(X1,sK3(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),X1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X1)) )),
% 2.40/0.68    inference(subsumption_resolution,[],[f121,f96])).
% 2.40/0.68  fof(f121,plain,(
% 2.40/0.68    ( ! [X1] : (~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),X1)) != k1_funct_1(X1,sK3(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),X1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X1)) )),
% 2.40/0.68    inference(subsumption_resolution,[],[f117,f90])).
% 2.40/0.68  fof(f117,plain,(
% 2.40/0.68    ( ! [X1] : (~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),X1)) != k1_funct_1(X1,sK3(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),X1)) | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X1)) )),
% 2.40/0.68    inference(resolution,[],[f93,f45])).
% 2.40/0.68  fof(f809,plain,(
% 2.40/0.68    k1_funct_1(k1_xboole_0,sK3(u1_struct_0(sK1),k1_xboole_0,sK2)) != k1_funct_1(sK2,sK3(u1_struct_0(sK1),k1_xboole_0,sK2)) | k1_xboole_0 = u1_struct_0(sK1)),
% 2.40/0.68    inference(superposition,[],[f194,f754])).
% 2.40/0.68  fof(f754,plain,(
% 2.40/0.68    k1_xboole_0 = k4_tmap_1(sK0,sK1) | k1_xboole_0 = u1_struct_0(sK1)),
% 2.40/0.68    inference(subsumption_resolution,[],[f750,f707])).
% 2.40/0.68  fof(f750,plain,(
% 2.40/0.68    k1_xboole_0 = u1_struct_0(sK1) | k1_xboole_0 = k4_tmap_1(sK0,sK1) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0)))),
% 2.40/0.68    inference(resolution,[],[f706,f73])).
% 2.40/0.68  fof(f1811,plain,(
% 2.40/0.68    ( ! [X3] : (k1_funct_1(k1_xboole_0,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK1))) )),
% 2.40/0.68    inference(backward_demodulation,[],[f727,f1791])).
% 2.40/0.68  fof(f2074,plain,(
% 2.40/0.68    r2_hidden(sK4(k4_tmap_1(sK0,sK1),k1_xboole_0),k1_xboole_0) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)),
% 2.40/0.68    inference(subsumption_resolution,[],[f2073,f128])).
% 2.40/0.68  fof(f2073,plain,(
% 2.40/0.68    ~v1_relat_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK4(k4_tmap_1(sK0,sK1),k1_xboole_0),k1_xboole_0) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)),
% 2.40/0.68    inference(subsumption_resolution,[],[f2072,f90])).
% 2.40/0.68  fof(f2072,plain,(
% 2.40/0.68    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK4(k4_tmap_1(sK0,sK1),k1_xboole_0),k1_xboole_0) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)),
% 2.40/0.68    inference(subsumption_resolution,[],[f2071,f70])).
% 2.40/0.68  fof(f2071,plain,(
% 2.40/0.68    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK4(k4_tmap_1(sK0,sK1),k1_xboole_0),k1_xboole_0) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)),
% 2.40/0.68    inference(superposition,[],[f2032,f2007])).
% 2.40/0.68  fof(f2007,plain,(
% 2.40/0.68    k1_xboole_0 = k1_relat_1(k4_tmap_1(sK0,sK1))),
% 2.40/0.68    inference(backward_demodulation,[],[f1934,f2006])).
% 2.40/0.68  fof(f2006,plain,(
% 2.40/0.68    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1))),
% 2.40/0.68    inference(subsumption_resolution,[],[f2001,f1930])).
% 2.40/0.68  fof(f1930,plain,(
% 2.40/0.68    m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 2.40/0.68    inference(backward_demodulation,[],[f707,f1921])).
% 2.40/0.68  fof(f2001,plain,(
% 2.40/0.68    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1)) | ~m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 2.40/0.68    inference(resolution,[],[f1929,f71])).
% 2.40/0.68  fof(f1929,plain,(
% 2.40/0.68    v1_funct_2(k4_tmap_1(sK0,sK1),k1_xboole_0,k1_xboole_0)),
% 2.40/0.68    inference(backward_demodulation,[],[f706,f1921])).
% 2.40/0.68  fof(f1934,plain,(
% 2.40/0.68    k1_relat_1(k4_tmap_1(sK0,sK1)) = k1_relset_1(k1_xboole_0,k1_xboole_0,k4_tmap_1(sK0,sK1))),
% 2.40/0.68    inference(backward_demodulation,[],[f718,f1921])).
% 2.40/0.68  fof(f2032,plain,(
% 2.40/0.68    ( ! [X1] : (~r1_tarski(k1_relat_1(X1),k1_xboole_0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | r2_hidden(sK4(X1,k1_xboole_0),k1_relat_1(X1)) | r1_tarski(X1,k1_xboole_0)) )),
% 2.40/0.68    inference(subsumption_resolution,[],[f2031,f1793])).
% 2.40/0.68  fof(f1793,plain,(
% 2.40/0.68    v1_funct_1(k1_xboole_0)),
% 2.40/0.68    inference(backward_demodulation,[],[f34,f1791])).
% 2.40/0.68  fof(f2031,plain,(
% 2.40/0.68    ( ! [X1] : (~r1_tarski(k1_relat_1(X1),k1_xboole_0) | ~v1_funct_1(X1) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(X1) | r2_hidden(sK4(X1,k1_xboole_0),k1_relat_1(X1)) | r1_tarski(X1,k1_xboole_0)) )),
% 2.40/0.68    inference(subsumption_resolution,[],[f2025,f1794])).
% 2.40/0.68  fof(f1794,plain,(
% 2.40/0.68    v1_relat_1(k1_xboole_0)),
% 2.40/0.68    inference(backward_demodulation,[],[f114,f1791])).
% 2.40/0.68  fof(f2025,plain,(
% 2.40/0.68    ( ! [X1] : (~r1_tarski(k1_relat_1(X1),k1_xboole_0) | ~v1_funct_1(X1) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(X1) | r2_hidden(sK4(X1,k1_xboole_0),k1_relat_1(X1)) | r1_tarski(X1,k1_xboole_0)) )),
% 2.40/0.68    inference(superposition,[],[f50,f1989])).
% 2.40/0.68  fof(f1989,plain,(
% 2.40/0.68    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.40/0.68    inference(backward_demodulation,[],[f1956,f1988])).
% 2.40/0.68  fof(f1988,plain,(
% 2.40/0.68    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 2.40/0.68    inference(subsumption_resolution,[],[f1982,f1954])).
% 2.40/0.68  fof(f1954,plain,(
% 2.40/0.68    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 2.40/0.68    inference(backward_demodulation,[],[f1803,f1921])).
% 2.40/0.68  fof(f1803,plain,(
% 2.40/0.68    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0)))),
% 2.40/0.68    inference(backward_demodulation,[],[f702,f1791])).
% 2.40/0.68  fof(f1982,plain,(
% 2.40/0.68    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 2.40/0.68    inference(resolution,[],[f1953,f71])).
% 2.40/0.68  fof(f1953,plain,(
% 2.40/0.68    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 2.40/0.68    inference(backward_demodulation,[],[f1802,f1921])).
% 2.40/0.68  fof(f1802,plain,(
% 2.40/0.68    v1_funct_2(k1_xboole_0,u1_struct_0(sK1),k1_xboole_0)),
% 2.40/0.68    inference(backward_demodulation,[],[f701,f1791])).
% 2.40/0.68  fof(f1956,plain,(
% 2.40/0.68    k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 2.40/0.68    inference(backward_demodulation,[],[f1805,f1921])).
% 2.40/0.68  fof(f1805,plain,(
% 2.40/0.68    k1_relat_1(k1_xboole_0) = k1_relset_1(u1_struct_0(sK1),k1_xboole_0,k1_xboole_0)),
% 2.40/0.68    inference(backward_demodulation,[],[f713,f1791])).
% 2.40/0.68  fof(f2189,plain,(
% 2.40/0.68    sK4(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) | ~r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 2.40/0.68    inference(resolution,[],[f2170,f61])).
% 2.40/0.68  fof(f2170,plain,(
% 2.40/0.68    r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | sK4(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0))),
% 2.40/0.68    inference(subsumption_resolution,[],[f2169,f2089])).
% 2.40/0.68  fof(f2089,plain,(
% 2.40/0.68    k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))),
% 2.40/0.68    inference(subsumption_resolution,[],[f2088,f90])).
% 2.40/0.68  fof(f2088,plain,(
% 2.40/0.68    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))),
% 2.40/0.68    inference(subsumption_resolution,[],[f2087,f128])).
% 2.40/0.68  fof(f2087,plain,(
% 2.40/0.68    ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))),
% 2.40/0.68    inference(subsumption_resolution,[],[f2086,f70])).
% 2.40/0.68  fof(f2086,plain,(
% 2.40/0.68    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))),
% 2.40/0.68    inference(superposition,[],[f2034,f2007])).
% 2.40/0.68  fof(f2034,plain,(
% 2.40/0.68    ( ! [X2] : (~r1_tarski(k1_xboole_0,k1_relat_1(X2)) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,X2)) != k1_funct_1(X2,sK4(k1_xboole_0,X2)) | r1_tarski(k1_xboole_0,X2)) )),
% 2.40/0.68    inference(subsumption_resolution,[],[f2033,f1794])).
% 2.40/0.68  fof(f2033,plain,(
% 2.40/0.68    ( ! [X2] : (~r1_tarski(k1_xboole_0,k1_relat_1(X2)) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(k1_xboole_0) | k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,X2)) != k1_funct_1(X2,sK4(k1_xboole_0,X2)) | r1_tarski(k1_xboole_0,X2)) )),
% 2.40/0.68    inference(subsumption_resolution,[],[f2026,f1793])).
% 2.40/0.68  fof(f2026,plain,(
% 2.40/0.68    ( ! [X2] : (~r1_tarski(k1_xboole_0,k1_relat_1(X2)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(k1_xboole_0) | k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,X2)) != k1_funct_1(X2,sK4(k1_xboole_0,X2)) | r1_tarski(k1_xboole_0,X2)) )),
% 2.40/0.68    inference(superposition,[],[f51,f1989])).
% 2.40/0.68  fof(f2169,plain,(
% 2.40/0.68    k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | sK4(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0))),
% 2.40/0.68    inference(subsumption_resolution,[],[f2168,f1794])).
% 2.40/0.69  fof(f2168,plain,(
% 2.40/0.69    k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) | ~v1_relat_1(k1_xboole_0) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | sK4(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0))),
% 2.40/0.69    inference(subsumption_resolution,[],[f2162,f1793])).
% 2.40/0.69  fof(f2162,plain,(
% 2.40/0.69    ~v1_funct_1(k1_xboole_0) | k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) | ~v1_relat_1(k1_xboole_0) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | sK4(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k1_xboole_0,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0))),
% 2.40/0.69    inference(resolution,[],[f2084,f2099])).
% 2.40/0.69  fof(f2084,plain,(
% 2.40/0.69    ( ! [X0] : (~r1_tarski(k4_tmap_1(sK0,sK1),X0) | ~v1_funct_1(X0) | k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(X0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) | ~v1_relat_1(X0) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))) )),
% 2.40/0.69    inference(resolution,[],[f2061,f2069])).
% 2.40/0.69  fof(f2069,plain,(
% 2.40/0.69    r2_hidden(sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)),k1_xboole_0) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))),
% 2.40/0.69    inference(subsumption_resolution,[],[f2068,f90])).
% 2.40/0.69  fof(f2068,plain,(
% 2.40/0.69    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)),k1_xboole_0) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))),
% 2.40/0.69    inference(subsumption_resolution,[],[f2067,f128])).
% 2.40/0.69  fof(f2067,plain,(
% 2.40/0.69    ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)),k1_xboole_0) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))),
% 2.40/0.69    inference(subsumption_resolution,[],[f2066,f70])).
% 2.40/0.69  fof(f2066,plain,(
% 2.40/0.69    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | r2_hidden(sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)),k1_xboole_0) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1))),
% 2.40/0.69    inference(superposition,[],[f2030,f2007])).
% 2.40/0.69  fof(f2030,plain,(
% 2.40/0.69    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK4(k1_xboole_0,X0),k1_xboole_0) | r1_tarski(k1_xboole_0,X0)) )),
% 2.40/0.69    inference(subsumption_resolution,[],[f2029,f1794])).
% 2.40/0.69  fof(f2029,plain,(
% 2.40/0.69    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(k1_xboole_0) | r2_hidden(sK4(k1_xboole_0,X0),k1_xboole_0) | r1_tarski(k1_xboole_0,X0)) )),
% 2.40/0.69    inference(subsumption_resolution,[],[f2024,f1793])).
% 2.40/0.69  fof(f2024,plain,(
% 2.40/0.69    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(k1_xboole_0) | r2_hidden(sK4(k1_xboole_0,X0),k1_xboole_0) | r1_tarski(k1_xboole_0,X0)) )),
% 2.40/0.69    inference(superposition,[],[f50,f1989])).
% 2.40/0.69  fof(f2061,plain,(
% 2.40/0.69    ( ! [X4,X5] : (~r2_hidden(X4,k1_xboole_0) | ~v1_relat_1(X5) | ~v1_funct_1(X5) | k1_funct_1(k4_tmap_1(sK0,sK1),X4) = k1_funct_1(X5,X4) | ~r1_tarski(k4_tmap_1(sK0,sK1),X5)) )),
% 2.40/0.69    inference(subsumption_resolution,[],[f2060,f128])).
% 2.40/0.69  fof(f2060,plain,(
% 2.40/0.69    ( ! [X4,X5] : (~r2_hidden(X4,k1_xboole_0) | ~v1_relat_1(X5) | ~v1_funct_1(X5) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X4) = k1_funct_1(X5,X4) | ~r1_tarski(k4_tmap_1(sK0,sK1),X5)) )),
% 2.40/0.69    inference(subsumption_resolution,[],[f2051,f90])).
% 2.40/0.69  fof(f2051,plain,(
% 2.40/0.69    ( ! [X4,X5] : (~r2_hidden(X4,k1_xboole_0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(X5) | ~v1_funct_1(X5) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k4_tmap_1(sK0,sK1),X4) = k1_funct_1(X5,X4) | ~r1_tarski(k4_tmap_1(sK0,sK1),X5)) )),
% 2.40/0.69    inference(superposition,[],[f52,f2007])).
% 2.40/0.69  fof(f2242,plain,(
% 2.40/0.69    sK4(k4_tmap_1(sK0,sK1),k1_xboole_0) != k1_funct_1(k1_xboole_0,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 2.40/0.69    inference(superposition,[],[f2094,f2214])).
% 2.40/0.69  fof(f2214,plain,(
% 2.40/0.69    sK4(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 2.40/0.69    inference(subsumption_resolution,[],[f2212,f2097])).
% 2.40/0.69  fof(f2097,plain,(
% 2.40/0.69    r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | sK4(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),k1_xboole_0))),
% 2.40/0.69    inference(resolution,[],[f2074,f1939])).
% 2.40/0.69  fof(f1939,plain,(
% 2.40/0.69    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = X0) )),
% 2.40/0.69    inference(backward_demodulation,[],[f728,f1921])).
% 2.40/0.69  fof(f2212,plain,(
% 2.40/0.69    sK4(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) | ~r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 2.40/0.69    inference(resolution,[],[f2167,f61])).
% 2.40/0.69  fof(f2167,plain,(
% 2.40/0.69    r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | sK4(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),k1_xboole_0))),
% 2.40/0.69    inference(subsumption_resolution,[],[f2166,f2089])).
% 2.40/0.69  fof(f2166,plain,(
% 2.40/0.69    k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | sK4(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),k1_xboole_0))),
% 2.40/0.69    inference(subsumption_resolution,[],[f2165,f1794])).
% 2.40/0.69  fof(f2165,plain,(
% 2.40/0.69    k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) | ~v1_relat_1(k1_xboole_0) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | sK4(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),k1_xboole_0))),
% 2.40/0.69    inference(subsumption_resolution,[],[f2161,f1793])).
% 2.40/0.69  fof(f2161,plain,(
% 2.40/0.69    ~v1_funct_1(k1_xboole_0) | k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) | ~v1_relat_1(k1_xboole_0) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | sK4(k4_tmap_1(sK0,sK1),k1_xboole_0) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),k1_xboole_0))),
% 2.40/0.69    inference(resolution,[],[f2084,f2097])).
% 2.40/0.69  fof(f2094,plain,(
% 2.40/0.69    k1_funct_1(k1_xboole_0,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)),
% 2.40/0.69    inference(subsumption_resolution,[],[f2093,f128])).
% 2.40/0.69  fof(f2093,plain,(
% 2.40/0.69    ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k1_xboole_0,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)),
% 2.40/0.69    inference(subsumption_resolution,[],[f2092,f90])).
% 2.40/0.69  fof(f2092,plain,(
% 2.40/0.69    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k1_xboole_0,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)),
% 2.40/0.69    inference(subsumption_resolution,[],[f2091,f70])).
% 2.40/0.69  fof(f2091,plain,(
% 2.40/0.69    ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | ~v1_relat_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k1_xboole_0,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) != k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)),
% 2.40/0.69    inference(superposition,[],[f2036,f2007])).
% 2.40/0.69  fof(f2036,plain,(
% 2.40/0.69    ( ! [X3] : (~r1_tarski(k1_relat_1(X3),k1_xboole_0) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | k1_funct_1(X3,sK4(X3,k1_xboole_0)) != k1_funct_1(k1_xboole_0,sK4(X3,k1_xboole_0)) | r1_tarski(X3,k1_xboole_0)) )),
% 2.40/0.69    inference(subsumption_resolution,[],[f2035,f1793])).
% 2.40/0.69  fof(f2035,plain,(
% 2.40/0.69    ( ! [X3] : (~r1_tarski(k1_relat_1(X3),k1_xboole_0) | ~v1_funct_1(X3) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(X3) | k1_funct_1(X3,sK4(X3,k1_xboole_0)) != k1_funct_1(k1_xboole_0,sK4(X3,k1_xboole_0)) | r1_tarski(X3,k1_xboole_0)) )),
% 2.40/0.69    inference(subsumption_resolution,[],[f2027,f1794])).
% 2.40/0.69  fof(f2027,plain,(
% 2.40/0.69    ( ! [X3] : (~r1_tarski(k1_relat_1(X3),k1_xboole_0) | ~v1_funct_1(X3) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(X3) | k1_funct_1(X3,sK4(X3,k1_xboole_0)) != k1_funct_1(k1_xboole_0,sK4(X3,k1_xboole_0)) | r1_tarski(X3,k1_xboole_0)) )),
% 2.40/0.69    inference(superposition,[],[f51,f1989])).
% 2.40/0.69  fof(f2250,plain,(
% 2.40/0.69    k1_xboole_0 = k4_tmap_1(sK0,sK1) | ~r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)),
% 2.40/0.69    inference(duplicate_literal_removal,[],[f2248])).
% 2.40/0.69  fof(f2248,plain,(
% 2.40/0.69    k1_xboole_0 = k4_tmap_1(sK0,sK1) | ~r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 2.40/0.69    inference(resolution,[],[f2241,f61])).
% 2.40/0.69  fof(f2241,plain,(
% 2.40/0.69    r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 2.40/0.69    inference(subsumption_resolution,[],[f2240,f2180])).
% 2.40/0.69  fof(f2180,plain,(
% 2.40/0.69    sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 2.40/0.69    inference(duplicate_literal_removal,[],[f2175])).
% 2.40/0.69  fof(f2175,plain,(
% 2.40/0.69    sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) | sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 2.40/0.69    inference(resolution,[],[f2160,f2113])).
% 2.40/0.69  fof(f2113,plain,(
% 2.40/0.69    ~r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 2.40/0.69    inference(resolution,[],[f2080,f61])).
% 2.40/0.69  fof(f2080,plain,(
% 2.40/0.69    r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)))),
% 2.40/0.69    inference(resolution,[],[f2069,f1960])).
% 2.40/0.69  fof(f2160,plain,(
% 2.40/0.69    r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)))),
% 2.40/0.69    inference(subsumption_resolution,[],[f2159,f2094])).
% 2.40/0.69  fof(f2159,plain,(
% 2.40/0.69    k1_funct_1(k1_xboole_0,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)))),
% 2.40/0.69    inference(subsumption_resolution,[],[f2158,f90])).
% 2.40/0.69  fof(f2158,plain,(
% 2.40/0.69    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k1_xboole_0,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)))),
% 2.40/0.69    inference(subsumption_resolution,[],[f2152,f128])).
% 2.40/0.69  fof(f2152,plain,(
% 2.40/0.69    ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k1_xboole_0,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)))),
% 2.40/0.69    inference(resolution,[],[f2096,f2080])).
% 2.40/0.69  fof(f2096,plain,(
% 2.40/0.69    ( ! [X1] : (~r1_tarski(k1_xboole_0,X1) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_funct_1(k1_xboole_0,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(X1,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0)) )),
% 2.40/0.69    inference(resolution,[],[f2074,f2038])).
% 2.40/0.69  fof(f2038,plain,(
% 2.40/0.69    ( ! [X4,X5] : (~r2_hidden(X4,k1_xboole_0) | ~v1_relat_1(X5) | ~v1_funct_1(X5) | k1_funct_1(X5,X4) = k1_funct_1(k1_xboole_0,X4) | ~r1_tarski(k1_xboole_0,X5)) )),
% 2.40/0.69    inference(subsumption_resolution,[],[f2037,f1794])).
% 2.40/0.69  fof(f2037,plain,(
% 2.40/0.69    ( ! [X4,X5] : (~r2_hidden(X4,k1_xboole_0) | ~v1_relat_1(X5) | ~v1_funct_1(X5) | ~v1_relat_1(k1_xboole_0) | k1_funct_1(X5,X4) = k1_funct_1(k1_xboole_0,X4) | ~r1_tarski(k1_xboole_0,X5)) )),
% 2.40/0.69    inference(subsumption_resolution,[],[f2028,f1793])).
% 2.40/0.69  fof(f2028,plain,(
% 2.40/0.69    ( ! [X4,X5] : (~r2_hidden(X4,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(X5) | ~v1_funct_1(X5) | ~v1_relat_1(k1_xboole_0) | k1_funct_1(X5,X4) = k1_funct_1(k1_xboole_0,X4) | ~r1_tarski(k1_xboole_0,X5)) )),
% 2.40/0.69    inference(superposition,[],[f52,f1989])).
% 2.40/0.69  fof(f2240,plain,(
% 2.40/0.69    sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)) != k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) | r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 2.40/0.69    inference(superposition,[],[f2089,f2203])).
% 2.40/0.69  fof(f2203,plain,(
% 2.40/0.69    sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 2.40/0.69    inference(subsumption_resolution,[],[f2201,f2078])).
% 2.40/0.69  fof(f2078,plain,(
% 2.40/0.69    r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)))),
% 2.40/0.69    inference(resolution,[],[f2069,f1939])).
% 2.40/0.69  fof(f2201,plain,(
% 2.40/0.69    sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k1_xboole_0,k4_tmap_1(sK0,sK1))) | ~r1_tarski(k1_xboole_0,k4_tmap_1(sK0,sK1)) | k1_xboole_0 = k4_tmap_1(sK0,sK1)),
% 2.40/0.69    inference(resolution,[],[f2157,f61])).
% 2.40/0.69  fof(f2157,plain,(
% 2.40/0.69    r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)))),
% 2.40/0.69    inference(subsumption_resolution,[],[f2156,f2094])).
% 2.40/0.69  fof(f2156,plain,(
% 2.40/0.69    k1_funct_1(k1_xboole_0,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)))),
% 2.40/0.69    inference(subsumption_resolution,[],[f2155,f90])).
% 2.40/0.69  fof(f2155,plain,(
% 2.40/0.69    ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k1_xboole_0,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)))),
% 2.40/0.69    inference(subsumption_resolution,[],[f2151,f128])).
% 2.40/0.69  fof(f2151,plain,(
% 2.40/0.69    ~v1_relat_1(k4_tmap_1(sK0,sK1)) | ~v1_funct_1(k4_tmap_1(sK0,sK1)) | k1_funct_1(k1_xboole_0,sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k4_tmap_1(sK0,sK1),k1_xboole_0)) | r1_tarski(k4_tmap_1(sK0,sK1),k1_xboole_0) | sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)) = k1_funct_1(k4_tmap_1(sK0,sK1),sK4(k1_xboole_0,k4_tmap_1(sK0,sK1)))),
% 2.40/0.69    inference(resolution,[],[f2096,f2078])).
% 2.40/0.69  fof(f1950,plain,(
% 2.40/0.69    k1_funct_1(k4_tmap_1(sK0,sK1),sK3(k1_xboole_0,k4_tmap_1(sK0,sK1),k1_xboole_0)) != k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k4_tmap_1(sK0,sK1),k1_xboole_0))),
% 2.40/0.69    inference(backward_demodulation,[],[f1799,f1921])).
% 2.40/0.69  fof(f1799,plain,(
% 2.40/0.69    k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),k1_xboole_0)) != k1_funct_1(k1_xboole_0,sK3(u1_struct_0(sK1),k4_tmap_1(sK0,sK1),k1_xboole_0))),
% 2.40/0.69    inference(backward_demodulation,[],[f194,f1791])).
% 2.40/0.69  % SZS output end Proof for theBenchmark
% 2.40/0.69  % (32020)------------------------------
% 2.40/0.69  % (32020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.40/0.69  % (32020)Termination reason: Refutation
% 2.40/0.69  
% 2.40/0.69  % (32020)Memory used [KB]: 6908
% 2.40/0.69  % (32020)Time elapsed: 0.224 s
% 2.40/0.69  % (32020)------------------------------
% 2.40/0.69  % (32020)------------------------------
% 2.40/0.69  % (32014)Success in time 0.327 s
%------------------------------------------------------------------------------
