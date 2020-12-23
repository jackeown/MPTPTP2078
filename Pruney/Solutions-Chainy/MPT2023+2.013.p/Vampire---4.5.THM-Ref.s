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
% DateTime   : Thu Dec  3 13:23:08 EST 2020

% Result     : Theorem 2.16s
% Output     : Refutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 833 expanded)
%              Number of leaves         :   27 ( 320 expanded)
%              Depth                    :   18
%              Number of atoms          :  602 (4548 expanded)
%              Number of equality atoms :   19 ( 139 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1951,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f181,f1849,f1874,f1881,f1920,f1925,f1950])).

fof(f1950,plain,(
    spl11_17 ),
    inference(avatar_contradiction_clause,[],[f1949])).

fof(f1949,plain,
    ( $false
    | spl11_17 ),
    inference(subsumption_resolution,[],[f1947,f240])).

fof(f240,plain,(
    r1_tarski(sK8,u1_struct_0(sK5)) ),
    inference(resolution,[],[f228,f148])).

fof(f148,plain,(
    ! [X10,X8,X9] :
      ( ~ sP2(X8,X9,X10)
      | r1_tarski(X10,u1_struct_0(X8)) ) ),
    inference(resolution,[],[f145,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP2(X0,X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f144])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP2(X0,X1,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(superposition,[],[f66,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( sK9(X0,X1,X2) = X2
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( v3_pre_topc(sK9(X0,X1,X2),X0)
        & r2_hidden(X1,sK9(X0,X1,X2))
        & sK9(X0,X1,X2) = X2
        & m1_subset_1(sK9(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f41,f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( v3_pre_topc(X3,X0)
          & r2_hidden(X1,X3)
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v3_pre_topc(sK9(X0,X1,X2),X0)
        & r2_hidden(X1,sK9(X0,X1,X2))
        & sK9(X0,X1,X2) = X2
        & m1_subset_1(sK9(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( v3_pre_topc(X3,X0)
          & r2_hidden(X1,X3)
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( v3_pre_topc(X3,X0)
          & r2_hidden(X1,X3)
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ sP2(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK9(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f228,plain,(
    sP2(sK5,sK6,sK8) ),
    inference(subsumption_resolution,[],[f227,f53])).

fof(f53,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK7,sK8),u1_struct_0(k9_yellow_6(sK5,sK6)))
    & m1_subset_1(sK8,u1_struct_0(k9_yellow_6(sK5,sK6)))
    & m1_subset_1(sK7,u1_struct_0(k9_yellow_6(sK5,sK6)))
    & m1_subset_1(sK6,u1_struct_0(sK5))
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f13,f34,f33,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                    & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
                & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK5,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK5,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK5,X1))) )
          & m1_subset_1(X1,u1_struct_0(sK5)) )
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK5,X1)))
                & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK5,X1))) )
            & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK5,X1))) )
        & m1_subset_1(X1,u1_struct_0(sK5)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK5,sK6)))
              & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK5,sK6))) )
          & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK5,sK6))) )
      & m1_subset_1(sK6,u1_struct_0(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK5,sK6)))
            & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK5,sK6))) )
        & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK5,sK6))) )
   => ( ? [X3] :
          ( ~ m1_subset_1(k3_xboole_0(sK7,X3),u1_struct_0(k9_yellow_6(sK5,sK6)))
          & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK5,sK6))) )
      & m1_subset_1(sK7,u1_struct_0(k9_yellow_6(sK5,sK6))) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X3] :
        ( ~ m1_subset_1(k3_xboole_0(sK7,X3),u1_struct_0(k9_yellow_6(sK5,sK6)))
        & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK5,sK6))) )
   => ( ~ m1_subset_1(k3_xboole_0(sK7,sK8),u1_struct_0(k9_yellow_6(sK5,sK6)))
      & m1_subset_1(sK8,u1_struct_0(k9_yellow_6(sK5,sK6))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))
                   => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))
                 => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_waybel_9)).

fof(f227,plain,
    ( sP2(sK5,sK6,sK8)
    | v2_struct_0(sK5) ),
    inference(subsumption_resolution,[],[f226,f54])).

fof(f54,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f226,plain,
    ( sP2(sK5,sK6,sK8)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5) ),
    inference(subsumption_resolution,[],[f225,f55])).

fof(f55,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f225,plain,
    ( sP2(sK5,sK6,sK8)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5) ),
    inference(subsumption_resolution,[],[f219,f56])).

fof(f56,plain,(
    m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f35])).

fof(f219,plain,
    ( sP2(sK5,sK6,sK8)
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5) ),
    inference(resolution,[],[f70,f58])).

fof(f58,plain,(
    m1_subset_1(sK8,u1_struct_0(k9_yellow_6(sK5,sK6))) ),
    inference(cnf_transformation,[],[f35])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | sP2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f17,f26])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_yellow_6)).

fof(f1947,plain,
    ( ~ r1_tarski(sK8,u1_struct_0(sK5))
    | spl11_17 ),
    inference(resolution,[],[f1919,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1919,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
    | spl11_17 ),
    inference(avatar_component_clause,[],[f1917])).

fof(f1917,plain,
    ( spl11_17
  <=> m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).

fof(f1925,plain,(
    spl11_16 ),
    inference(avatar_contradiction_clause,[],[f1924])).

fof(f1924,plain,
    ( $false
    | spl11_16 ),
    inference(subsumption_resolution,[],[f1922,f233])).

fof(f233,plain,(
    r1_tarski(sK7,u1_struct_0(sK5)) ),
    inference(resolution,[],[f224,f148])).

fof(f224,plain,(
    sP2(sK5,sK6,sK7) ),
    inference(subsumption_resolution,[],[f223,f53])).

fof(f223,plain,
    ( sP2(sK5,sK6,sK7)
    | v2_struct_0(sK5) ),
    inference(subsumption_resolution,[],[f222,f54])).

fof(f222,plain,
    ( sP2(sK5,sK6,sK7)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5) ),
    inference(subsumption_resolution,[],[f221,f55])).

fof(f221,plain,
    ( sP2(sK5,sK6,sK7)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5) ),
    inference(subsumption_resolution,[],[f218,f56])).

fof(f218,plain,
    ( sP2(sK5,sK6,sK7)
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5) ),
    inference(resolution,[],[f70,f57])).

fof(f57,plain,(
    m1_subset_1(sK7,u1_struct_0(k9_yellow_6(sK5,sK6))) ),
    inference(cnf_transformation,[],[f35])).

fof(f1922,plain,
    ( ~ r1_tarski(sK7,u1_struct_0(sK5))
    | spl11_16 ),
    inference(resolution,[],[f1915,f75])).

fof(f1915,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
    | spl11_16 ),
    inference(avatar_component_clause,[],[f1913])).

fof(f1913,plain,
    ( spl11_16
  <=> m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f1920,plain,
    ( ~ spl11_16
    | ~ spl11_17
    | spl11_15 ),
    inference(avatar_split_clause,[],[f1911,f1871,f1917,f1913])).

fof(f1871,plain,
    ( spl11_15
  <=> v3_pre_topc(k1_setfam_1(k2_tarski(sK7,sK8)),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f1911,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
    | spl11_15 ),
    inference(subsumption_resolution,[],[f1910,f54])).

fof(f1910,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v2_pre_topc(sK5)
    | spl11_15 ),
    inference(subsumption_resolution,[],[f1909,f55])).

fof(f1909,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | spl11_15 ),
    inference(subsumption_resolution,[],[f1908,f230])).

fof(f230,plain,(
    v3_pre_topc(sK7,sK5) ),
    inference(resolution,[],[f224,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | v3_pre_topc(X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ sP2(X0,X1,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(superposition,[],[f69,f67])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK9(X0,X1,X2),X0)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1908,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v3_pre_topc(sK7,sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | spl11_15 ),
    inference(subsumption_resolution,[],[f1905,f237])).

fof(f237,plain,(
    v3_pre_topc(sK8,sK5) ),
    inference(resolution,[],[f228,f99])).

fof(f1905,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v3_pre_topc(sK8,sK5)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v3_pre_topc(sK7,sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | spl11_15 ),
    inference(resolution,[],[f1873,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k1_setfam_1(k2_tarski(X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f76,f72])).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_tops_1)).

fof(f1873,plain,
    ( ~ v3_pre_topc(k1_setfam_1(k2_tarski(sK7,sK8)),sK5)
    | spl11_15 ),
    inference(avatar_component_clause,[],[f1871])).

fof(f1881,plain,(
    spl11_14 ),
    inference(avatar_contradiction_clause,[],[f1880])).

fof(f1880,plain,
    ( $false
    | spl11_14 ),
    inference(subsumption_resolution,[],[f1879,f229])).

fof(f229,plain,(
    r2_hidden(sK6,sK7) ),
    inference(resolution,[],[f224,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | r2_hidden(X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ sP2(X0,X1,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(superposition,[],[f68,f67])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK9(X0,X1,X2))
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1879,plain,
    ( ~ r2_hidden(sK6,sK7)
    | spl11_14 ),
    inference(subsumption_resolution,[],[f1878,f236])).

fof(f236,plain,(
    r2_hidden(sK6,sK8) ),
    inference(resolution,[],[f228,f97])).

fof(f1878,plain,
    ( ~ r2_hidden(sK6,sK8)
    | ~ r2_hidden(sK6,sK7)
    | spl11_14 ),
    inference(resolution,[],[f1875,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X1,X2)
      | ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ~ r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X1,X3,X0] :
      ( ( sP3(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP3(X1,X3,X0) ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X1,X3,X0] :
      ( ( sP3(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP3(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X1,X3,X0] :
      ( sP3(X1,X3,X0)
    <=> ( r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f1875,plain,
    ( ~ sP3(sK8,sK6,sK7)
    | spl11_14 ),
    inference(resolution,[],[f1869,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X0)))
      | ~ sP3(X0,X1,X2) ) ),
    inference(resolution,[],[f79,f92])).

fof(f92,plain,(
    ! [X0,X1] : sP4(X0,X1,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( sP4(X0,X1,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f85,f72])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( sP4(X0,X1,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP4(X0,X1,X2) )
      & ( sP4(X0,X1,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP4(X0,X1,X2) ) ),
    inference(definition_folding,[],[f1,f29,f28])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( sP4(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP3(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP4(X0,X1,X2)
      | ~ sP3(X1,X4,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ( ( ~ sP3(X1,sK10(X0,X1,X2),X0)
            | ~ r2_hidden(sK10(X0,X1,X2),X2) )
          & ( sP3(X1,sK10(X0,X1,X2),X0)
            | r2_hidden(sK10(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP3(X1,X4,X0) )
            & ( sP3(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f46,f47])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP3(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP3(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP3(X1,sK10(X0,X1,X2),X0)
          | ~ r2_hidden(sK10(X0,X1,X2),X2) )
        & ( sP3(X1,sK10(X0,X1,X2),X0)
          | r2_hidden(sK10(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP3(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP3(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP3(X1,X4,X0) )
            & ( sP3(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP3(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP3(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP3(X1,X3,X0) )
            & ( sP3(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f1869,plain,
    ( ~ r2_hidden(sK6,k1_setfam_1(k2_tarski(sK7,sK8)))
    | spl11_14 ),
    inference(avatar_component_clause,[],[f1867])).

fof(f1867,plain,
    ( spl11_14
  <=> r2_hidden(sK6,k1_setfam_1(k2_tarski(sK7,sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f1874,plain,
    ( ~ spl11_14
    | ~ spl11_15
    | spl11_2 ),
    inference(avatar_split_clause,[],[f1863,f178,f1871,f1867])).

fof(f178,plain,
    ( spl11_2
  <=> sP0(sK5,k1_setfam_1(k2_tarski(sK7,sK8)),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f1863,plain,
    ( ~ v3_pre_topc(k1_setfam_1(k2_tarski(sK7,sK8)),sK5)
    | ~ r2_hidden(sK6,k1_setfam_1(k2_tarski(sK7,sK8)))
    | spl11_2 ),
    inference(resolution,[],[f180,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ~ v3_pre_topc(X1,X0)
        | ~ r2_hidden(X2,X1) )
      & ( ( v3_pre_topc(X1,X0)
          & r2_hidden(X2,X1) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X2,X1] :
      ( ( sP0(X0,X2,X1)
        | ~ v3_pre_topc(X2,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( v3_pre_topc(X2,X0)
          & r2_hidden(X1,X2) )
        | ~ sP0(X0,X2,X1) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X2,X1] :
      ( ( sP0(X0,X2,X1)
        | ~ v3_pre_topc(X2,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( v3_pre_topc(X2,X0)
          & r2_hidden(X1,X2) )
        | ~ sP0(X0,X2,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X2,X1] :
      ( sP0(X0,X2,X1)
    <=> ( v3_pre_topc(X2,X0)
        & r2_hidden(X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f180,plain,
    ( ~ sP0(sK5,k1_setfam_1(k2_tarski(sK7,sK8)),sK6)
    | spl11_2 ),
    inference(avatar_component_clause,[],[f178])).

fof(f1849,plain,(
    spl11_1 ),
    inference(avatar_contradiction_clause,[],[f1842])).

fof(f1842,plain,
    ( $false
    | spl11_1 ),
    inference(subsumption_resolution,[],[f309,f1833])).

fof(f1833,plain,(
    ! [X10] : r1_tarski(k1_setfam_1(k2_tarski(sK7,X10)),u1_struct_0(sK5)) ),
    inference(resolution,[],[f1660,f115])).

fof(f115,plain,(
    ! [X12,X10,X11] :
      ( ~ sP4(X10,X11,X12)
      | r1_tarski(X12,X10) ) ),
    inference(superposition,[],[f88,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X2
      | ~ sP4(X0,X1,X2) ) ),
    inference(definition_unfolding,[],[f86,f72])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f88,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f71,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f1660,plain,(
    ! [X47] : sP4(u1_struct_0(sK5),k1_setfam_1(k2_tarski(sK7,X47)),k1_setfam_1(k2_tarski(sK7,X47))) ),
    inference(duplicate_literal_removal,[],[f1635])).

fof(f1635,plain,(
    ! [X47] :
      ( sP4(u1_struct_0(sK5),k1_setfam_1(k2_tarski(sK7,X47)),k1_setfam_1(k2_tarski(sK7,X47)))
      | sP4(u1_struct_0(sK5),k1_setfam_1(k2_tarski(sK7,X47)),k1_setfam_1(k2_tarski(sK7,X47))) ) ),
    inference(resolution,[],[f265,f349])).

fof(f349,plain,(
    ! [X11] :
      ( ~ r2_hidden(sK10(u1_struct_0(sK5),X11,X11),sK7)
      | sP4(u1_struct_0(sK5),X11,X11) ) ),
    inference(resolution,[],[f340,f232])).

fof(f232,plain,(
    ! [X1] :
      ( r2_hidden(X1,u1_struct_0(sK5))
      | ~ r2_hidden(X1,sK7) ) ),
    inference(resolution,[],[f224,f147])).

fof(f147,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ sP2(X4,X5,X6)
      | ~ r2_hidden(X7,X6)
      | r2_hidden(X7,u1_struct_0(X4)) ) ),
    inference(resolution,[],[f145,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f340,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(sK10(X6,X7,X7),X6)
      | sP4(X6,X7,X7) ) ),
    inference(subsumption_resolution,[],[f337,f184])).

fof(f184,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK10(X0,X1,X2),X2)
      | sP4(X0,X1,X2)
      | r2_hidden(sK10(X0,X1,X2),X1) ) ),
    inference(resolution,[],[f80,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( sP3(X1,sK10(X0,X1,X2),X0)
      | sP4(X0,X1,X2)
      | r2_hidden(sK10(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f337,plain,(
    ! [X6,X7] :
      ( sP4(X6,X7,X7)
      | ~ r2_hidden(sK10(X6,X7,X7),X7)
      | ~ r2_hidden(sK10(X6,X7,X7),X6) ) ),
    inference(duplicate_literal_removal,[],[f330])).

fof(f330,plain,(
    ! [X6,X7] :
      ( sP4(X6,X7,X7)
      | ~ r2_hidden(sK10(X6,X7,X7),X7)
      | ~ r2_hidden(sK10(X6,X7,X7),X6)
      | sP4(X6,X7,X7) ) ),
    inference(resolution,[],[f194,f260])).

fof(f260,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK10(X0,X1,X1),X1)
      | sP4(X0,X1,X1) ) ),
    inference(factoring,[],[f184])).

fof(f194,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(sK10(X3,X4,X5),X5)
      | sP4(X3,X4,X5)
      | ~ r2_hidden(sK10(X3,X4,X5),X4)
      | ~ r2_hidden(sK10(X3,X4,X5),X3) ) ),
    inference(resolution,[],[f81,f84])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X1,sK10(X0,X1,X2),X0)
      | sP4(X0,X1,X2)
      | ~ r2_hidden(sK10(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f265,plain,(
    ! [X12,X13,X11] :
      ( r2_hidden(sK10(X11,k1_setfam_1(k2_tarski(X12,X13)),k1_setfam_1(k2_tarski(X12,X13))),X12)
      | sP4(X11,k1_setfam_1(k2_tarski(X12,X13)),k1_setfam_1(k2_tarski(X12,X13))) ) ),
    inference(resolution,[],[f260,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2)))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f100,f88])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f73,f75])).

fof(f309,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_tarski(sK7,sK8)),u1_struct_0(sK5))
    | spl11_1 ),
    inference(subsumption_resolution,[],[f308,f53])).

fof(f308,plain,
    ( v2_struct_0(sK5)
    | ~ r1_tarski(k1_setfam_1(k2_tarski(sK7,sK8)),u1_struct_0(sK5))
    | spl11_1 ),
    inference(subsumption_resolution,[],[f307,f54])).

fof(f307,plain,
    ( ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ r1_tarski(k1_setfam_1(k2_tarski(sK7,sK8)),u1_struct_0(sK5))
    | spl11_1 ),
    inference(subsumption_resolution,[],[f306,f55])).

fof(f306,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ r1_tarski(k1_setfam_1(k2_tarski(sK7,sK8)),u1_struct_0(sK5))
    | spl11_1 ),
    inference(subsumption_resolution,[],[f305,f56])).

fof(f305,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ r1_tarski(k1_setfam_1(k2_tarski(sK7,sK8)),u1_struct_0(sK5))
    | spl11_1 ),
    inference(resolution,[],[f209,f176])).

fof(f176,plain,
    ( ~ sP1(sK6,k1_setfam_1(k2_tarski(sK7,sK8)),sK5)
    | spl11_1 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl11_1
  <=> sP1(sK6,k1_setfam_1(k2_tarski(sK7,sK8)),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f209,plain,(
    ! [X6,X4,X5] :
      ( sP1(X4,X5,X6)
      | ~ m1_subset_1(X4,u1_struct_0(X6))
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ r1_tarski(X5,u1_struct_0(X6)) ) ),
    inference(resolution,[],[f65,f75])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X1,X2,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X1,X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f15,f24,f23])).

fof(f24,plain,(
    ! [X1,X2,X0] :
      ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      <=> sP0(X0,X2,X1) )
      | ~ sP1(X1,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_yellow_6)).

fof(f181,plain,
    ( ~ spl11_1
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f169,f178,f174])).

fof(f169,plain,
    ( ~ sP0(sK5,k1_setfam_1(k2_tarski(sK7,sK8)),sK6)
    | ~ sP1(sK6,k1_setfam_1(k2_tarski(sK7,sK8)),sK5) ),
    inference(resolution,[],[f61,f137])).

fof(f137,plain,(
    ~ r2_hidden(k1_setfam_1(k2_tarski(sK7,sK8)),u1_struct_0(k9_yellow_6(sK5,sK6))) ),
    inference(condensation,[],[f135])).

fof(f135,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_setfam_1(k2_tarski(sK7,sK8)),X0)
      | ~ r2_hidden(k1_setfam_1(k2_tarski(sK7,sK8)),u1_struct_0(k9_yellow_6(sK5,sK6))) ) ),
    inference(resolution,[],[f130,f84])).

fof(f130,plain,(
    ! [X0] : ~ sP3(X0,k1_setfam_1(k2_tarski(sK7,sK8)),u1_struct_0(k9_yellow_6(sK5,sK6))) ),
    inference(resolution,[],[f129,f107])).

fof(f107,plain,(
    ! [X0] : ~ r2_hidden(k1_setfam_1(k2_tarski(sK7,sK8)),k1_setfam_1(k2_tarski(u1_struct_0(k9_yellow_6(sK5,sK6)),X0))) ),
    inference(resolution,[],[f103,f88])).

fof(f103,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(k9_yellow_6(sK5,sK6)))
      | ~ r2_hidden(k1_setfam_1(k2_tarski(sK7,sK8)),X0) ) ),
    inference(resolution,[],[f101,f87])).

fof(f87,plain,(
    ~ m1_subset_1(k1_setfam_1(k2_tarski(sK7,sK8)),u1_struct_0(k9_yellow_6(sK5,sK6))) ),
    inference(definition_unfolding,[],[f59,f72])).

fof(f59,plain,(
    ~ m1_subset_1(k3_xboole_0(sK7,sK8),u1_struct_0(k9_yellow_6(sK5,sK6))) ),
    inference(cnf_transformation,[],[f35])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X2)
      | ~ r1_tarski(X2,X1) ) ),
    inference(resolution,[],[f77,f75])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X0)))
      | ~ sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X0)))
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X0))) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X1,X2,X0] :
      ( ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
          | ~ sP0(X0,X2,X1) )
        & ( sP0(X0,X2,X1)
          | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) ) )
      | ~ sP1(X1,X2,X0) ) ),
    inference(nnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:11:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (24887)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (24872)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (24879)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.50  % (24871)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.50  % (24888)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (24867)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (24887)Refutation not found, incomplete strategy% (24887)------------------------------
% 0.20/0.51  % (24887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (24887)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (24887)Memory used [KB]: 10746
% 0.20/0.51  % (24887)Time elapsed: 0.058 s
% 0.20/0.51  % (24887)------------------------------
% 0.20/0.51  % (24887)------------------------------
% 0.20/0.51  % (24878)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (24877)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (24868)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (24880)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (24876)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (24865)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (24885)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (24867)Refutation not found, incomplete strategy% (24867)------------------------------
% 0.20/0.53  % (24867)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (24867)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (24867)Memory used [KB]: 10746
% 0.20/0.53  % (24867)Time elapsed: 0.127 s
% 0.20/0.53  % (24867)------------------------------
% 0.20/0.53  % (24867)------------------------------
% 0.20/0.53  % (24890)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (24866)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (24891)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (24869)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.54  % (24870)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (24876)Refutation not found, incomplete strategy% (24876)------------------------------
% 0.20/0.54  % (24876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (24876)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (24876)Memory used [KB]: 10746
% 0.20/0.54  % (24876)Time elapsed: 0.118 s
% 0.20/0.54  % (24876)------------------------------
% 0.20/0.54  % (24876)------------------------------
% 0.20/0.54  % (24889)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (24883)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (24882)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (24892)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (24884)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (24894)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (24893)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (24873)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.55  % (24875)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % (24873)Refutation not found, incomplete strategy% (24873)------------------------------
% 0.20/0.55  % (24873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (24873)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (24873)Memory used [KB]: 10746
% 0.20/0.55  % (24873)Time elapsed: 0.148 s
% 0.20/0.55  % (24873)------------------------------
% 0.20/0.55  % (24873)------------------------------
% 0.20/0.55  % (24874)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.55  % (24886)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (24875)Refutation not found, incomplete strategy% (24875)------------------------------
% 0.20/0.55  % (24875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (24875)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (24875)Memory used [KB]: 10746
% 0.20/0.55  % (24875)Time elapsed: 0.153 s
% 0.20/0.55  % (24875)------------------------------
% 0.20/0.55  % (24875)------------------------------
% 1.62/0.57  % (24881)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 2.05/0.63  % (24897)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.16/0.67  % (24899)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.16/0.68  % (24900)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.16/0.68  % (24898)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.16/0.69  % (24901)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.16/0.69  % (24892)Refutation found. Thanks to Tanya!
% 2.16/0.69  % SZS status Theorem for theBenchmark
% 2.16/0.69  % SZS output start Proof for theBenchmark
% 2.16/0.69  fof(f1951,plain,(
% 2.16/0.69    $false),
% 2.16/0.69    inference(avatar_sat_refutation,[],[f181,f1849,f1874,f1881,f1920,f1925,f1950])).
% 2.16/0.69  fof(f1950,plain,(
% 2.16/0.69    spl11_17),
% 2.16/0.69    inference(avatar_contradiction_clause,[],[f1949])).
% 2.16/0.69  fof(f1949,plain,(
% 2.16/0.69    $false | spl11_17),
% 2.16/0.69    inference(subsumption_resolution,[],[f1947,f240])).
% 2.16/0.69  fof(f240,plain,(
% 2.16/0.69    r1_tarski(sK8,u1_struct_0(sK5))),
% 2.16/0.69    inference(resolution,[],[f228,f148])).
% 2.16/0.69  fof(f148,plain,(
% 2.16/0.69    ( ! [X10,X8,X9] : (~sP2(X8,X9,X10) | r1_tarski(X10,u1_struct_0(X8))) )),
% 2.16/0.69    inference(resolution,[],[f145,f74])).
% 2.16/0.69  fof(f74,plain,(
% 2.16/0.69    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.16/0.69    inference(cnf_transformation,[],[f44])).
% 2.16/0.69  fof(f44,plain,(
% 2.16/0.69    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.16/0.69    inference(nnf_transformation,[],[f5])).
% 2.16/0.69  fof(f5,axiom,(
% 2.16/0.69    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.16/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.16/0.69  fof(f145,plain,(
% 2.16/0.69    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~sP2(X0,X1,X2)) )),
% 2.16/0.69    inference(duplicate_literal_removal,[],[f144])).
% 2.16/0.69  fof(f144,plain,(
% 2.16/0.69    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~sP2(X0,X1,X2) | ~sP2(X0,X1,X2)) )),
% 2.16/0.69    inference(superposition,[],[f66,f67])).
% 2.16/0.69  fof(f67,plain,(
% 2.16/0.69    ( ! [X2,X0,X1] : (sK9(X0,X1,X2) = X2 | ~sP2(X0,X1,X2)) )),
% 2.16/0.69    inference(cnf_transformation,[],[f43])).
% 2.16/0.69  fof(f43,plain,(
% 2.16/0.69    ! [X0,X1,X2] : ((v3_pre_topc(sK9(X0,X1,X2),X0) & r2_hidden(X1,sK9(X0,X1,X2)) & sK9(X0,X1,X2) = X2 & m1_subset_1(sK9(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~sP2(X0,X1,X2))),
% 2.16/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f41,f42])).
% 2.16/0.69  fof(f42,plain,(
% 2.16/0.69    ! [X2,X1,X0] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (v3_pre_topc(sK9(X0,X1,X2),X0) & r2_hidden(X1,sK9(X0,X1,X2)) & sK9(X0,X1,X2) = X2 & m1_subset_1(sK9(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.16/0.69    introduced(choice_axiom,[])).
% 2.16/0.69  fof(f41,plain,(
% 2.16/0.69    ! [X0,X1,X2] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP2(X0,X1,X2))),
% 2.16/0.69    inference(nnf_transformation,[],[f26])).
% 2.16/0.69  fof(f26,plain,(
% 2.16/0.69    ! [X0,X1,X2] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP2(X0,X1,X2))),
% 2.16/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 2.16/0.69  fof(f66,plain,(
% 2.16/0.69    ( ! [X2,X0,X1] : (m1_subset_1(sK9(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~sP2(X0,X1,X2)) )),
% 2.16/0.69    inference(cnf_transformation,[],[f43])).
% 2.16/0.69  fof(f228,plain,(
% 2.16/0.69    sP2(sK5,sK6,sK8)),
% 2.16/0.69    inference(subsumption_resolution,[],[f227,f53])).
% 2.16/0.69  fof(f53,plain,(
% 2.16/0.69    ~v2_struct_0(sK5)),
% 2.16/0.69    inference(cnf_transformation,[],[f35])).
% 2.16/0.69  fof(f35,plain,(
% 2.16/0.69    (((~m1_subset_1(k3_xboole_0(sK7,sK8),u1_struct_0(k9_yellow_6(sK5,sK6))) & m1_subset_1(sK8,u1_struct_0(k9_yellow_6(sK5,sK6)))) & m1_subset_1(sK7,u1_struct_0(k9_yellow_6(sK5,sK6)))) & m1_subset_1(sK6,u1_struct_0(sK5))) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)),
% 2.16/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f13,f34,f33,f32,f31])).
% 2.16/0.69  fof(f31,plain,(
% 2.16/0.69    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK5,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK5,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK5,X1)))) & m1_subset_1(X1,u1_struct_0(sK5))) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))),
% 2.16/0.69    introduced(choice_axiom,[])).
% 2.16/0.69  fof(f32,plain,(
% 2.16/0.69    ? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK5,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK5,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK5,X1)))) & m1_subset_1(X1,u1_struct_0(sK5))) => (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK5,sK6))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK5,sK6)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK5,sK6)))) & m1_subset_1(sK6,u1_struct_0(sK5)))),
% 2.16/0.69    introduced(choice_axiom,[])).
% 2.16/0.69  fof(f33,plain,(
% 2.16/0.69    ? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK5,sK6))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK5,sK6)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK5,sK6)))) => (? [X3] : (~m1_subset_1(k3_xboole_0(sK7,X3),u1_struct_0(k9_yellow_6(sK5,sK6))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK5,sK6)))) & m1_subset_1(sK7,u1_struct_0(k9_yellow_6(sK5,sK6))))),
% 2.16/0.69    introduced(choice_axiom,[])).
% 2.16/0.69  fof(f34,plain,(
% 2.16/0.69    ? [X3] : (~m1_subset_1(k3_xboole_0(sK7,X3),u1_struct_0(k9_yellow_6(sK5,sK6))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK5,sK6)))) => (~m1_subset_1(k3_xboole_0(sK7,sK8),u1_struct_0(k9_yellow_6(sK5,sK6))) & m1_subset_1(sK8,u1_struct_0(k9_yellow_6(sK5,sK6))))),
% 2.16/0.69    introduced(choice_axiom,[])).
% 2.16/0.69  fof(f13,plain,(
% 2.16/0.69    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.16/0.69    inference(flattening,[],[f12])).
% 2.16/0.69  fof(f12,plain,(
% 2.16/0.69    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.16/0.69    inference(ennf_transformation,[],[f11])).
% 2.16/0.69  fof(f11,negated_conjecture,(
% 2.16/0.69    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 2.16/0.69    inference(negated_conjecture,[],[f10])).
% 2.16/0.69  fof(f10,conjecture,(
% 2.16/0.69    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 2.16/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_waybel_9)).
% 2.16/0.69  fof(f227,plain,(
% 2.16/0.69    sP2(sK5,sK6,sK8) | v2_struct_0(sK5)),
% 2.16/0.69    inference(subsumption_resolution,[],[f226,f54])).
% 2.16/0.69  fof(f54,plain,(
% 2.16/0.69    v2_pre_topc(sK5)),
% 2.16/0.69    inference(cnf_transformation,[],[f35])).
% 2.16/0.69  fof(f226,plain,(
% 2.16/0.69    sP2(sK5,sK6,sK8) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)),
% 2.16/0.69    inference(subsumption_resolution,[],[f225,f55])).
% 2.16/0.69  fof(f55,plain,(
% 2.16/0.69    l1_pre_topc(sK5)),
% 2.16/0.69    inference(cnf_transformation,[],[f35])).
% 2.16/0.69  fof(f225,plain,(
% 2.16/0.69    sP2(sK5,sK6,sK8) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)),
% 2.16/0.69    inference(subsumption_resolution,[],[f219,f56])).
% 2.16/0.69  fof(f56,plain,(
% 2.16/0.69    m1_subset_1(sK6,u1_struct_0(sK5))),
% 2.16/0.69    inference(cnf_transformation,[],[f35])).
% 2.16/0.69  fof(f219,plain,(
% 2.16/0.69    sP2(sK5,sK6,sK8) | ~m1_subset_1(sK6,u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)),
% 2.16/0.69    inference(resolution,[],[f70,f58])).
% 2.16/0.69  fof(f58,plain,(
% 2.16/0.69    m1_subset_1(sK8,u1_struct_0(k9_yellow_6(sK5,sK6)))),
% 2.16/0.69    inference(cnf_transformation,[],[f35])).
% 2.16/0.69  fof(f70,plain,(
% 2.16/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | sP2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.16/0.69    inference(cnf_transformation,[],[f27])).
% 2.16/0.69  fof(f27,plain,(
% 2.16/0.69    ! [X0] : (! [X1] : (! [X2] : (sP2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.16/0.69    inference(definition_folding,[],[f17,f26])).
% 2.16/0.69  fof(f17,plain,(
% 2.16/0.69    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.16/0.69    inference(flattening,[],[f16])).
% 2.16/0.69  fof(f16,plain,(
% 2.16/0.69    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.16/0.69    inference(ennf_transformation,[],[f8])).
% 2.16/0.69  fof(f8,axiom,(
% 2.16/0.69    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 2.16/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_yellow_6)).
% 2.16/0.69  fof(f1947,plain,(
% 2.16/0.69    ~r1_tarski(sK8,u1_struct_0(sK5)) | spl11_17),
% 2.16/0.69    inference(resolution,[],[f1919,f75])).
% 2.16/0.69  fof(f75,plain,(
% 2.16/0.69    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.16/0.69    inference(cnf_transformation,[],[f44])).
% 2.16/0.69  fof(f1919,plain,(
% 2.16/0.69    ~m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5))) | spl11_17),
% 2.16/0.69    inference(avatar_component_clause,[],[f1917])).
% 2.16/0.69  fof(f1917,plain,(
% 2.16/0.69    spl11_17 <=> m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))),
% 2.16/0.69    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).
% 2.16/0.69  fof(f1925,plain,(
% 2.16/0.69    spl11_16),
% 2.16/0.69    inference(avatar_contradiction_clause,[],[f1924])).
% 2.16/0.69  fof(f1924,plain,(
% 2.16/0.69    $false | spl11_16),
% 2.16/0.69    inference(subsumption_resolution,[],[f1922,f233])).
% 2.16/0.69  fof(f233,plain,(
% 2.16/0.69    r1_tarski(sK7,u1_struct_0(sK5))),
% 2.16/0.69    inference(resolution,[],[f224,f148])).
% 2.16/0.69  fof(f224,plain,(
% 2.16/0.69    sP2(sK5,sK6,sK7)),
% 2.16/0.69    inference(subsumption_resolution,[],[f223,f53])).
% 2.16/0.69  fof(f223,plain,(
% 2.16/0.69    sP2(sK5,sK6,sK7) | v2_struct_0(sK5)),
% 2.16/0.69    inference(subsumption_resolution,[],[f222,f54])).
% 2.16/0.69  fof(f222,plain,(
% 2.16/0.69    sP2(sK5,sK6,sK7) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)),
% 2.16/0.69    inference(subsumption_resolution,[],[f221,f55])).
% 2.16/0.69  fof(f221,plain,(
% 2.16/0.69    sP2(sK5,sK6,sK7) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)),
% 2.16/0.69    inference(subsumption_resolution,[],[f218,f56])).
% 2.16/0.69  fof(f218,plain,(
% 2.16/0.69    sP2(sK5,sK6,sK7) | ~m1_subset_1(sK6,u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5)),
% 2.16/0.69    inference(resolution,[],[f70,f57])).
% 2.16/0.69  fof(f57,plain,(
% 2.16/0.69    m1_subset_1(sK7,u1_struct_0(k9_yellow_6(sK5,sK6)))),
% 2.16/0.69    inference(cnf_transformation,[],[f35])).
% 2.16/0.69  fof(f1922,plain,(
% 2.16/0.69    ~r1_tarski(sK7,u1_struct_0(sK5)) | spl11_16),
% 2.16/0.69    inference(resolution,[],[f1915,f75])).
% 2.16/0.69  fof(f1915,plain,(
% 2.16/0.69    ~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) | spl11_16),
% 2.16/0.69    inference(avatar_component_clause,[],[f1913])).
% 2.16/0.69  fof(f1913,plain,(
% 2.16/0.69    spl11_16 <=> m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))),
% 2.16/0.69    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).
% 2.16/0.69  fof(f1920,plain,(
% 2.16/0.69    ~spl11_16 | ~spl11_17 | spl11_15),
% 2.16/0.69    inference(avatar_split_clause,[],[f1911,f1871,f1917,f1913])).
% 2.16/0.69  fof(f1871,plain,(
% 2.16/0.69    spl11_15 <=> v3_pre_topc(k1_setfam_1(k2_tarski(sK7,sK8)),sK5)),
% 2.16/0.69    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).
% 2.16/0.69  fof(f1911,plain,(
% 2.16/0.69    ~m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5))) | ~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) | spl11_15),
% 2.16/0.69    inference(subsumption_resolution,[],[f1910,f54])).
% 2.16/0.69  fof(f1910,plain,(
% 2.16/0.69    ~m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5))) | ~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) | ~v2_pre_topc(sK5) | spl11_15),
% 2.16/0.69    inference(subsumption_resolution,[],[f1909,f55])).
% 2.16/0.69  fof(f1909,plain,(
% 2.16/0.69    ~m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5))) | ~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | spl11_15),
% 2.16/0.69    inference(subsumption_resolution,[],[f1908,f230])).
% 2.16/0.69  fof(f230,plain,(
% 2.16/0.69    v3_pre_topc(sK7,sK5)),
% 2.16/0.69    inference(resolution,[],[f224,f99])).
% 2.16/0.69  fof(f99,plain,(
% 2.16/0.69    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | v3_pre_topc(X2,X0)) )),
% 2.16/0.69    inference(duplicate_literal_removal,[],[f98])).
% 2.16/0.69  fof(f98,plain,(
% 2.16/0.69    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~sP2(X0,X1,X2) | ~sP2(X0,X1,X2)) )),
% 2.16/0.69    inference(superposition,[],[f69,f67])).
% 2.16/0.69  fof(f69,plain,(
% 2.16/0.69    ( ! [X2,X0,X1] : (v3_pre_topc(sK9(X0,X1,X2),X0) | ~sP2(X0,X1,X2)) )),
% 2.16/0.69    inference(cnf_transformation,[],[f43])).
% 2.16/0.69  fof(f1908,plain,(
% 2.16/0.69    ~m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5))) | ~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) | ~v3_pre_topc(sK7,sK5) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | spl11_15),
% 2.16/0.69    inference(subsumption_resolution,[],[f1905,f237])).
% 2.16/0.69  fof(f237,plain,(
% 2.16/0.69    v3_pre_topc(sK8,sK5)),
% 2.16/0.69    inference(resolution,[],[f228,f99])).
% 2.16/0.69  fof(f1905,plain,(
% 2.16/0.69    ~m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5))) | ~v3_pre_topc(sK8,sK5) | ~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) | ~v3_pre_topc(sK7,sK5) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | spl11_15),
% 2.16/0.69    inference(resolution,[],[f1873,f89])).
% 2.16/0.69  fof(f89,plain,(
% 2.16/0.69    ( ! [X2,X0,X1] : (v3_pre_topc(k1_setfam_1(k2_tarski(X1,X2)),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.16/0.69    inference(definition_unfolding,[],[f76,f72])).
% 2.16/0.69  fof(f72,plain,(
% 2.16/0.69    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.16/0.69    inference(cnf_transformation,[],[f4])).
% 2.16/0.69  fof(f4,axiom,(
% 2.16/0.69    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.16/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.16/0.69  fof(f76,plain,(
% 2.16/0.69    ( ! [X2,X0,X1] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.16/0.69    inference(cnf_transformation,[],[f20])).
% 2.16/0.69  fof(f20,plain,(
% 2.16/0.69    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.16/0.69    inference(flattening,[],[f19])).
% 2.16/0.69  fof(f19,plain,(
% 2.16/0.69    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.16/0.69    inference(ennf_transformation,[],[f7])).
% 2.16/0.69  fof(f7,axiom,(
% 2.16/0.69    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k3_xboole_0(X1,X2),X0))),
% 2.16/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_tops_1)).
% 2.16/0.69  fof(f1873,plain,(
% 2.16/0.69    ~v3_pre_topc(k1_setfam_1(k2_tarski(sK7,sK8)),sK5) | spl11_15),
% 2.16/0.69    inference(avatar_component_clause,[],[f1871])).
% 2.16/0.69  fof(f1881,plain,(
% 2.16/0.69    spl11_14),
% 2.16/0.69    inference(avatar_contradiction_clause,[],[f1880])).
% 2.16/0.69  fof(f1880,plain,(
% 2.16/0.69    $false | spl11_14),
% 2.16/0.69    inference(subsumption_resolution,[],[f1879,f229])).
% 2.16/0.69  fof(f229,plain,(
% 2.16/0.69    r2_hidden(sK6,sK7)),
% 2.16/0.69    inference(resolution,[],[f224,f97])).
% 2.16/0.69  fof(f97,plain,(
% 2.16/0.69    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | r2_hidden(X1,X2)) )),
% 2.16/0.69    inference(duplicate_literal_removal,[],[f96])).
% 2.16/0.69  fof(f96,plain,(
% 2.16/0.69    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~sP2(X0,X1,X2) | ~sP2(X0,X1,X2)) )),
% 2.16/0.69    inference(superposition,[],[f68,f67])).
% 2.16/0.69  fof(f68,plain,(
% 2.16/0.69    ( ! [X2,X0,X1] : (r2_hidden(X1,sK9(X0,X1,X2)) | ~sP2(X0,X1,X2)) )),
% 2.16/0.69    inference(cnf_transformation,[],[f43])).
% 2.16/0.69  fof(f1879,plain,(
% 2.16/0.69    ~r2_hidden(sK6,sK7) | spl11_14),
% 2.16/0.69    inference(subsumption_resolution,[],[f1878,f236])).
% 2.16/0.69  fof(f236,plain,(
% 2.16/0.69    r2_hidden(sK6,sK8)),
% 2.16/0.69    inference(resolution,[],[f228,f97])).
% 2.16/0.69  fof(f1878,plain,(
% 2.16/0.69    ~r2_hidden(sK6,sK8) | ~r2_hidden(sK6,sK7) | spl11_14),
% 2.16/0.69    inference(resolution,[],[f1875,f84])).
% 2.16/0.69  fof(f84,plain,(
% 2.16/0.69    ( ! [X2,X0,X1] : (sP3(X0,X1,X2) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) )),
% 2.16/0.69    inference(cnf_transformation,[],[f51])).
% 2.16/0.69  fof(f51,plain,(
% 2.16/0.69    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP3(X0,X1,X2)))),
% 2.16/0.69    inference(rectify,[],[f50])).
% 2.16/0.69  fof(f50,plain,(
% 2.16/0.69    ! [X1,X3,X0] : ((sP3(X1,X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP3(X1,X3,X0)))),
% 2.16/0.69    inference(flattening,[],[f49])).
% 2.16/0.69  fof(f49,plain,(
% 2.16/0.69    ! [X1,X3,X0] : ((sP3(X1,X3,X0) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP3(X1,X3,X0)))),
% 2.16/0.69    inference(nnf_transformation,[],[f28])).
% 2.16/0.69  fof(f28,plain,(
% 2.16/0.69    ! [X1,X3,X0] : (sP3(X1,X3,X0) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 2.16/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 2.16/0.69  fof(f1875,plain,(
% 2.16/0.69    ~sP3(sK8,sK6,sK7) | spl11_14),
% 2.16/0.69    inference(resolution,[],[f1869,f129])).
% 2.16/0.69  fof(f129,plain,(
% 2.16/0.69    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X0))) | ~sP3(X0,X1,X2)) )),
% 2.16/0.69    inference(resolution,[],[f79,f92])).
% 2.16/0.69  fof(f92,plain,(
% 2.16/0.69    ( ! [X0,X1] : (sP4(X0,X1,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.16/0.69    inference(equality_resolution,[],[f91])).
% 2.16/0.69  fof(f91,plain,(
% 2.16/0.69    ( ! [X2,X0,X1] : (sP4(X0,X1,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 2.16/0.69    inference(definition_unfolding,[],[f85,f72])).
% 2.16/0.69  fof(f85,plain,(
% 2.16/0.69    ( ! [X2,X0,X1] : (sP4(X0,X1,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.16/0.69    inference(cnf_transformation,[],[f52])).
% 2.16/0.69  fof(f52,plain,(
% 2.16/0.69    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP4(X0,X1,X2)) & (sP4(X0,X1,X2) | k3_xboole_0(X0,X1) != X2))),
% 2.16/0.69    inference(nnf_transformation,[],[f30])).
% 2.16/0.69  fof(f30,plain,(
% 2.16/0.69    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP4(X0,X1,X2))),
% 2.16/0.69    inference(definition_folding,[],[f1,f29,f28])).
% 2.16/0.69  fof(f29,plain,(
% 2.16/0.69    ! [X0,X1,X2] : (sP4(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP3(X1,X3,X0)))),
% 2.16/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 2.16/0.69  fof(f1,axiom,(
% 2.16/0.69    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.16/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.16/0.69  fof(f79,plain,(
% 2.16/0.69    ( ! [X4,X2,X0,X1] : (~sP4(X0,X1,X2) | ~sP3(X1,X4,X0) | r2_hidden(X4,X2)) )),
% 2.16/0.69    inference(cnf_transformation,[],[f48])).
% 2.16/0.69  fof(f48,plain,(
% 2.16/0.69    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ((~sP3(X1,sK10(X0,X1,X2),X0) | ~r2_hidden(sK10(X0,X1,X2),X2)) & (sP3(X1,sK10(X0,X1,X2),X0) | r2_hidden(sK10(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP3(X1,X4,X0)) & (sP3(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP4(X0,X1,X2)))),
% 2.16/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f46,f47])).
% 2.16/0.69  fof(f47,plain,(
% 2.16/0.69    ! [X2,X1,X0] : (? [X3] : ((~sP3(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP3(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP3(X1,sK10(X0,X1,X2),X0) | ~r2_hidden(sK10(X0,X1,X2),X2)) & (sP3(X1,sK10(X0,X1,X2),X0) | r2_hidden(sK10(X0,X1,X2),X2))))),
% 2.16/0.69    introduced(choice_axiom,[])).
% 2.16/0.69  fof(f46,plain,(
% 2.16/0.69    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ? [X3] : ((~sP3(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP3(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP3(X1,X4,X0)) & (sP3(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP4(X0,X1,X2)))),
% 2.16/0.69    inference(rectify,[],[f45])).
% 2.16/0.69  fof(f45,plain,(
% 2.16/0.69    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ? [X3] : ((~sP3(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP3(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP3(X1,X3,X0)) & (sP3(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP4(X0,X1,X2)))),
% 2.16/0.69    inference(nnf_transformation,[],[f29])).
% 2.16/0.69  fof(f1869,plain,(
% 2.16/0.69    ~r2_hidden(sK6,k1_setfam_1(k2_tarski(sK7,sK8))) | spl11_14),
% 2.16/0.69    inference(avatar_component_clause,[],[f1867])).
% 2.16/0.69  fof(f1867,plain,(
% 2.16/0.69    spl11_14 <=> r2_hidden(sK6,k1_setfam_1(k2_tarski(sK7,sK8)))),
% 2.16/0.69    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).
% 2.16/0.69  fof(f1874,plain,(
% 2.16/0.69    ~spl11_14 | ~spl11_15 | spl11_2),
% 2.16/0.69    inference(avatar_split_clause,[],[f1863,f178,f1871,f1867])).
% 2.16/0.69  fof(f178,plain,(
% 2.16/0.69    spl11_2 <=> sP0(sK5,k1_setfam_1(k2_tarski(sK7,sK8)),sK6)),
% 2.16/0.69    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 2.16/0.69  fof(f1863,plain,(
% 2.16/0.69    ~v3_pre_topc(k1_setfam_1(k2_tarski(sK7,sK8)),sK5) | ~r2_hidden(sK6,k1_setfam_1(k2_tarski(sK7,sK8))) | spl11_2),
% 2.16/0.69    inference(resolution,[],[f180,f64])).
% 2.16/0.69  fof(f64,plain,(
% 2.16/0.69    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | ~v3_pre_topc(X1,X0) | ~r2_hidden(X2,X1)) )),
% 2.16/0.69    inference(cnf_transformation,[],[f40])).
% 2.16/0.69  fof(f40,plain,(
% 2.16/0.69    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ~v3_pre_topc(X1,X0) | ~r2_hidden(X2,X1)) & ((v3_pre_topc(X1,X0) & r2_hidden(X2,X1)) | ~sP0(X0,X1,X2)))),
% 2.16/0.69    inference(rectify,[],[f39])).
% 2.16/0.69  fof(f39,plain,(
% 2.16/0.69    ! [X0,X2,X1] : ((sP0(X0,X2,X1) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2)) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~sP0(X0,X2,X1)))),
% 2.16/0.69    inference(flattening,[],[f38])).
% 2.16/0.69  fof(f38,plain,(
% 2.16/0.69    ! [X0,X2,X1] : ((sP0(X0,X2,X1) | (~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2))) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~sP0(X0,X2,X1)))),
% 2.16/0.69    inference(nnf_transformation,[],[f23])).
% 2.16/0.69  fof(f23,plain,(
% 2.16/0.69    ! [X0,X2,X1] : (sP0(X0,X2,X1) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2)))),
% 2.16/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.16/0.69  fof(f180,plain,(
% 2.16/0.69    ~sP0(sK5,k1_setfam_1(k2_tarski(sK7,sK8)),sK6) | spl11_2),
% 2.16/0.69    inference(avatar_component_clause,[],[f178])).
% 2.16/0.69  fof(f1849,plain,(
% 2.16/0.69    spl11_1),
% 2.16/0.69    inference(avatar_contradiction_clause,[],[f1842])).
% 2.16/0.69  fof(f1842,plain,(
% 2.16/0.69    $false | spl11_1),
% 2.16/0.69    inference(subsumption_resolution,[],[f309,f1833])).
% 2.16/0.69  fof(f1833,plain,(
% 2.16/0.69    ( ! [X10] : (r1_tarski(k1_setfam_1(k2_tarski(sK7,X10)),u1_struct_0(sK5))) )),
% 2.16/0.69    inference(resolution,[],[f1660,f115])).
% 2.16/0.69  fof(f115,plain,(
% 2.16/0.69    ( ! [X12,X10,X11] : (~sP4(X10,X11,X12) | r1_tarski(X12,X10)) )),
% 2.16/0.69    inference(superposition,[],[f88,f90])).
% 2.16/0.69  fof(f90,plain,(
% 2.16/0.69    ( ! [X2,X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X2 | ~sP4(X0,X1,X2)) )),
% 2.16/0.69    inference(definition_unfolding,[],[f86,f72])).
% 2.16/0.69  fof(f86,plain,(
% 2.16/0.69    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~sP4(X0,X1,X2)) )),
% 2.16/0.69    inference(cnf_transformation,[],[f52])).
% 2.16/0.69  fof(f88,plain,(
% 2.16/0.69    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 2.16/0.69    inference(definition_unfolding,[],[f71,f72])).
% 2.16/0.69  fof(f71,plain,(
% 2.16/0.69    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.16/0.69    inference(cnf_transformation,[],[f2])).
% 2.16/0.69  fof(f2,axiom,(
% 2.16/0.69    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.16/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.16/0.69  fof(f1660,plain,(
% 2.16/0.69    ( ! [X47] : (sP4(u1_struct_0(sK5),k1_setfam_1(k2_tarski(sK7,X47)),k1_setfam_1(k2_tarski(sK7,X47)))) )),
% 2.16/0.69    inference(duplicate_literal_removal,[],[f1635])).
% 2.16/0.69  fof(f1635,plain,(
% 2.16/0.69    ( ! [X47] : (sP4(u1_struct_0(sK5),k1_setfam_1(k2_tarski(sK7,X47)),k1_setfam_1(k2_tarski(sK7,X47))) | sP4(u1_struct_0(sK5),k1_setfam_1(k2_tarski(sK7,X47)),k1_setfam_1(k2_tarski(sK7,X47)))) )),
% 2.16/0.69    inference(resolution,[],[f265,f349])).
% 2.16/0.69  fof(f349,plain,(
% 2.16/0.69    ( ! [X11] : (~r2_hidden(sK10(u1_struct_0(sK5),X11,X11),sK7) | sP4(u1_struct_0(sK5),X11,X11)) )),
% 2.16/0.69    inference(resolution,[],[f340,f232])).
% 2.16/0.69  fof(f232,plain,(
% 2.16/0.69    ( ! [X1] : (r2_hidden(X1,u1_struct_0(sK5)) | ~r2_hidden(X1,sK7)) )),
% 2.16/0.69    inference(resolution,[],[f224,f147])).
% 2.16/0.69  fof(f147,plain,(
% 2.16/0.69    ( ! [X6,X4,X7,X5] : (~sP2(X4,X5,X6) | ~r2_hidden(X7,X6) | r2_hidden(X7,u1_struct_0(X4))) )),
% 2.16/0.69    inference(resolution,[],[f145,f73])).
% 2.16/0.69  fof(f73,plain,(
% 2.16/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 2.16/0.69    inference(cnf_transformation,[],[f18])).
% 2.16/0.69  fof(f18,plain,(
% 2.16/0.69    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.16/0.69    inference(ennf_transformation,[],[f3])).
% 2.16/0.69  fof(f3,axiom,(
% 2.16/0.69    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.16/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 2.16/0.69  fof(f340,plain,(
% 2.16/0.69    ( ! [X6,X7] : (~r2_hidden(sK10(X6,X7,X7),X6) | sP4(X6,X7,X7)) )),
% 2.16/0.69    inference(subsumption_resolution,[],[f337,f184])).
% 2.16/0.69  fof(f184,plain,(
% 2.16/0.69    ( ! [X2,X0,X1] : (r2_hidden(sK10(X0,X1,X2),X2) | sP4(X0,X1,X2) | r2_hidden(sK10(X0,X1,X2),X1)) )),
% 2.16/0.69    inference(resolution,[],[f80,f83])).
% 2.16/0.69  fof(f83,plain,(
% 2.16/0.69    ( ! [X2,X0,X1] : (~sP3(X0,X1,X2) | r2_hidden(X1,X0)) )),
% 2.16/0.69    inference(cnf_transformation,[],[f51])).
% 2.16/0.69  fof(f80,plain,(
% 2.16/0.69    ( ! [X2,X0,X1] : (sP3(X1,sK10(X0,X1,X2),X0) | sP4(X0,X1,X2) | r2_hidden(sK10(X0,X1,X2),X2)) )),
% 2.16/0.69    inference(cnf_transformation,[],[f48])).
% 2.16/0.69  fof(f337,plain,(
% 2.16/0.69    ( ! [X6,X7] : (sP4(X6,X7,X7) | ~r2_hidden(sK10(X6,X7,X7),X7) | ~r2_hidden(sK10(X6,X7,X7),X6)) )),
% 2.16/0.69    inference(duplicate_literal_removal,[],[f330])).
% 2.16/0.69  fof(f330,plain,(
% 2.16/0.69    ( ! [X6,X7] : (sP4(X6,X7,X7) | ~r2_hidden(sK10(X6,X7,X7),X7) | ~r2_hidden(sK10(X6,X7,X7),X6) | sP4(X6,X7,X7)) )),
% 2.16/0.69    inference(resolution,[],[f194,f260])).
% 2.16/0.69  fof(f260,plain,(
% 2.16/0.69    ( ! [X0,X1] : (r2_hidden(sK10(X0,X1,X1),X1) | sP4(X0,X1,X1)) )),
% 2.16/0.69    inference(factoring,[],[f184])).
% 2.16/0.69  fof(f194,plain,(
% 2.16/0.69    ( ! [X4,X5,X3] : (~r2_hidden(sK10(X3,X4,X5),X5) | sP4(X3,X4,X5) | ~r2_hidden(sK10(X3,X4,X5),X4) | ~r2_hidden(sK10(X3,X4,X5),X3)) )),
% 2.16/0.69    inference(resolution,[],[f81,f84])).
% 2.16/0.69  fof(f81,plain,(
% 2.16/0.69    ( ! [X2,X0,X1] : (~sP3(X1,sK10(X0,X1,X2),X0) | sP4(X0,X1,X2) | ~r2_hidden(sK10(X0,X1,X2),X2)) )),
% 2.16/0.69    inference(cnf_transformation,[],[f48])).
% 2.16/0.69  fof(f265,plain,(
% 2.16/0.69    ( ! [X12,X13,X11] : (r2_hidden(sK10(X11,k1_setfam_1(k2_tarski(X12,X13)),k1_setfam_1(k2_tarski(X12,X13))),X12) | sP4(X11,k1_setfam_1(k2_tarski(X12,X13)),k1_setfam_1(k2_tarski(X12,X13)))) )),
% 2.16/0.69    inference(resolution,[],[f260,f102])).
% 2.16/0.69  fof(f102,plain,(
% 2.16/0.69    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) | r2_hidden(X0,X1)) )),
% 2.16/0.69    inference(resolution,[],[f100,f88])).
% 2.16/0.69  fof(f100,plain,(
% 2.16/0.69    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 2.16/0.69    inference(resolution,[],[f73,f75])).
% 2.16/0.69  fof(f309,plain,(
% 2.16/0.69    ~r1_tarski(k1_setfam_1(k2_tarski(sK7,sK8)),u1_struct_0(sK5)) | spl11_1),
% 2.16/0.69    inference(subsumption_resolution,[],[f308,f53])).
% 2.16/0.69  fof(f308,plain,(
% 2.16/0.69    v2_struct_0(sK5) | ~r1_tarski(k1_setfam_1(k2_tarski(sK7,sK8)),u1_struct_0(sK5)) | spl11_1),
% 2.16/0.69    inference(subsumption_resolution,[],[f307,f54])).
% 2.16/0.69  fof(f307,plain,(
% 2.16/0.69    ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~r1_tarski(k1_setfam_1(k2_tarski(sK7,sK8)),u1_struct_0(sK5)) | spl11_1),
% 2.16/0.69    inference(subsumption_resolution,[],[f306,f55])).
% 2.16/0.69  fof(f306,plain,(
% 2.16/0.69    ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~r1_tarski(k1_setfam_1(k2_tarski(sK7,sK8)),u1_struct_0(sK5)) | spl11_1),
% 2.16/0.69    inference(subsumption_resolution,[],[f305,f56])).
% 2.16/0.69  fof(f305,plain,(
% 2.16/0.69    ~m1_subset_1(sK6,u1_struct_0(sK5)) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~r1_tarski(k1_setfam_1(k2_tarski(sK7,sK8)),u1_struct_0(sK5)) | spl11_1),
% 2.16/0.69    inference(resolution,[],[f209,f176])).
% 2.16/0.69  fof(f176,plain,(
% 2.16/0.69    ~sP1(sK6,k1_setfam_1(k2_tarski(sK7,sK8)),sK5) | spl11_1),
% 2.16/0.69    inference(avatar_component_clause,[],[f174])).
% 2.16/0.69  fof(f174,plain,(
% 2.16/0.69    spl11_1 <=> sP1(sK6,k1_setfam_1(k2_tarski(sK7,sK8)),sK5)),
% 2.16/0.69    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 2.16/0.69  fof(f209,plain,(
% 2.16/0.69    ( ! [X6,X4,X5] : (sP1(X4,X5,X6) | ~m1_subset_1(X4,u1_struct_0(X6)) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | ~r1_tarski(X5,u1_struct_0(X6))) )),
% 2.16/0.69    inference(resolution,[],[f65,f75])).
% 2.16/0.69  fof(f65,plain,(
% 2.16/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X1,X2,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.16/0.69    inference(cnf_transformation,[],[f25])).
% 2.16/0.69  fof(f25,plain,(
% 2.16/0.69    ! [X0] : (! [X1] : (! [X2] : (sP1(X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.16/0.69    inference(definition_folding,[],[f15,f24,f23])).
% 2.16/0.69  fof(f24,plain,(
% 2.16/0.69    ! [X1,X2,X0] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> sP0(X0,X2,X1)) | ~sP1(X1,X2,X0))),
% 2.16/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.16/0.69  fof(f15,plain,(
% 2.16/0.69    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.16/0.69    inference(flattening,[],[f14])).
% 2.16/0.69  fof(f14,plain,(
% 2.16/0.69    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.16/0.69    inference(ennf_transformation,[],[f9])).
% 2.16/0.69  fof(f9,axiom,(
% 2.16/0.69    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 2.16/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_yellow_6)).
% 2.16/0.69  fof(f181,plain,(
% 2.16/0.69    ~spl11_1 | ~spl11_2),
% 2.16/0.69    inference(avatar_split_clause,[],[f169,f178,f174])).
% 2.16/0.69  fof(f169,plain,(
% 2.16/0.69    ~sP0(sK5,k1_setfam_1(k2_tarski(sK7,sK8)),sK6) | ~sP1(sK6,k1_setfam_1(k2_tarski(sK7,sK8)),sK5)),
% 2.16/0.69    inference(resolution,[],[f61,f137])).
% 2.16/0.69  fof(f137,plain,(
% 2.16/0.69    ~r2_hidden(k1_setfam_1(k2_tarski(sK7,sK8)),u1_struct_0(k9_yellow_6(sK5,sK6)))),
% 2.16/0.69    inference(condensation,[],[f135])).
% 2.16/0.69  fof(f135,plain,(
% 2.16/0.69    ( ! [X0] : (~r2_hidden(k1_setfam_1(k2_tarski(sK7,sK8)),X0) | ~r2_hidden(k1_setfam_1(k2_tarski(sK7,sK8)),u1_struct_0(k9_yellow_6(sK5,sK6)))) )),
% 2.16/0.69    inference(resolution,[],[f130,f84])).
% 2.16/0.69  fof(f130,plain,(
% 2.16/0.69    ( ! [X0] : (~sP3(X0,k1_setfam_1(k2_tarski(sK7,sK8)),u1_struct_0(k9_yellow_6(sK5,sK6)))) )),
% 2.16/0.69    inference(resolution,[],[f129,f107])).
% 2.16/0.69  fof(f107,plain,(
% 2.16/0.69    ( ! [X0] : (~r2_hidden(k1_setfam_1(k2_tarski(sK7,sK8)),k1_setfam_1(k2_tarski(u1_struct_0(k9_yellow_6(sK5,sK6)),X0)))) )),
% 2.16/0.69    inference(resolution,[],[f103,f88])).
% 2.16/0.69  fof(f103,plain,(
% 2.16/0.69    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(k9_yellow_6(sK5,sK6))) | ~r2_hidden(k1_setfam_1(k2_tarski(sK7,sK8)),X0)) )),
% 2.16/0.69    inference(resolution,[],[f101,f87])).
% 2.16/0.69  fof(f87,plain,(
% 2.16/0.69    ~m1_subset_1(k1_setfam_1(k2_tarski(sK7,sK8)),u1_struct_0(k9_yellow_6(sK5,sK6)))),
% 2.16/0.69    inference(definition_unfolding,[],[f59,f72])).
% 2.16/0.69  fof(f59,plain,(
% 2.16/0.69    ~m1_subset_1(k3_xboole_0(sK7,sK8),u1_struct_0(k9_yellow_6(sK5,sK6)))),
% 2.16/0.69    inference(cnf_transformation,[],[f35])).
% 2.16/0.69  fof(f101,plain,(
% 2.16/0.69    ( ! [X2,X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X2) | ~r1_tarski(X2,X1)) )),
% 2.16/0.69    inference(resolution,[],[f77,f75])).
% 2.16/0.69  fof(f77,plain,(
% 2.16/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 2.16/0.69    inference(cnf_transformation,[],[f22])).
% 2.16/0.69  fof(f22,plain,(
% 2.16/0.69    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.16/0.69    inference(flattening,[],[f21])).
% 2.16/0.69  fof(f21,plain,(
% 2.16/0.69    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.16/0.69    inference(ennf_transformation,[],[f6])).
% 2.16/0.69  fof(f6,axiom,(
% 2.16/0.69    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.16/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 2.16/0.69  fof(f61,plain,(
% 2.16/0.69    ( ! [X2,X0,X1] : (r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X0))) | ~sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 2.16/0.69    inference(cnf_transformation,[],[f37])).
% 2.16/0.69  fof(f37,plain,(
% 2.16/0.69    ! [X0,X1,X2] : (((r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X0))) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X0))))) | ~sP1(X0,X1,X2))),
% 2.16/0.69    inference(rectify,[],[f36])).
% 2.16/0.69  fof(f36,plain,(
% 2.16/0.69    ! [X1,X2,X0] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~sP0(X0,X2,X1)) & (sP0(X0,X2,X1) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~sP1(X1,X2,X0))),
% 2.16/0.69    inference(nnf_transformation,[],[f24])).
% 2.16/0.69  % SZS output end Proof for theBenchmark
% 2.16/0.69  % (24892)------------------------------
% 2.16/0.69  % (24892)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.69  % (24892)Termination reason: Refutation
% 2.16/0.69  
% 2.16/0.69  % (24892)Memory used [KB]: 7291
% 2.16/0.69  % (24892)Time elapsed: 0.293 s
% 2.16/0.69  % (24892)------------------------------
% 2.16/0.69  % (24892)------------------------------
% 2.16/0.69  % (24864)Success in time 0.333 s
%------------------------------------------------------------------------------
