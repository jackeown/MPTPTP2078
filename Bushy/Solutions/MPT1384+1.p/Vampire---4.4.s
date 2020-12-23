%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : connsp_2__t9_connsp_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:55 EDT 2019

% Result     : Theorem 38.05s
% Output     : Refutation 38.05s
% Verified   : 
% Statistics : Number of formulae       :  244 ( 941 expanded)
%              Number of leaves         :   34 ( 214 expanded)
%              Depth                    :   23
%              Number of atoms          : 1110 (5906 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14996,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f257,f291,f295,f307,f354,f930,f940,f1901,f6436,f6443,f6469,f6657,f6695,f6699,f8074,f8075,f8961,f9274,f14995])).

fof(f14995,plain,
    ( ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_14
    | ~ spl14_34
    | ~ spl14_114 ),
    inference(avatar_contradiction_clause,[],[f14994])).

fof(f14994,plain,
    ( $false
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_14
    | ~ spl14_34
    | ~ spl14_114 ),
    inference(subsumption_resolution,[],[f14993,f247])).

fof(f247,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl14_0 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl14_0
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_0])])).

fof(f14993,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_14
    | ~ spl14_34
    | ~ spl14_114 ),
    inference(subsumption_resolution,[],[f14992,f256])).

fof(f256,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl14_2 ),
    inference(avatar_component_clause,[],[f255])).

fof(f255,plain,
    ( spl14_2
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f14992,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_14
    | ~ spl14_34
    | ~ spl14_114 ),
    inference(subsumption_resolution,[],[f14991,f59])).

fof(f59,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ ( ! [X3] :
                          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( r1_tarski(X3,X1)
                              & m1_connsp_2(X3,X0,X2) ) )
                      & r2_hidden(X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( r1_tarski(X3,X1)
                            & m1_connsp_2(X3,X0,X2) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t9_connsp_2.p',t9_connsp_2)).

fof(f14991,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_14
    | ~ spl14_34
    | ~ spl14_114 ),
    inference(subsumption_resolution,[],[f14990,f62])).

fof(f62,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f14990,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_14
    | ~ spl14_34
    | ~ spl14_114 ),
    inference(subsumption_resolution,[],[f14966,f61])).

fof(f61,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f14966,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_14
    | ~ spl14_34
    | ~ spl14_114 ),
    inference(resolution,[],[f14432,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(sK6(X0,X1,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,X1)
              <=> ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r1_tarski(X3,X1)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,X1)
              <=> ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r1_tarski(X3,X1)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,X1)
              <=> ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r1_tarski(X3,X1)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t9_connsp_2.p',t57_tops_1)).

fof(f14432,plain,
    ( ~ r1_tarski(sK6(sK0,sK1,sK2),sK1)
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_14
    | ~ spl14_34
    | ~ spl14_114 ),
    inference(resolution,[],[f14334,f6702])).

fof(f6702,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK0,sK2)
        | ~ r1_tarski(X0,sK1) )
    | ~ spl14_4
    | ~ spl14_14 ),
    inference(duplicate_literal_removal,[],[f729])).

fof(f729,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK0,sK2)
        | ~ r1_tarski(X0,sK1)
        | ~ m1_connsp_2(X0,sK0,sK2) )
    | ~ spl14_4
    | ~ spl14_14 ),
    inference(resolution,[],[f435,f353])).

fof(f353,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1)
        | ~ m1_connsp_2(X3,sK0,sK2) )
    | ~ spl14_14 ),
    inference(avatar_component_clause,[],[f352])).

fof(f352,plain,
    ( spl14_14
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1)
        | ~ m1_connsp_2(X3,sK0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_14])])).

fof(f435,plain,
    ( ! [X7] :
        ( m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_connsp_2(X7,sK0,sK2) )
    | ~ spl14_4 ),
    inference(subsumption_resolution,[],[f434,f62])).

fof(f434,plain,
    ( ! [X7] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_connsp_2(X7,sK0,sK2)
        | m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl14_4 ),
    inference(subsumption_resolution,[],[f433,f61])).

fof(f433,plain,
    ( ! [X7] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_connsp_2(X7,sK0,sK2)
        | m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl14_4 ),
    inference(subsumption_resolution,[],[f418,f60])).

fof(f60,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f418,plain,
    ( ! [X7] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_connsp_2(X7,sK0,sK2)
        | m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl14_4 ),
    inference(resolution,[],[f290,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t9_connsp_2.p',dt_m1_connsp_2)).

fof(f290,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl14_4 ),
    inference(avatar_component_clause,[],[f289])).

fof(f289,plain,
    ( spl14_4
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).

fof(f14334,plain,
    ( m1_connsp_2(sK6(sK0,sK1,sK2),sK0,sK2)
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_34
    | ~ spl14_114 ),
    inference(subsumption_resolution,[],[f14333,f247])).

fof(f14333,plain,
    ( m1_connsp_2(sK6(sK0,sK1,sK2),sK0,sK2)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_34
    | ~ spl14_114 ),
    inference(subsumption_resolution,[],[f14332,f59])).

fof(f14332,plain,
    ( m1_connsp_2(sK6(sK0,sK1,sK2),sK0,sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_34
    | ~ spl14_114 ),
    inference(subsumption_resolution,[],[f14331,f9138])).

fof(f9138,plain,
    ( v3_pre_topc(sK6(sK0,sK1,sK2),sK0)
    | ~ spl14_114 ),
    inference(avatar_component_clause,[],[f9137])).

fof(f9137,plain,
    ( spl14_114
  <=> v3_pre_topc(sK6(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_114])])).

fof(f14331,plain,
    ( ~ v3_pre_topc(sK6(sK0,sK1,sK2),sK0)
    | m1_connsp_2(sK6(sK0,sK1,sK2),sK0,sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_34 ),
    inference(subsumption_resolution,[],[f14330,f290])).

fof(f14330,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v3_pre_topc(sK6(sK0,sK1,sK2),sK0)
    | m1_connsp_2(sK6(sK0,sK1,sK2),sK0,sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl14_2
    | ~ spl14_34 ),
    inference(subsumption_resolution,[],[f14329,f256])).

fof(f14329,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v3_pre_topc(sK6(sK0,sK1,sK2),sK0)
    | m1_connsp_2(sK6(sK0,sK1,sK2),sK0,sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl14_2
    | ~ spl14_34 ),
    inference(subsumption_resolution,[],[f14328,f62])).

fof(f14328,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ r2_hidden(sK2,sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v3_pre_topc(sK6(sK0,sK1,sK2),sK0)
    | m1_connsp_2(sK6(sK0,sK1,sK2),sK0,sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl14_2
    | ~ spl14_34 ),
    inference(subsumption_resolution,[],[f14327,f61])).

fof(f14327,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ r2_hidden(sK2,sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v3_pre_topc(sK6(sK0,sK1,sK2),sK0)
    | m1_connsp_2(sK6(sK0,sK1,sK2),sK0,sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl14_2
    | ~ spl14_34 ),
    inference(subsumption_resolution,[],[f14326,f60])).

fof(f14326,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ r2_hidden(sK2,sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v3_pre_topc(sK6(sK0,sK1,sK2),sK0)
    | m1_connsp_2(sK6(sK0,sK1,sK2),sK0,sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl14_2
    | ~ spl14_34 ),
    inference(duplicate_literal_removal,[],[f14311])).

fof(f14311,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ r2_hidden(sK2,sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v3_pre_topc(sK6(sK0,sK1,sK2),sK0)
    | m1_connsp_2(sK6(sK0,sK1,sK2),sK0,sK2)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl14_2
    | ~ spl14_34 ),
    inference(resolution,[],[f6987,f6751])).

fof(f6751,plain,
    ( ! [X3] :
        ( m1_subset_1(sK6(X3,sK1,sK2),k1_zfmisc_1(u1_struct_0(X3)))
        | ~ l1_pre_topc(X3)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ v2_pre_topc(X3)
        | ~ v3_pre_topc(sK1,X3) )
    | ~ spl14_2 ),
    inference(resolution,[],[f256,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6987,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(sK6(sK0,sK1,X4),k1_zfmisc_1(u1_struct_0(X5)))
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | ~ r2_hidden(X4,sK1)
        | ~ m1_subset_1(X4,u1_struct_0(X5))
        | ~ v3_pre_topc(sK6(sK0,sK1,X4),X5)
        | m1_connsp_2(sK6(sK0,sK1,X4),X5,X4) )
    | ~ spl14_34 ),
    inference(resolution,[],[f939,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ r2_hidden(X2,X1)
      | m1_connsp_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t9_connsp_2.p',t5_connsp_2)).

fof(f939,plain,
    ( ! [X14] :
        ( r2_hidden(X14,sK6(sK0,sK1,X14))
        | ~ r2_hidden(X14,sK1) )
    | ~ spl14_34 ),
    inference(avatar_component_clause,[],[f938])).

fof(f938,plain,
    ( spl14_34
  <=> ! [X14] :
        ( r2_hidden(X14,sK6(sK0,sK1,X14))
        | ~ r2_hidden(X14,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_34])])).

fof(f9274,plain,
    ( ~ spl14_2
    | ~ spl14_30
    | spl14_115 ),
    inference(avatar_contradiction_clause,[],[f9273])).

fof(f9273,plain,
    ( $false
    | ~ spl14_2
    | ~ spl14_30
    | ~ spl14_115 ),
    inference(subsumption_resolution,[],[f9252,f256])).

fof(f9252,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl14_30
    | ~ spl14_115 ),
    inference(resolution,[],[f9141,f929])).

fof(f929,plain,
    ( ! [X12] :
        ( v3_pre_topc(sK6(sK0,sK1,X12),sK0)
        | ~ r2_hidden(X12,sK1) )
    | ~ spl14_30 ),
    inference(avatar_component_clause,[],[f928])).

fof(f928,plain,
    ( spl14_30
  <=> ! [X12] :
        ( v3_pre_topc(sK6(sK0,sK1,X12),sK0)
        | ~ r2_hidden(X12,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_30])])).

fof(f9141,plain,
    ( ~ v3_pre_topc(sK6(sK0,sK1,sK2),sK0)
    | ~ spl14_115 ),
    inference(avatar_component_clause,[],[f9140])).

fof(f9140,plain,
    ( spl14_115
  <=> ~ v3_pre_topc(sK6(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_115])])).

fof(f8961,plain,
    ( ~ spl14_91
    | spl14_0
    | spl14_37 ),
    inference(avatar_split_clause,[],[f6704,f991,f246,f8069])).

fof(f8069,plain,
    ( spl14_91
  <=> ~ sP12(sK7(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_91])])).

fof(f991,plain,
    ( spl14_37
  <=> ~ r2_hidden(sK5(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_37])])).

fof(f6704,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ sP12(sK7(sK0,sK1))
    | ~ spl14_37 ),
    inference(subsumption_resolution,[],[f3455,f992])).

fof(f992,plain,
    ( ~ r2_hidden(sK5(sK0,sK1),sK1)
    | ~ spl14_37 ),
    inference(avatar_component_clause,[],[f991])).

fof(f3455,plain,
    ( r2_hidden(sK5(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ sP12(sK7(sK0,sK1)) ),
    inference(resolution,[],[f1701,f59])).

fof(f1701,plain,(
    ! [X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK5(sK0,X22),X22)
      | v3_pre_topc(X22,sK0)
      | ~ sP12(sK7(sK0,X22)) ) ),
    inference(resolution,[],[f152,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP12(X1) ) ),
    inference(general_splitting,[],[f92,f96_D])).

fof(f96,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP12(X1) ) ),
    inference(cnf_transformation,[],[f96_D])).

fof(f96_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP12(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP12])])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t9_connsp_2.p',t5_subset)).

fof(f152,plain,(
    ! [X18] :
      ( r2_hidden(sK5(sK0,X18),sK7(sK0,X18))
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK5(sK0,X18),X18)
      | v3_pre_topc(X18,sK0) ) ),
    inference(subsumption_resolution,[],[f140,f62])).

fof(f140,plain,(
    ! [X18] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK5(sK0,X18),sK7(sK0,X18))
      | r2_hidden(sK5(sK0,X18),X18)
      | v3_pre_topc(X18,sK0) ) ),
    inference(resolution,[],[f61,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK5(X0,X1),sK7(X0,X1))
      | r2_hidden(sK5(X0,X1),X1)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f8075,plain,
    ( spl14_0
    | spl14_48
    | spl14_37 ),
    inference(avatar_split_clause,[],[f6733,f991,f1145,f246])).

fof(f1145,plain,
    ( spl14_48
  <=> r2_hidden(sK5(sK0,sK1),sK7(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_48])])).

fof(f6733,plain,
    ( r2_hidden(sK5(sK0,sK1),sK7(sK0,sK1))
    | v3_pre_topc(sK1,sK0)
    | ~ spl14_37 ),
    inference(subsumption_resolution,[],[f6732,f59])).

fof(f6732,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK5(sK0,sK1),sK7(sK0,sK1))
    | v3_pre_topc(sK1,sK0)
    | ~ spl14_37 ),
    inference(subsumption_resolution,[],[f6731,f62])).

fof(f6731,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK5(sK0,sK1),sK7(sK0,sK1))
    | v3_pre_topc(sK1,sK0)
    | ~ spl14_37 ),
    inference(subsumption_resolution,[],[f6522,f61])).

fof(f6522,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK5(sK0,sK1),sK7(sK0,sK1))
    | v3_pre_topc(sK1,sK0)
    | ~ spl14_37 ),
    inference(resolution,[],[f992,f74])).

fof(f8074,plain,
    ( spl14_90
    | ~ spl14_79
    | ~ spl14_40 ),
    inference(avatar_split_clause,[],[f6678,f1027,f6630,f8072])).

fof(f8072,plain,
    ( spl14_90
  <=> sP12(sK7(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_90])])).

fof(f6630,plain,
    ( spl14_79
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_79])])).

fof(f1027,plain,
    ( spl14_40
  <=> r1_tarski(sK7(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_40])])).

fof(f6678,plain,
    ( ~ v1_xboole_0(sK1)
    | sP12(sK7(sK0,sK1))
    | ~ spl14_40 ),
    inference(resolution,[],[f6566,f96])).

fof(f6566,plain,
    ( m1_subset_1(sK7(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl14_40 ),
    inference(resolution,[],[f1028,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t9_connsp_2.p',t3_subset)).

fof(f1028,plain,
    ( r1_tarski(sK7(sK0,sK1),sK1)
    | ~ spl14_40 ),
    inference(avatar_component_clause,[],[f1027])).

fof(f6699,plain,
    ( ~ spl14_40
    | ~ spl14_48
    | spl14_87 ),
    inference(avatar_contradiction_clause,[],[f6696])).

fof(f6696,plain,
    ( $false
    | ~ spl14_40
    | ~ spl14_48
    | ~ spl14_87 ),
    inference(unit_resulting_resolution,[],[f6566,f1146,f6694,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t9_connsp_2.p',t4_subset)).

fof(f6694,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1),sK1)
    | ~ spl14_87 ),
    inference(avatar_component_clause,[],[f6693])).

fof(f6693,plain,
    ( spl14_87
  <=> ~ m1_subset_1(sK5(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_87])])).

fof(f1146,plain,
    ( r2_hidden(sK5(sK0,sK1),sK7(sK0,sK1))
    | ~ spl14_48 ),
    inference(avatar_component_clause,[],[f1145])).

fof(f6695,plain,
    ( spl14_78
    | ~ spl14_87
    | spl14_37 ),
    inference(avatar_split_clause,[],[f6523,f991,f6693,f6633])).

fof(f6633,plain,
    ( spl14_78
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_78])])).

fof(f6523,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1),sK1)
    | v1_xboole_0(sK1)
    | ~ spl14_37 ),
    inference(resolution,[],[f992,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t9_connsp_2.p',t2_subset)).

fof(f6657,plain,
    ( spl14_36
    | spl14_40
    | spl14_1 ),
    inference(avatar_split_clause,[],[f6480,f249,f1027,f994])).

fof(f994,plain,
    ( spl14_36
  <=> r2_hidden(sK5(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_36])])).

fof(f249,plain,
    ( spl14_1
  <=> ~ v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f6480,plain,
    ( r1_tarski(sK7(sK0,sK1),sK1)
    | r2_hidden(sK5(sK0,sK1),sK1)
    | ~ spl14_1 ),
    inference(subsumption_resolution,[],[f6479,f59])).

fof(f6479,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK7(sK0,sK1),sK1)
    | r2_hidden(sK5(sK0,sK1),sK1)
    | ~ spl14_1 ),
    inference(subsumption_resolution,[],[f6478,f62])).

fof(f6478,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK7(sK0,sK1),sK1)
    | r2_hidden(sK5(sK0,sK1),sK1)
    | ~ spl14_1 ),
    inference(subsumption_resolution,[],[f6369,f61])).

fof(f6369,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK7(sK0,sK1),sK1)
    | r2_hidden(sK5(sK0,sK1),sK1)
    | ~ spl14_1 ),
    inference(resolution,[],[f250,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(sK7(X0,X1),X1)
      | r2_hidden(sK5(X0,X1),X1)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f250,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl14_1 ),
    inference(avatar_component_clause,[],[f249])).

fof(f6469,plain,
    ( ~ spl14_36
    | spl14_77 ),
    inference(avatar_contradiction_clause,[],[f6468])).

fof(f6468,plain,
    ( $false
    | ~ spl14_36
    | ~ spl14_77 ),
    inference(subsumption_resolution,[],[f6460,f59])).

fof(f6460,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl14_36
    | ~ spl14_77 ),
    inference(resolution,[],[f6435,f1015])).

fof(f1015,plain,
    ( ! [X8] :
        ( m1_subset_1(sK5(sK0,sK1),X8)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X8)) )
    | ~ spl14_36 ),
    inference(resolution,[],[f995,f91])).

fof(f995,plain,
    ( r2_hidden(sK5(sK0,sK1),sK1)
    | ~ spl14_36 ),
    inference(avatar_component_clause,[],[f994])).

fof(f6435,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ spl14_77 ),
    inference(avatar_component_clause,[],[f6434])).

fof(f6434,plain,
    ( spl14_77
  <=> ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_77])])).

fof(f6443,plain,
    ( ~ spl14_6
    | ~ spl14_8
    | ~ spl14_36
    | spl14_75 ),
    inference(avatar_contradiction_clause,[],[f6442])).

fof(f6442,plain,
    ( $false
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_36
    | ~ spl14_75 ),
    inference(subsumption_resolution,[],[f6438,f995])).

fof(f6438,plain,
    ( ~ r2_hidden(sK5(sK0,sK1),sK1)
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_75 ),
    inference(resolution,[],[f6429,f2963])).

fof(f2963,plain,
    ( ! [X0] :
        ( m1_connsp_2(sK1,sK0,X0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl14_6
    | ~ spl14_8 ),
    inference(duplicate_literal_removal,[],[f2952])).

fof(f2952,plain,
    ( ! [X0] :
        ( m1_connsp_2(sK1,sK0,X0)
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl14_6
    | ~ spl14_8 ),
    inference(resolution,[],[f1463,f350])).

fof(f350,plain,
    ( ! [X4] :
        ( r2_hidden(X4,sK4(sK0,X4,sK3(X4)))
        | ~ r2_hidden(X4,sK1) )
    | ~ spl14_8 ),
    inference(subsumption_resolution,[],[f349,f330])).

fof(f330,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl14_8 ),
    inference(subsumption_resolution,[],[f329,f195])).

fof(f195,plain,(
    ! [X17] :
      ( m1_subset_1(X17,u1_struct_0(sK0))
      | ~ r2_hidden(X17,sK1) ) ),
    inference(resolution,[],[f59,f91])).

fof(f329,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl14_8 ),
    inference(subsumption_resolution,[],[f328,f62])).

fof(f328,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl14_8 ),
    inference(subsumption_resolution,[],[f327,f61])).

fof(f327,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl14_8 ),
    inference(subsumption_resolution,[],[f322,f60])).

fof(f322,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl14_8 ),
    inference(resolution,[],[f308,f84])).

fof(f308,plain,
    ( ! [X2] :
        ( m1_connsp_2(sK3(X2),sK0,X2)
        | ~ r2_hidden(X2,sK1) )
    | ~ spl14_8 ),
    inference(subsumption_resolution,[],[f306,f195])).

fof(f306,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | m1_connsp_2(sK3(X2),sK0,X2)
        | ~ r2_hidden(X2,sK1) )
    | ~ spl14_8 ),
    inference(avatar_component_clause,[],[f305])).

fof(f305,plain,
    ( spl14_8
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | m1_connsp_2(sK3(X2),sK0,X2)
        | ~ r2_hidden(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_8])])).

fof(f349,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK1)
        | ~ m1_subset_1(sK3(X4),k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X4,sK4(sK0,X4,sK3(X4))) )
    | ~ spl14_8 ),
    inference(subsumption_resolution,[],[f348,f195])).

fof(f348,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(X4),k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X4,sK4(sK0,X4,sK3(X4))) )
    | ~ spl14_8 ),
    inference(subsumption_resolution,[],[f347,f62])).

fof(f347,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK1)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(X4),k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X4,sK4(sK0,X4,sK3(X4))) )
    | ~ spl14_8 ),
    inference(subsumption_resolution,[],[f346,f61])).

fof(f346,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK1)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(X4),k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X4,sK4(sK0,X4,sK3(X4))) )
    | ~ spl14_8 ),
    inference(subsumption_resolution,[],[f326,f60])).

fof(f326,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK1)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(X4),k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X4,sK4(sK0,X4,sK3(X4))) )
    | ~ spl14_8 ),
    inference(resolution,[],[f308,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,sK4(X0,X1,X2))
      | ~ m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t9_connsp_2.p',t8_connsp_2)).

fof(f1463,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X6,sK4(sK0,X5,sK3(X5)))
        | m1_connsp_2(sK1,sK0,X6)
        | ~ r2_hidden(X5,sK1) )
    | ~ spl14_6
    | ~ spl14_8 ),
    inference(subsumption_resolution,[],[f1462,f925])).

fof(f925,plain,
    ( ! [X0] :
        ( r1_tarski(sK4(sK0,X0,sK3(X0)),sK1)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl14_6
    | ~ spl14_8 ),
    inference(duplicate_literal_removal,[],[f918])).

fof(f918,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK1)
        | r1_tarski(sK4(sK0,X0,sK3(X0)),sK1) )
    | ~ spl14_6
    | ~ spl14_8 ),
    inference(resolution,[],[f345,f297])).

fof(f297,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,sK3(X0))
        | ~ r2_hidden(X0,sK1)
        | r1_tarski(X1,sK1) )
    | ~ spl14_6 ),
    inference(resolution,[],[f296,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t9_connsp_2.p',t1_xboole_1)).

fof(f296,plain,
    ( ! [X2] :
        ( r1_tarski(sK3(X2),sK1)
        | ~ r2_hidden(X2,sK1) )
    | ~ spl14_6 ),
    inference(subsumption_resolution,[],[f294,f195])).

fof(f294,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_tarski(sK3(X2),sK1)
        | ~ r2_hidden(X2,sK1) )
    | ~ spl14_6 ),
    inference(avatar_component_clause,[],[f293])).

fof(f293,plain,
    ( spl14_6
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_tarski(sK3(X2),sK1)
        | ~ r2_hidden(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_6])])).

fof(f345,plain,
    ( ! [X3] :
        ( r1_tarski(sK4(sK0,X3,sK3(X3)),sK3(X3))
        | ~ r2_hidden(X3,sK1) )
    | ~ spl14_8 ),
    inference(subsumption_resolution,[],[f344,f330])).

fof(f344,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK1)
        | ~ m1_subset_1(sK3(X3),k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(sK4(sK0,X3,sK3(X3)),sK3(X3)) )
    | ~ spl14_8 ),
    inference(subsumption_resolution,[],[f343,f195])).

fof(f343,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(X3),k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(sK4(sK0,X3,sK3(X3)),sK3(X3)) )
    | ~ spl14_8 ),
    inference(subsumption_resolution,[],[f342,f62])).

fof(f342,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK1)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(X3),k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(sK4(sK0,X3,sK3(X3)),sK3(X3)) )
    | ~ spl14_8 ),
    inference(subsumption_resolution,[],[f341,f61])).

fof(f341,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK1)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(X3),k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(sK4(sK0,X3,sK3(X3)),sK3(X3)) )
    | ~ spl14_8 ),
    inference(subsumption_resolution,[],[f325,f60])).

fof(f325,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK1)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(X3),k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(sK4(sK0,X3,sK3(X3)),sK3(X3)) )
    | ~ spl14_8 ),
    inference(resolution,[],[f308,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(sK4(X0,X1,X2),X2)
      | ~ m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1462,plain,
    ( ! [X6,X5] :
        ( ~ r1_tarski(sK4(sK0,X5,sK3(X5)),sK1)
        | ~ r2_hidden(X6,sK4(sK0,X5,sK3(X5)))
        | m1_connsp_2(sK1,sK0,X6)
        | ~ r2_hidden(X5,sK1) )
    | ~ spl14_8 ),
    inference(subsumption_resolution,[],[f1450,f340])).

fof(f340,plain,
    ( ! [X2] :
        ( v3_pre_topc(sK4(sK0,X2,sK3(X2)),sK0)
        | ~ r2_hidden(X2,sK1) )
    | ~ spl14_8 ),
    inference(subsumption_resolution,[],[f339,f330])).

fof(f339,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK1)
        | ~ m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(sK4(sK0,X2,sK3(X2)),sK0) )
    | ~ spl14_8 ),
    inference(subsumption_resolution,[],[f338,f195])).

fof(f338,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(sK4(sK0,X2,sK3(X2)),sK0) )
    | ~ spl14_8 ),
    inference(subsumption_resolution,[],[f337,f62])).

fof(f337,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK1)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(sK4(sK0,X2,sK3(X2)),sK0) )
    | ~ spl14_8 ),
    inference(subsumption_resolution,[],[f336,f61])).

fof(f336,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK1)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(sK4(sK0,X2,sK3(X2)),sK0) )
    | ~ spl14_8 ),
    inference(subsumption_resolution,[],[f324,f60])).

fof(f324,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK1)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(sK4(sK0,X2,sK3(X2)),sK0) )
    | ~ spl14_8 ),
    inference(resolution,[],[f308,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(sK4(X0,X1,X2),X0)
      | ~ m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1450,plain,
    ( ! [X6,X5] :
        ( ~ v3_pre_topc(sK4(sK0,X5,sK3(X5)),sK0)
        | ~ r1_tarski(sK4(sK0,X5,sK3(X5)),sK1)
        | ~ r2_hidden(X6,sK4(sK0,X5,sK3(X5)))
        | m1_connsp_2(sK1,sK0,X6)
        | ~ r2_hidden(X5,sK1) )
    | ~ spl14_8 ),
    inference(resolution,[],[f214,f335])).

fof(f335,plain,
    ( ! [X1] :
        ( m1_subset_1(sK4(sK0,X1,sK3(X1)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,sK1) )
    | ~ spl14_8 ),
    inference(subsumption_resolution,[],[f334,f330])).

fof(f334,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(sK4(sK0,X1,sK3(X1)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl14_8 ),
    inference(subsumption_resolution,[],[f333,f195])).

fof(f333,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(sK4(sK0,X1,sK3(X1)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl14_8 ),
    inference(subsumption_resolution,[],[f332,f62])).

fof(f332,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(sK4(sK0,X1,sK3(X1)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl14_8 ),
    inference(subsumption_resolution,[],[f331,f61])).

fof(f331,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(sK4(sK0,X1,sK3(X1)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl14_8 ),
    inference(subsumption_resolution,[],[f323,f60])).

fof(f323,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(sK4(sK0,X1,sK3(X1)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl14_8 ),
    inference(resolution,[],[f308,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f214,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X5,sK0)
      | ~ r1_tarski(X5,sK1)
      | ~ r2_hidden(X4,X5)
      | m1_connsp_2(sK1,sK0,X4) ) ),
    inference(subsumption_resolution,[],[f213,f91])).

fof(f213,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X5,sK0)
      | ~ r1_tarski(X5,sK1)
      | ~ r2_hidden(X4,X5)
      | m1_connsp_2(sK1,sK0,X4) ) ),
    inference(subsumption_resolution,[],[f212,f62])).

fof(f212,plain,(
    ! [X4,X5] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X5,sK0)
      | ~ r1_tarski(X5,sK1)
      | ~ r2_hidden(X4,X5)
      | m1_connsp_2(sK1,sK0,X4) ) ),
    inference(subsumption_resolution,[],[f211,f61])).

fof(f211,plain,(
    ! [X4,X5] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X5,sK0)
      | ~ r1_tarski(X5,sK1)
      | ~ r2_hidden(X4,X5)
      | m1_connsp_2(sK1,sK0,X4) ) ),
    inference(subsumption_resolution,[],[f180,f60])).

fof(f180,plain,(
    ! [X4,X5] :
      ( v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X5,sK0)
      | ~ r1_tarski(X5,sK1)
      | ~ r2_hidden(X4,X5)
      | m1_connsp_2(sK1,sK0,X4) ) ),
    inference(resolution,[],[f59,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | ~ r1_tarski(X3,X2)
      | ~ r2_hidden(X1,X3)
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6429,plain,
    ( ~ m1_connsp_2(sK1,sK0,sK5(sK0,sK1))
    | ~ spl14_75 ),
    inference(avatar_component_clause,[],[f6428])).

fof(f6428,plain,
    ( spl14_75
  <=> ~ m1_connsp_2(sK1,sK0,sK5(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_75])])).

fof(f6436,plain,
    ( ~ spl14_75
    | ~ spl14_77
    | ~ spl14_56 ),
    inference(avatar_split_clause,[],[f6408,f1899,f6434,f6428])).

fof(f1899,plain,
    ( spl14_56
  <=> ! [X9] :
        ( ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK5(sK0,sK1),X9)
        | ~ r1_tarski(X9,sK1)
        | ~ v3_pre_topc(X9,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_56])])).

fof(f6408,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_connsp_2(sK1,sK0,sK5(sK0,sK1))
    | ~ spl14_56 ),
    inference(subsumption_resolution,[],[f6407,f204])).

fof(f204,plain,(
    ! [X1] :
      ( v3_pre_topc(sK4(sK0,X1,sK1),sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_connsp_2(sK1,sK0,X1) ) ),
    inference(subsumption_resolution,[],[f203,f62])).

fof(f203,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v3_pre_topc(sK4(sK0,X1,sK1),sK0)
      | ~ m1_connsp_2(sK1,sK0,X1) ) ),
    inference(subsumption_resolution,[],[f202,f61])).

fof(f202,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v3_pre_topc(sK4(sK0,X1,sK1),sK0)
      | ~ m1_connsp_2(sK1,sK0,X1) ) ),
    inference(subsumption_resolution,[],[f177,f60])).

fof(f177,plain,(
    ! [X1] :
      ( v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v3_pre_topc(sK4(sK0,X1,sK1),sK0)
      | ~ m1_connsp_2(sK1,sK0,X1) ) ),
    inference(resolution,[],[f59,f65])).

fof(f6407,plain,
    ( ~ v3_pre_topc(sK4(sK0,sK5(sK0,sK1),sK1),sK0)
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_connsp_2(sK1,sK0,sK5(sK0,sK1))
    | ~ spl14_56 ),
    inference(subsumption_resolution,[],[f6392,f207])).

fof(f207,plain,(
    ! [X2] :
      ( r1_tarski(sK4(sK0,X2,sK1),sK1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_connsp_2(sK1,sK0,X2) ) ),
    inference(subsumption_resolution,[],[f206,f62])).

fof(f206,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_tarski(sK4(sK0,X2,sK1),sK1)
      | ~ m1_connsp_2(sK1,sK0,X2) ) ),
    inference(subsumption_resolution,[],[f205,f61])).

fof(f205,plain,(
    ! [X2] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_tarski(sK4(sK0,X2,sK1),sK1)
      | ~ m1_connsp_2(sK1,sK0,X2) ) ),
    inference(subsumption_resolution,[],[f178,f60])).

fof(f178,plain,(
    ! [X2] :
      ( v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_tarski(sK4(sK0,X2,sK1),sK1)
      | ~ m1_connsp_2(sK1,sK0,X2) ) ),
    inference(resolution,[],[f59,f66])).

fof(f6392,plain,
    ( ~ r1_tarski(sK4(sK0,sK5(sK0,sK1),sK1),sK1)
    | ~ v3_pre_topc(sK4(sK0,sK5(sK0,sK1),sK1),sK0)
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_connsp_2(sK1,sK0,sK5(sK0,sK1))
    | ~ spl14_56 ),
    inference(resolution,[],[f6365,f210])).

fof(f210,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK4(sK0,X3,sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_connsp_2(sK1,sK0,X3) ) ),
    inference(subsumption_resolution,[],[f209,f62])).

fof(f209,plain,(
    ! [X3] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r2_hidden(X3,sK4(sK0,X3,sK1))
      | ~ m1_connsp_2(sK1,sK0,X3) ) ),
    inference(subsumption_resolution,[],[f208,f61])).

fof(f208,plain,(
    ! [X3] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r2_hidden(X3,sK4(sK0,X3,sK1))
      | ~ m1_connsp_2(sK1,sK0,X3) ) ),
    inference(subsumption_resolution,[],[f179,f60])).

fof(f179,plain,(
    ! [X3] :
      ( v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r2_hidden(X3,sK4(sK0,X3,sK1))
      | ~ m1_connsp_2(sK1,sK0,X3) ) ),
    inference(resolution,[],[f59,f67])).

fof(f6365,plain,
    ( ! [X9] :
        ( ~ r2_hidden(sK5(sK0,sK1),X9)
        | ~ r1_tarski(X9,sK1)
        | ~ v3_pre_topc(X9,sK0) )
    | ~ spl14_56 ),
    inference(subsumption_resolution,[],[f1900,f1981])).

fof(f1981,plain,(
    ! [X4] :
      ( ~ r1_tarski(X4,sK1)
      | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f278,f86])).

fof(f278,plain,(
    ! [X0] :
      ( r1_tarski(X0,u1_struct_0(sK0))
      | ~ r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f196,f90])).

fof(f196,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f59,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1900,plain,
    ( ! [X9] :
        ( ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK5(sK0,sK1),X9)
        | ~ r1_tarski(X9,sK1)
        | ~ v3_pre_topc(X9,sK0) )
    | ~ spl14_56 ),
    inference(avatar_component_clause,[],[f1899])).

fof(f1901,plain,
    ( spl14_0
    | ~ spl14_37
    | spl14_56 ),
    inference(avatar_split_clause,[],[f222,f1899,f991,f246])).

fof(f222,plain,(
    ! [X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X9,sK0)
      | ~ r1_tarski(X9,sK1)
      | ~ r2_hidden(sK5(sK0,sK1),X9)
      | ~ r2_hidden(sK5(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f221,f62])).

fof(f221,plain,(
    ! [X9] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X9,sK0)
      | ~ r1_tarski(X9,sK1)
      | ~ r2_hidden(sK5(sK0,sK1),X9)
      | ~ r2_hidden(sK5(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f183,f61])).

fof(f183,plain,(
    ! [X9] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X9,sK0)
      | ~ r1_tarski(X9,sK1)
      | ~ r2_hidden(sK5(sK0,sK1),X9)
      | ~ r2_hidden(sK5(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(resolution,[],[f59,f70])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | ~ r1_tarski(X3,X1)
      | ~ r2_hidden(sK5(X0,X1),X3)
      | ~ r2_hidden(sK5(X0,X1),X1)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f940,plain,
    ( ~ spl14_1
    | spl14_34 ),
    inference(avatar_split_clause,[],[f240,f938,f249])).

fof(f240,plain,(
    ! [X14] :
      ( r2_hidden(X14,sK6(sK0,sK1,X14))
      | ~ r2_hidden(X14,sK1)
      | ~ v3_pre_topc(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f239,f62])).

fof(f239,plain,(
    ! [X14] :
      ( ~ l1_pre_topc(sK0)
      | r2_hidden(X14,sK6(sK0,sK1,X14))
      | ~ r2_hidden(X14,sK1)
      | ~ v3_pre_topc(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f192,f61])).

fof(f192,plain,(
    ! [X14] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | r2_hidden(X14,sK6(sK0,sK1,X14))
      | ~ r2_hidden(X14,sK1)
      | ~ v3_pre_topc(sK1,sK0) ) ),
    inference(resolution,[],[f59,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X2,sK6(X0,X1,X2))
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f930,plain,
    ( ~ spl14_1
    | spl14_30 ),
    inference(avatar_split_clause,[],[f236,f928,f249])).

fof(f236,plain,(
    ! [X12] :
      ( v3_pre_topc(sK6(sK0,sK1,X12),sK0)
      | ~ r2_hidden(X12,sK1)
      | ~ v3_pre_topc(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f235,f62])).

fof(f235,plain,(
    ! [X12] :
      ( ~ l1_pre_topc(sK0)
      | v3_pre_topc(sK6(sK0,sK1,X12),sK0)
      | ~ r2_hidden(X12,sK1)
      | ~ v3_pre_topc(sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f190,f61])).

fof(f190,plain,(
    ! [X12] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v3_pre_topc(sK6(sK0,sK1,X12),sK0)
      | ~ r2_hidden(X12,sK1)
      | ~ v3_pre_topc(sK1,sK0) ) ),
    inference(resolution,[],[f59,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(sK6(X0,X1,X2),X0)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f354,plain,
    ( ~ spl14_1
    | spl14_14 ),
    inference(avatar_split_clause,[],[f56,f352,f249])).

fof(f56,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(X3,sK0,sK2)
      | ~ r1_tarski(X3,sK1)
      | ~ v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f307,plain,
    ( spl14_0
    | spl14_8 ),
    inference(avatar_split_clause,[],[f54,f305,f246])).

fof(f54,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,sK1)
      | m1_connsp_2(sK3(X2),sK0,X2)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f295,plain,
    ( spl14_0
    | spl14_6 ),
    inference(avatar_split_clause,[],[f55,f293,f246])).

fof(f55,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,sK1)
      | r1_tarski(sK3(X2),sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f291,plain,
    ( ~ spl14_1
    | spl14_4 ),
    inference(avatar_split_clause,[],[f57,f289,f249])).

fof(f57,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f257,plain,
    ( ~ spl14_1
    | spl14_2 ),
    inference(avatar_split_clause,[],[f58,f255,f249])).

fof(f58,plain,
    ( r2_hidden(sK2,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
