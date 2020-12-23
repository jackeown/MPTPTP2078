%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : connsp_2__t21_connsp_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:52 EDT 2019

% Result     : Theorem 6.67s
% Output     : Refutation 6.67s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 404 expanded)
%              Number of leaves         :   21 (  94 expanded)
%              Depth                    :   11
%              Number of atoms          :  369 (1749 expanded)
%              Number of equality atoms :    9 (  22 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1486,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f494,f564,f817,f1040,f1431,f1485])).

fof(f1485,plain,(
    ~ spl10_34 ),
    inference(avatar_contradiction_clause,[],[f1480])).

fof(f1480,plain,
    ( $false
    | ~ spl10_34 ),
    inference(unit_resulting_resolution,[],[f80,f1432])).

fof(f1432,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl10_34 ),
    inference(backward_demodulation,[],[f810,f165])).

fof(f165,plain,(
    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f82,f83,f78,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t21_connsp_2.p',fc9_tops_1)).

fof(f78,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v3_connsp_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & v1_connsp_2(X0)
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v3_connsp_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & v1_connsp_2(X0)
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v1_connsp_2(X0)
         => ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ( v3_connsp_1(X1,X0)
               => v3_pre_topc(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_connsp_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_connsp_1(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t21_connsp_2.p',t21_connsp_2)).

fof(f83,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f82,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f810,plain,
    ( k1_tops_1(sK0,sK1) = sK1
    | ~ spl10_34 ),
    inference(avatar_component_clause,[],[f809])).

fof(f809,plain,
    ( spl10_34
  <=> k1_tops_1(sK0,sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f80,plain,(
    ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f1431,plain,
    ( spl10_37
    | ~ spl10_46 ),
    inference(avatar_contradiction_clause,[],[f1427])).

fof(f1427,plain,
    ( $false
    | ~ spl10_37
    | ~ spl10_46 ),
    inference(unit_resulting_resolution,[],[f82,f83,f81,f78,f182,f161,f1056,f819,f1380,f838,f1079,f118])).

fof(f118,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ r3_connsp_1(X0,X2,X3)
      | ~ r2_hidden(X1,X3)
      | m1_connsp_2(X3,X0,X1)
      | ~ r1_connsp_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_connsp_2(X0,X1)
          <=> ! [X2] :
                ( ! [X3] :
                    ( m1_connsp_2(X3,X0,X1)
                    | ~ r2_hidden(X1,X3)
                    | ~ r3_connsp_1(X0,X2,X3)
                    | ~ m1_connsp_2(X2,X0,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_connsp_2(X0,X1)
          <=> ! [X2] :
                ( ! [X3] :
                    ( m1_connsp_2(X3,X0,X1)
                    | ~ r2_hidden(X1,X3)
                    | ~ r3_connsp_1(X0,X2,X3)
                    | ~ m1_connsp_2(X2,X0,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_connsp_2(X0,X1)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( r2_hidden(X1,X3)
                        & r3_connsp_1(X0,X2,X3)
                        & m1_connsp_2(X2,X0,X1) )
                     => m1_connsp_2(X3,X0,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t21_connsp_2.p',t19_connsp_2)).

fof(f1079,plain,
    ( m1_connsp_2(u1_struct_0(sK0),sK0,sK6(sK1,k1_tops_1(sK0,sK1)))
    | ~ spl10_37
    | ~ spl10_46 ),
    inference(unit_resulting_resolution,[],[f163,f161,f838,f842,f1039])).

fof(f1039,plain,
    ( ! [X4,X5] :
        ( m1_connsp_2(X4,sK0,X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X4,sK0)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_hidden(X5,X4) )
    | ~ spl10_46 ),
    inference(avatar_component_clause,[],[f1038])).

fof(f1038,plain,
    ( spl10_46
  <=> ! [X5,X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_connsp_2(X4,sK0,X5)
        | ~ v3_pre_topc(X4,sK0)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_hidden(X5,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_46])])).

fof(f842,plain,
    ( r2_hidden(sK6(sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl10_37 ),
    inference(unit_resulting_resolution,[],[f171,f819,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t21_connsp_2.p',d3_tarski)).

fof(f171,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f78,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t21_connsp_2.p',t3_subset)).

fof(f163,plain,(
    v3_pre_topc(u1_struct_0(sK0),sK0) ),
    inference(backward_demodulation,[],[f156,f142])).

fof(f142,plain,(
    v3_pre_topc(k2_struct_0(sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f82,f83,f86])).

fof(f86,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t21_connsp_2.p',fc10_tops_1)).

fof(f156,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f147,f105])).

fof(f105,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t21_connsp_2.p',d3_struct_0)).

fof(f147,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f83,f127])).

fof(f127,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t21_connsp_2.p',dt_l1_pre_topc)).

fof(f838,plain,
    ( m1_subset_1(sK6(sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl10_37 ),
    inference(unit_resulting_resolution,[],[f78,f819,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t21_connsp_2.p',t4_subset)).

fof(f1380,plain,
    ( ~ m1_connsp_2(sK1,sK0,sK6(sK1,k1_tops_1(sK0,sK1)))
    | ~ spl10_37 ),
    inference(unit_resulting_resolution,[],[f83,f82,f81,f78,f838,f820,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t21_connsp_2.p',d1_connsp_2)).

fof(f820,plain,
    ( ~ r2_hidden(sK6(sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))
    | ~ spl10_37 ),
    inference(unit_resulting_resolution,[],[f816,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f816,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl10_37 ),
    inference(avatar_component_clause,[],[f815])).

fof(f815,plain,
    ( spl10_37
  <=> ~ r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).

fof(f819,plain,
    ( r2_hidden(sK6(sK1,k1_tops_1(sK0,sK1)),sK1)
    | ~ spl10_37 ),
    inference(unit_resulting_resolution,[],[f816,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f1056,plain,
    ( r1_connsp_2(sK0,sK6(sK1,k1_tops_1(sK0,sK1)))
    | ~ spl10_37 ),
    inference(unit_resulting_resolution,[],[f81,f82,f84,f83,f838,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v1_connsp_2(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_connsp_2(X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( v1_connsp_2(X0)
      <=> ! [X1] :
            ( r1_connsp_2(X0,X1)
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( v1_connsp_2(X0)
      <=> ! [X1] :
            ( r1_connsp_2(X0,X1)
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_connsp_2(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => r1_connsp_2(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t21_connsp_2.p',d4_connsp_2)).

fof(f84,plain,(
    v1_connsp_2(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f161,plain,(
    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f156,f157])).

fof(f157,plain,(
    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f147,f104])).

fof(f104,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t21_connsp_2.p',dt_k2_struct_0)).

fof(f182,plain,(
    r3_connsp_1(sK0,u1_struct_0(sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f81,f82,f83,f79,f171,f78,f161,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_connsp_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | r3_connsp_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_connsp_1(X0,X2,X1)
              | ~ r1_tarski(X1,X2)
              | ~ v3_connsp_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_connsp_1(X0,X2,X1)
              | ~ r1_tarski(X1,X2)
              | ~ v3_connsp_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_connsp_1(X1,X0) )
               => r3_connsp_1(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t21_connsp_2.p',t13_connsp_2)).

fof(f79,plain,(
    v3_connsp_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f81,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f1040,plain,
    ( spl10_46
    | spl10_12
    | ~ spl10_11 ),
    inference(avatar_split_clause,[],[f152,f488,f545,f1038])).

fof(f545,plain,
    ( spl10_12
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f488,plain,
    ( spl10_11
  <=> ~ v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f152,plain,(
    ! [X4,X5] :
      ( ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ v3_pre_topc(X4,sK0)
      | ~ r2_hidden(X5,X4)
      | m1_connsp_2(X4,sK0,X5) ) ),
    inference(resolution,[],[f83,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ r2_hidden(X2,X1)
      | m1_connsp_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/connsp_2__t21_connsp_2.p',t5_connsp_2)).

fof(f817,plain,
    ( spl10_34
    | ~ spl10_37 ),
    inference(avatar_split_clause,[],[f178,f815,f809])).

fof(f178,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | k1_tops_1(sK0,sK1) = sK1 ),
    inference(resolution,[],[f170,f124])).

fof(f124,plain,(
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
    file('/export/starexec/sandbox2/benchmark/connsp_2__t21_connsp_2.p',d10_xboole_0)).

fof(f170,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f83,f78,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t21_connsp_2.p',t44_tops_1)).

fof(f564,plain,(
    ~ spl10_12 ),
    inference(avatar_contradiction_clause,[],[f561])).

fof(f561,plain,
    ( $false
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f81,f546])).

fof(f546,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f545])).

fof(f494,plain,(
    spl10_11 ),
    inference(avatar_contradiction_clause,[],[f491])).

fof(f491,plain,
    ( $false
    | ~ spl10_11 ),
    inference(unit_resulting_resolution,[],[f82,f489])).

fof(f489,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f488])).
%------------------------------------------------------------------------------
