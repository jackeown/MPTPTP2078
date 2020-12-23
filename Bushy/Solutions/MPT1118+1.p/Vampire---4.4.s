%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : pre_topc__t49_pre_topc.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:43 EDT 2019

% Result     : Theorem 22.49s
% Output     : Refutation 22.49s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 207 expanded)
%              Number of leaves         :   12 (  48 expanded)
%              Depth                    :   14
%              Number of atoms          :  267 ( 804 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2657,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1638,f1650,f1686,f1823,f2583,f2656])).

fof(f2656,plain,
    ( ~ spl9_46
    | ~ spl9_48
    | ~ spl9_52
    | ~ spl9_54
    | ~ spl9_68 ),
    inference(avatar_contradiction_clause,[],[f2655])).

fof(f2655,plain,
    ( $false
    | ~ spl9_46
    | ~ spl9_48
    | ~ spl9_52
    | ~ spl9_54
    | ~ spl9_68 ),
    inference(subsumption_resolution,[],[f2654,f141])).

fof(f141,plain,(
    ~ r2_hidden(sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,sK2)) ),
    inference(resolution,[],[f51,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t49_pre_topc.p',d3_tarski)).

fof(f51,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X1,X2)
                 => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t49_pre_topc.p',t49_pre_topc)).

fof(f2654,plain,
    ( r2_hidden(sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,sK2))
    | ~ spl9_46
    | ~ spl9_48
    | ~ spl9_52
    | ~ spl9_54
    | ~ spl9_68 ),
    inference(subsumption_resolution,[],[f2653,f1634])).

fof(f1634,plain,
    ( r2_hidden(sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),u1_struct_0(sK0))
    | ~ spl9_48 ),
    inference(avatar_component_clause,[],[f1633])).

fof(f1633,plain,
    ( spl9_48
  <=> r2_hidden(sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).

fof(f2653,plain,
    ( ~ r2_hidden(sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),u1_struct_0(sK0))
    | r2_hidden(sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,sK2))
    | ~ spl9_46
    | ~ spl9_52
    | ~ spl9_54
    | ~ spl9_68 ),
    inference(subsumption_resolution,[],[f2652,f1631])).

fof(f1631,plain,
    ( v4_pre_topc(sK3(sK0,sK2,sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))),sK0)
    | ~ spl9_46 ),
    inference(avatar_component_clause,[],[f1630])).

fof(f1630,plain,
    ( spl9_46
  <=> v4_pre_topc(sK3(sK0,sK2,sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).

fof(f2652,plain,
    ( ~ v4_pre_topc(sK3(sK0,sK2,sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))),sK0)
    | ~ r2_hidden(sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),u1_struct_0(sK0))
    | r2_hidden(sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,sK2))
    | ~ spl9_52
    | ~ spl9_54
    | ~ spl9_68 ),
    inference(subsumption_resolution,[],[f2651,f1689])).

fof(f1689,plain,
    ( r1_tarski(sK1,sK3(sK0,sK2,sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))))
    | ~ spl9_52 ),
    inference(resolution,[],[f1685,f94])).

fof(f94,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK2,X1)
      | r1_tarski(sK1,X1) ) ),
    inference(resolution,[],[f50,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t49_pre_topc.p',t1_xboole_1)).

fof(f50,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f1685,plain,
    ( r1_tarski(sK2,sK3(sK0,sK2,sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))))
    | ~ spl9_52 ),
    inference(avatar_component_clause,[],[f1684])).

fof(f1684,plain,
    ( spl9_52
  <=> r1_tarski(sK2,sK3(sK0,sK2,sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_52])])).

fof(f2651,plain,
    ( ~ r1_tarski(sK1,sK3(sK0,sK2,sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))))
    | ~ v4_pre_topc(sK3(sK0,sK2,sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))),sK0)
    | ~ r2_hidden(sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),u1_struct_0(sK0))
    | r2_hidden(sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,sK2))
    | ~ spl9_54
    | ~ spl9_68 ),
    inference(subsumption_resolution,[],[f2626,f1822])).

fof(f1822,plain,
    ( m1_subset_1(sK3(sK0,sK2,sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_54 ),
    inference(avatar_component_clause,[],[f1821])).

fof(f1821,plain,
    ( spl9_54
  <=> m1_subset_1(sK3(sK0,sK2,sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_54])])).

fof(f2626,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2,sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK1,sK3(sK0,sK2,sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))))
    | ~ v4_pre_topc(sK3(sK0,sK2,sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))),sK0)
    | ~ r2_hidden(sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),u1_struct_0(sK0))
    | r2_hidden(sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,sK2))
    | ~ spl9_68 ),
    inference(resolution,[],[f2582,f115])).

fof(f115,plain,(
    ! [X7] :
      ( ~ r2_hidden(X7,sK3(sK0,sK2,X7))
      | ~ r2_hidden(X7,u1_struct_0(sK0))
      | r2_hidden(X7,k2_pre_topc(sK0,sK2)) ) ),
    inference(subsumption_resolution,[],[f103,f53])).

fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f103,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(sK0)
      | ~ r2_hidden(X7,u1_struct_0(sK0))
      | ~ r2_hidden(X7,sK3(sK0,sK2,X7))
      | r2_hidden(X7,k2_pre_topc(sK0,sK2)) ) ),
    inference(resolution,[],[f49,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,sK3(X0,X1,X2))
      | r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( r2_hidden(X2,X3)
                    | ~ r1_tarski(X1,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( r2_hidden(X2,X3)
                    | ~ r1_tarski(X1,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( r2_hidden(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( r1_tarski(X1,X3)
                        & v4_pre_topc(X3,X0) )
                     => r2_hidden(X2,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t49_pre_topc.p',t45_pre_topc)).

fof(f49,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f2582,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK1,X0)
        | ~ v4_pre_topc(X0,sK0) )
    | ~ spl9_68 ),
    inference(avatar_component_clause,[],[f2581])).

fof(f2581,plain,
    ( spl9_68
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),X0)
        | ~ r1_tarski(sK1,X0)
        | ~ v4_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_68])])).

fof(f2583,plain,
    ( spl9_68
    | ~ spl9_49 ),
    inference(avatar_split_clause,[],[f305,f1636,f2581])).

fof(f1636,plain,
    ( spl9_49
  <=> ~ r2_hidden(sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).

fof(f305,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X0,sK0)
      | ~ r1_tarski(sK1,X0)
      | r2_hidden(sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),X0) ) ),
    inference(subsumption_resolution,[],[f304,f52])).

fof(f52,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f304,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X0,sK0)
      | ~ r1_tarski(sK1,X0)
      | r2_hidden(sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),X0) ) ),
    inference(subsumption_resolution,[],[f296,f53])).

fof(f296,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X0,sK0)
      | ~ r1_tarski(sK1,X0)
      | r2_hidden(sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),X0) ) ),
    inference(resolution,[],[f140,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X3,X0)
      | ~ r1_tarski(X1,X3)
      | r2_hidden(X2,X3)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f140,plain,(
    r2_hidden(sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f51,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1823,plain,
    ( spl9_54
    | ~ spl9_49 ),
    inference(avatar_split_clause,[],[f315,f1636,f1821])).

fof(f315,plain,
    ( ~ r2_hidden(sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,sK2,sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f314,f49])).

fof(f314,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,sK2,sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f307,f53])).

fof(f307,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,sK2,sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f141,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,u1_struct_0(X0))
      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1686,plain,
    ( spl9_52
    | ~ spl9_49 ),
    inference(avatar_split_clause,[],[f319,f1636,f1684])).

fof(f319,plain,
    ( ~ r2_hidden(sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),u1_struct_0(sK0))
    | r1_tarski(sK2,sK3(sK0,sK2,sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))) ),
    inference(subsumption_resolution,[],[f318,f49])).

fof(f318,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),u1_struct_0(sK0))
    | r1_tarski(sK2,sK3(sK0,sK2,sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))) ),
    inference(subsumption_resolution,[],[f309,f53])).

fof(f309,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),u1_struct_0(sK0))
    | r1_tarski(sK2,sK3(sK0,sK2,sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))) ),
    inference(resolution,[],[f141,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,u1_struct_0(X0))
      | r1_tarski(X1,sK3(X0,X1,X2))
      | r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1650,plain,(
    spl9_49 ),
    inference(avatar_contradiction_clause,[],[f1649])).

fof(f1649,plain,
    ( $false
    | ~ spl9_49 ),
    inference(subsumption_resolution,[],[f1641,f230])).

fof(f230,plain,(
    r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f136,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t49_pre_topc.p',t3_subset)).

fof(f136,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f124,f53])).

fof(f124,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f52,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t49_pre_topc.p',dt_k2_pre_topc)).

fof(f1641,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0))
    | ~ spl9_49 ),
    inference(resolution,[],[f1637,f300])).

fof(f300,plain,(
    ! [X1] :
      ( r2_hidden(sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),X1)
      | ~ r1_tarski(k2_pre_topc(sK0,sK1),X1) ) ),
    inference(resolution,[],[f140,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1637,plain,
    ( ~ r2_hidden(sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),u1_struct_0(sK0))
    | ~ spl9_49 ),
    inference(avatar_component_clause,[],[f1636])).

fof(f1638,plain,
    ( spl9_46
    | ~ spl9_49 ),
    inference(avatar_split_clause,[],[f317,f1636,f1630])).

fof(f317,plain,
    ( ~ r2_hidden(sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),u1_struct_0(sK0))
    | v4_pre_topc(sK3(sK0,sK2,sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))),sK0) ),
    inference(subsumption_resolution,[],[f316,f49])).

fof(f316,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),u1_struct_0(sK0))
    | v4_pre_topc(sK3(sK0,sK2,sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))),sK0) ),
    inference(subsumption_resolution,[],[f308,f53])).

fof(f308,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),u1_struct_0(sK0))
    | v4_pre_topc(sK3(sK0,sK2,sK5(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))),sK0) ),
    inference(resolution,[],[f141,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,u1_struct_0(X0))
      | v4_pre_topc(sK3(X0,X1,X2),X0)
      | r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
