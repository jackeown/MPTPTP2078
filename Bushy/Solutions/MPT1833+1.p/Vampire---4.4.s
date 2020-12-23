%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t149_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:09 EDT 2019

% Result     : Theorem 125.73s
% Output     : Refutation 125.73s
% Verified   : 
% Statistics : Number of formulae       :  308 (1593 expanded)
%              Number of leaves         :   29 ( 326 expanded)
%              Depth                    :   33
%              Number of atoms          : 2763 (26682 expanded)
%              Number of equality atoms :   54 ( 106 expanded)
%              Maximal formula depth    :   30 (  10 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1333,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f211,f295,f315,f336,f977,f1013,f1055,f1068,f1134,f1162,f1182,f1208,f1298,f1300,f1332])).

fof(f1332,plain,
    ( spl13_69
    | ~ spl13_78 ),
    inference(avatar_contradiction_clause,[],[f1331])).

fof(f1331,plain,
    ( $false
    | ~ spl13_69
    | ~ spl13_78 ),
    inference(subsumption_resolution,[],[f1313,f98])).

fof(f98,plain,(
    v5_pre_topc(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & r1_tsep_1(X2,X3)
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_tsep_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & r1_tsep_1(X2,X3)
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_tsep_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
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
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_tsep_1(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( r1_tsep_1(X2,X3)
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(X4,X2,X1)
                            & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X4) )
                         => ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                & v5_pre_topc(X5,X3,X1)
                                & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                                & v1_funct_1(X5) )
                             => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                                & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
                & v1_tsep_1(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_tsep_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( r1_tsep_1(X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(X4,X2,X1)
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v5_pre_topc(X5,X3,X1)
                              & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                              & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t149_tmap_1.p',t149_tmap_1)).

fof(f1313,plain,
    ( ~ v5_pre_topc(sK4,sK2,sK1)
    | ~ spl13_69
    | ~ spl13_78 ),
    inference(backward_demodulation,[],[f1246,f1121])).

fof(f1121,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ spl13_69 ),
    inference(avatar_component_clause,[],[f1120])).

fof(f1120,plain,
    ( spl13_69
  <=> ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_69])])).

fof(f1246,plain,
    ( k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) = sK4
    | ~ spl13_78 ),
    inference(avatar_component_clause,[],[f1245])).

fof(f1245,plain,
    ( spl13_78
  <=> k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_78])])).

fof(f1300,plain,
    ( ~ spl13_77
    | spl13_78
    | ~ spl13_66
    | ~ spl13_70
    | ~ spl13_72 ),
    inference(avatar_split_clause,[],[f1299,f1129,f1123,f1111,f1245,f1236])).

fof(f1236,plain,
    ( spl13_77
  <=> ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_77])])).

fof(f1111,plain,
    ( spl13_66
  <=> m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_66])])).

fof(f1123,plain,
    ( spl13_70
  <=> v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_70])])).

fof(f1129,plain,
    ( spl13_72
  <=> v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_72])])).

fof(f1299,plain,
    ( k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) = sK4
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
    | ~ spl13_66
    | ~ spl13_70
    | ~ spl13_72 ),
    inference(subsumption_resolution,[],[f1278,f1124])).

fof(f1124,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl13_70 ),
    inference(avatar_component_clause,[],[f1123])).

fof(f1278,plain,
    ( k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) = sK4
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl13_66
    | ~ spl13_72 ),
    inference(subsumption_resolution,[],[f1273,f1130])).

fof(f1130,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl13_72 ),
    inference(avatar_component_clause,[],[f1129])).

fof(f1273,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) = sK4
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl13_66 ),
    inference(resolution,[],[f1221,f519])).

fof(f519,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
      | ~ v1_funct_1(X0)
      | sK4 = X0
      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0,sK4)
      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f281,f158])).

fof(f158,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t149_tmap_1.p',t3_subset)).

fof(f281,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(X5)
      | sK4 = X5
      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X5,sK4) ) ),
    inference(subsumption_resolution,[],[f280,f97])).

fof(f97,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f280,plain,(
    ! [X5] :
      ( ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(X5)
      | sK4 = X5
      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X5,sK4) ) ),
    inference(subsumption_resolution,[],[f261,f96])).

fof(f96,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f261,plain,(
    ! [X5] :
      ( ~ v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(X5)
      | sK4 = X5
      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X5,sK4) ) ),
    inference(resolution,[],[f99,f174])).

fof(f174,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X2)
      | X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f85])).

fof(f85,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t149_tmap_1.p',redefinition_r2_funct_2)).

fof(f99,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f1221,plain,
    ( r1_tarski(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
    | ~ spl13_66 ),
    inference(resolution,[],[f1112,f159])).

fof(f159,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1112,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl13_66 ),
    inference(avatar_component_clause,[],[f1111])).

fof(f1298,plain,
    ( ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | spl13_77 ),
    inference(avatar_contradiction_clause,[],[f1295])).

fof(f1295,plain,
    ( $false
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_77 ),
    inference(unit_resulting_resolution,[],[f368,f1237,f130])).

fof(f130,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4)
      | ~ sP7(X6,X5,X4,X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                              <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                  & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              | ~ v1_funct_1(X6) )
                          | ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                            & ~ r1_tsep_1(X2,X3) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                              <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                  & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              | ~ v1_funct_1(X6) )
                          | ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                            & ~ r1_tsep_1(X2,X3) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                         => ( ( r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                              | r1_tsep_1(X2,X3) )
                           => ! [X6] :
                                ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                  & v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                  & v1_funct_1(X6) )
                               => ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                    & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t149_tmap_1.p',d13_tmap_1)).

fof(f1237,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
    | ~ spl13_77 ),
    inference(avatar_component_clause,[],[f1236])).

fof(f368,plain,
    ( sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f367,f110])).

fof(f110,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f367,plain,
    ( v2_struct_0(sK0)
    | sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f366,f201])).

fof(f201,plain,
    ( v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ spl13_4 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl13_4
  <=> v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f366,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ spl13_0
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f365,f207])).

fof(f207,plain,
    ( v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl13_6 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl13_6
  <=> v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).

fof(f365,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f364,f103])).

fof(f103,plain,(
    r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f364,plain,
    ( ~ r1_tsep_1(sK2,sK3)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f363,f95])).

fof(f95,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f363,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r1_tsep_1(sK2,sK3)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f362,f93])).

fof(f93,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f362,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r1_tsep_1(sK2,sK3)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f361,f92])).

fof(f92,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f361,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r1_tsep_1(sK2,sK3)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f360,f99])).

fof(f360,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r1_tsep_1(sK2,sK3)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f359,f97])).

fof(f359,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r1_tsep_1(sK2,sK3)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f358,f96])).

fof(f358,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r1_tsep_1(sK2,sK3)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f357,f102])).

fof(f102,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f357,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r1_tsep_1(sK2,sK3)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f356,f100])).

fof(f100,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f356,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r1_tsep_1(sK2,sK3)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f355,f106])).

fof(f106,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f355,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r1_tsep_1(sK2,sK3)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f354,f104])).

fof(f104,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f354,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r1_tsep_1(sK2,sK3)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f353,f109])).

fof(f109,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f353,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r1_tsep_1(sK2,sK3)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f352,f108])).

fof(f108,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f352,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r1_tsep_1(sK2,sK3)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f351,f107])).

fof(f107,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f351,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r1_tsep_1(sK2,sK3)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f350,f112])).

fof(f112,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f350,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r1_tsep_1(sK2,sK3)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f337,f111])).

fof(f111,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f337,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r1_tsep_1(sK2,sK3)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ spl13_0 ),
    inference(resolution,[],[f189,f184])).

fof(f184,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ r1_tsep_1(X2,X3)
      | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | v2_struct_0(X0)
      | sP7(k10_tmap_1(X0,X1,X2,X3,X4,X5),X5,X4,X3,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f133])).

fof(f133,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ r1_tsep_1(X2,X3)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | sP7(X6,X5,X4,X3,X2,X1,X0)
      | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f189,plain,
    ( m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl13_0 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl13_0
  <=> m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_0])])).

fof(f1208,plain,
    ( ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_60
    | spl13_67 ),
    inference(avatar_contradiction_clause,[],[f1207])).

fof(f1207,plain,
    ( $false
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_60
    | ~ spl13_67 ),
    inference(subsumption_resolution,[],[f1206,f110])).

fof(f1206,plain,
    ( v2_struct_0(sK0)
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_60
    | ~ spl13_67 ),
    inference(subsumption_resolution,[],[f1205,f189])).

fof(f1205,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_60
    | ~ spl13_67 ),
    inference(subsumption_resolution,[],[f1204,f201])).

fof(f1204,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_6
    | ~ spl13_60
    | ~ spl13_67 ),
    inference(subsumption_resolution,[],[f1203,f207])).

fof(f1203,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_60
    | ~ spl13_67 ),
    inference(subsumption_resolution,[],[f1202,f106])).

fof(f1202,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_60
    | ~ spl13_67 ),
    inference(subsumption_resolution,[],[f1201,f967])).

fof(f967,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ spl13_60 ),
    inference(avatar_component_clause,[],[f966])).

fof(f966,plain,
    ( spl13_60
  <=> m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_60])])).

fof(f1201,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_67 ),
    inference(subsumption_resolution,[],[f1200,f109])).

fof(f1200,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_67 ),
    inference(subsumption_resolution,[],[f1199,f108])).

fof(f1199,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_67 ),
    inference(subsumption_resolution,[],[f1198,f107])).

fof(f1198,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_67 ),
    inference(subsumption_resolution,[],[f1197,f112])).

fof(f1197,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_67 ),
    inference(subsumption_resolution,[],[f1193,f111])).

fof(f1193,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_67 ),
    inference(resolution,[],[f1115,f177])).

fof(f177,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
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
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f87])).

fof(f87,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & m1_pre_topc(X2,X0)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t149_tmap_1.p',dt_k3_tmap_1)).

fof(f1115,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl13_67 ),
    inference(avatar_component_clause,[],[f1114])).

fof(f1114,plain,
    ( spl13_67
  <=> ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_67])])).

fof(f1182,plain,
    ( ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_60
    | spl13_71 ),
    inference(avatar_contradiction_clause,[],[f1181])).

fof(f1181,plain,
    ( $false
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_60
    | ~ spl13_71 ),
    inference(subsumption_resolution,[],[f1180,f110])).

fof(f1180,plain,
    ( v2_struct_0(sK0)
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_60
    | ~ spl13_71 ),
    inference(subsumption_resolution,[],[f1179,f189])).

fof(f1179,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_60
    | ~ spl13_71 ),
    inference(subsumption_resolution,[],[f1178,f201])).

fof(f1178,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_6
    | ~ spl13_60
    | ~ spl13_71 ),
    inference(subsumption_resolution,[],[f1177,f207])).

fof(f1177,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_60
    | ~ spl13_71 ),
    inference(subsumption_resolution,[],[f1176,f106])).

fof(f1176,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_60
    | ~ spl13_71 ),
    inference(subsumption_resolution,[],[f1175,f967])).

fof(f1175,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_71 ),
    inference(subsumption_resolution,[],[f1174,f109])).

fof(f1174,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_71 ),
    inference(subsumption_resolution,[],[f1173,f108])).

fof(f1173,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_71 ),
    inference(subsumption_resolution,[],[f1172,f107])).

fof(f1172,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_71 ),
    inference(subsumption_resolution,[],[f1171,f112])).

fof(f1171,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_71 ),
    inference(subsumption_resolution,[],[f1168,f111])).

fof(f1168,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_71 ),
    inference(resolution,[],[f1127,f176])).

fof(f176,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
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
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f1127,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl13_71 ),
    inference(avatar_component_clause,[],[f1126])).

fof(f1126,plain,
    ( spl13_71
  <=> ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_71])])).

fof(f1162,plain,
    ( ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_60
    | spl13_73 ),
    inference(avatar_contradiction_clause,[],[f1161])).

fof(f1161,plain,
    ( $false
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_60
    | ~ spl13_73 ),
    inference(subsumption_resolution,[],[f1160,f96])).

fof(f1160,plain,
    ( ~ v1_funct_1(sK4)
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_60
    | ~ spl13_73 ),
    inference(subsumption_resolution,[],[f1159,f368])).

fof(f1159,plain,
    ( ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ v1_funct_1(sK4)
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_60
    | ~ spl13_73 ),
    inference(subsumption_resolution,[],[f1158,f95])).

fof(f1158,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ v1_funct_1(sK4)
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_60
    | ~ spl13_73 ),
    inference(subsumption_resolution,[],[f1157,f93])).

fof(f1157,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ v1_funct_1(sK4)
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_60
    | ~ spl13_73 ),
    inference(subsumption_resolution,[],[f1156,f92])).

fof(f1156,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ v1_funct_1(sK4)
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_60
    | ~ spl13_73 ),
    inference(subsumption_resolution,[],[f1155,f99])).

fof(f1155,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ v1_funct_1(sK4)
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_60
    | ~ spl13_73 ),
    inference(subsumption_resolution,[],[f1154,f97])).

fof(f1154,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ v1_funct_1(sK4)
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_60
    | ~ spl13_73 ),
    inference(subsumption_resolution,[],[f1153,f111])).

fof(f1153,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ v1_funct_1(sK4)
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_60
    | ~ spl13_73 ),
    inference(subsumption_resolution,[],[f1152,f110])).

fof(f1152,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ v1_funct_1(sK4)
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_60
    | ~ spl13_73 ),
    inference(subsumption_resolution,[],[f1151,f106])).

fof(f1151,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ v1_funct_1(sK4)
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_60
    | ~ spl13_73 ),
    inference(subsumption_resolution,[],[f1150,f967])).

fof(f1150,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ v1_funct_1(sK4)
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_73 ),
    inference(subsumption_resolution,[],[f1139,f112])).

fof(f1139,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ v1_funct_1(sK4)
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_73 ),
    inference(resolution,[],[f1133,f743])).

fof(f743,plain,
    ( ! [X19,X17,X20,X18] :
        ( v1_funct_1(k3_tmap_1(X19,sK1,k1_tsep_1(sK0,sK2,sK3),X20,k10_tmap_1(sK0,sK1,sK2,sK3,X17,X18)))
        | ~ l1_pre_topc(X19)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X19)
        | ~ m1_pre_topc(X20,X19)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ v1_funct_2(X17,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X18,X17,sK3,sK2,sK1,sK0)
        | ~ v1_funct_1(X17) )
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6 ),
    inference(superposition,[],[f401,f381])).

fof(f381,plain,
    ( ! [X0,X1] :
        ( k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5) = k10_tmap_1(sK0,sK1,sK2,sK3,X0,X1)
        | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X1,X0,sK3,sK2,sK1,sK0)
        | ~ v1_funct_1(X0) )
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f380,f110])).

fof(f380,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | v2_struct_0(sK0)
        | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X1,X0,sK3,sK2,sK1,sK0)
        | k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5) = k10_tmap_1(sK0,sK1,sK2,sK3,X0,X1) )
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f379,f201])).

fof(f379,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X1,X0,sK3,sK2,sK1,sK0)
        | k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5) = k10_tmap_1(sK0,sK1,sK2,sK3,X0,X1) )
    | ~ spl13_0
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f378,f207])).

fof(f378,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X1,X0,sK3,sK2,sK1,sK0)
        | k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5) = k10_tmap_1(sK0,sK1,sK2,sK3,X0,X1) )
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f377,f103])).

fof(f377,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ r1_tsep_1(sK2,sK3)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X1,X0,sK3,sK2,sK1,sK0)
        | k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5) = k10_tmap_1(sK0,sK1,sK2,sK3,X0,X1) )
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f376,f102])).

fof(f376,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ r1_tsep_1(sK2,sK3)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X1,X0,sK3,sK2,sK1,sK0)
        | k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5) = k10_tmap_1(sK0,sK1,sK2,sK3,X0,X1) )
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f375,f100])).

fof(f375,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ r1_tsep_1(sK2,sK3)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X1,X0,sK3,sK2,sK1,sK0)
        | k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5) = k10_tmap_1(sK0,sK1,sK2,sK3,X0,X1) )
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f374,f106])).

fof(f374,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ r1_tsep_1(sK2,sK3)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X1,X0,sK3,sK2,sK1,sK0)
        | k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5) = k10_tmap_1(sK0,sK1,sK2,sK3,X0,X1) )
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f373,f104])).

fof(f373,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ r1_tsep_1(sK2,sK3)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X1,X0,sK3,sK2,sK1,sK0)
        | k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5) = k10_tmap_1(sK0,sK1,sK2,sK3,X0,X1) )
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f372,f109])).

fof(f372,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ r1_tsep_1(sK2,sK3)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X1,X0,sK3,sK2,sK1,sK0)
        | k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5) = k10_tmap_1(sK0,sK1,sK2,sK3,X0,X1) )
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f371,f108])).

fof(f371,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ r1_tsep_1(sK2,sK3)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X1,X0,sK3,sK2,sK1,sK0)
        | k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5) = k10_tmap_1(sK0,sK1,sK2,sK3,X0,X1) )
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f370,f107])).

fof(f370,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ r1_tsep_1(sK2,sK3)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X1,X0,sK3,sK2,sK1,sK0)
        | k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5) = k10_tmap_1(sK0,sK1,sK2,sK3,X0,X1) )
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f369,f112])).

fof(f369,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ r1_tsep_1(sK2,sK3)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X1,X0,sK3,sK2,sK1,sK0)
        | k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5) = k10_tmap_1(sK0,sK1,sK2,sK3,X0,X1) )
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f338,f111])).

fof(f338,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ r1_tsep_1(sK2,sK3)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X1,X0,sK3,sK2,sK1,sK0)
        | k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5) = k10_tmap_1(sK0,sK1,sK2,sK3,X0,X1) )
    | ~ spl13_0 ),
    inference(resolution,[],[f189,f132])).

fof(f132,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ r1_tsep_1(X2,X3)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | v2_struct_0(X0)
      | ~ sP7(X6,X5,X4,X3,X2,X1,X0)
      | k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f401,plain,
    ( ! [X6,X5] :
        ( v1_funct_1(k3_tmap_1(X5,sK1,k1_tsep_1(sK0,sK2,sK3),X6,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ l1_pre_topc(X5)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X5)
        | ~ m1_pre_topc(X6,X5)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(X5) )
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f400,f201])).

fof(f400,plain,
    ( ! [X6,X5] :
        ( ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X5)
        | ~ m1_pre_topc(X6,X5)
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
        | v2_struct_0(X5)
        | v1_funct_1(k3_tmap_1(X5,sK1,k1_tsep_1(sK0,sK2,sK3),X6,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) )
    | ~ spl13_0
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f399,f207])).

fof(f399,plain,
    ( ! [X6,X5] :
        ( ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X5)
        | ~ m1_pre_topc(X6,X5)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
        | v2_struct_0(X5)
        | v1_funct_1(k3_tmap_1(X5,sK1,k1_tsep_1(sK0,sK2,sK3),X6,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) )
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f398,f109])).

fof(f398,plain,
    ( ! [X6,X5] :
        ( ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X5)
        | ~ m1_pre_topc(X6,X5)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
        | v2_struct_0(X5)
        | v1_funct_1(k3_tmap_1(X5,sK1,k1_tsep_1(sK0,sK2,sK3),X6,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) )
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f397,f108])).

fof(f397,plain,
    ( ! [X6,X5] :
        ( ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X5)
        | ~ m1_pre_topc(X6,X5)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
        | v2_struct_0(X5)
        | v1_funct_1(k3_tmap_1(X5,sK1,k1_tsep_1(sK0,sK2,sK3),X6,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) )
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f342,f107])).

fof(f342,plain,
    ( ! [X6,X5] :
        ( ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),X5)
        | ~ m1_pre_topc(X6,X5)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
        | v2_struct_0(X5)
        | v1_funct_1(k3_tmap_1(X5,sK1,k1_tsep_1(sK0,sK2,sK3),X6,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) )
    | ~ spl13_0 ),
    inference(resolution,[],[f189,f175])).

fof(f175,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | v2_struct_0(X0)
      | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f1133,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl13_73 ),
    inference(avatar_component_clause,[],[f1132])).

fof(f1132,plain,
    ( spl13_73
  <=> ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_73])])).

fof(f1134,plain,
    ( ~ spl13_67
    | ~ spl13_69
    | ~ spl13_71
    | ~ spl13_73
    | ~ spl13_0
    | spl13_3
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f1109,f963,f206,f200,f197,f188,f1132,f1126,f1120,f1114])).

fof(f197,plain,
    ( spl13_3
  <=> ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f963,plain,
    ( spl13_58
  <=> k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_58])])).

fof(f1109,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl13_0
    | ~ spl13_3
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f1108,f94])).

fof(f94,plain,(
    v5_pre_topc(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f1108,plain,
    ( ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl13_0
    | ~ spl13_3
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_58 ),
    inference(forward_demodulation,[],[f1107,f964])).

fof(f964,plain,
    ( k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) = sK5
    | ~ spl13_58 ),
    inference(avatar_component_clause,[],[f963])).

fof(f1107,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | ~ spl13_0
    | ~ spl13_3
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f1106,f93])).

fof(f1106,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | ~ spl13_0
    | ~ spl13_3
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_58 ),
    inference(forward_demodulation,[],[f1105,f964])).

fof(f1105,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | ~ spl13_0
    | ~ spl13_3
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f1104,f92])).

fof(f1104,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | ~ spl13_0
    | ~ spl13_3
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_58 ),
    inference(forward_demodulation,[],[f1103,f964])).

fof(f1103,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | ~ spl13_0
    | ~ spl13_3
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f1102,f198])).

fof(f198,plain,
    ( ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl13_3 ),
    inference(avatar_component_clause,[],[f197])).

fof(f1102,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f1101,f110])).

fof(f1101,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | v2_struct_0(sK0)
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f1100,f189])).

fof(f1100,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | v2_struct_0(sK0)
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f1099,f201])).

fof(f1099,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | v2_struct_0(sK0)
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl13_6
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f1098,f207])).

fof(f1098,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | v2_struct_0(sK0)
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f1097,f102])).

fof(f1097,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | v2_struct_0(sK0)
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f1096,f101])).

fof(f101,plain,(
    v1_tsep_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f1096,plain,
    ( ~ v1_tsep_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | v2_struct_0(sK0)
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f1095,f100])).

fof(f1095,plain,
    ( v2_struct_0(sK3)
    | ~ v1_tsep_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | v2_struct_0(sK0)
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f1094,f106])).

fof(f1094,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ v1_tsep_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | v2_struct_0(sK0)
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f1093,f105])).

fof(f105,plain,(
    v1_tsep_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f1093,plain,
    ( ~ v1_tsep_1(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ v1_tsep_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | v2_struct_0(sK0)
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f1092,f104])).

fof(f1092,plain,
    ( v2_struct_0(sK2)
    | ~ v1_tsep_1(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ v1_tsep_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | v2_struct_0(sK0)
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f1091,f109])).

fof(f1091,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ v1_tsep_1(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ v1_tsep_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | v2_struct_0(sK0)
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f1090,f108])).

fof(f1090,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ v1_tsep_1(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ v1_tsep_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | v2_struct_0(sK0)
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f1089,f107])).

fof(f1089,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ v1_tsep_1(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ v1_tsep_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | v2_struct_0(sK0)
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f1088,f112])).

fof(f1088,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ v1_tsep_1(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ v1_tsep_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | v2_struct_0(sK0)
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f1087,f111])).

fof(f1087,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ v1_tsep_1(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ v1_tsep_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | v2_struct_0(sK0)
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f1080,f95])).

fof(f1080,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ v1_tsep_1(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ v1_tsep_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK2,sK1)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK3,sK1)
    | v2_struct_0(sK0)
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl13_58 ),
    inference(superposition,[],[f120,f964])).

fof(f120,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ v1_tsep_1(X2,X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ v1_tsep_1(X3,X0)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))
      | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
      | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
      | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
      | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
      | v2_struct_0(X0)
      | v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_tsep_1(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tsep_1(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_tsep_1(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tsep_1(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
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
                & v1_tsep_1(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_tsep_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t149_tmap_1.p',t128_tmap_1)).

fof(f1068,plain,
    ( ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_56 ),
    inference(avatar_contradiction_clause,[],[f1059])).

fof(f1059,plain,
    ( $false
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_56 ),
    inference(unit_resulting_resolution,[],[f111,f110,f112,f109,f96,f108,f100,f92,f107,f104,f103,f106,f102,f93,f97,f207,f95,f99,f201,f189,f958,f184])).

fof(f958,plain,
    ( ! [X9] : ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,X9,sK3,sK2,sK1,sK0)
    | ~ spl13_56 ),
    inference(avatar_component_clause,[],[f957])).

fof(f957,plain,
    ( spl13_56
  <=> ! [X9] : ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,X9,sK3,sK2,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_56])])).

fof(f1055,plain,
    ( ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_60
    | spl13_63 ),
    inference(avatar_contradiction_clause,[],[f1054])).

fof(f1054,plain,
    ( $false
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_60
    | ~ spl13_63 ),
    inference(subsumption_resolution,[],[f1053,f96])).

fof(f1053,plain,
    ( ~ v1_funct_1(sK4)
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_60
    | ~ spl13_63 ),
    inference(subsumption_resolution,[],[f1052,f368])).

fof(f1052,plain,
    ( ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ v1_funct_1(sK4)
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_60
    | ~ spl13_63 ),
    inference(subsumption_resolution,[],[f1051,f95])).

fof(f1051,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ v1_funct_1(sK4)
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_60
    | ~ spl13_63 ),
    inference(subsumption_resolution,[],[f1050,f93])).

fof(f1050,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ v1_funct_1(sK4)
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_60
    | ~ spl13_63 ),
    inference(subsumption_resolution,[],[f1049,f92])).

fof(f1049,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ v1_funct_1(sK4)
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_60
    | ~ spl13_63 ),
    inference(subsumption_resolution,[],[f1048,f99])).

fof(f1048,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ v1_funct_1(sK4)
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_60
    | ~ spl13_63 ),
    inference(subsumption_resolution,[],[f1047,f97])).

fof(f1047,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ v1_funct_1(sK4)
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_60
    | ~ spl13_63 ),
    inference(subsumption_resolution,[],[f1046,f111])).

fof(f1046,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ v1_funct_1(sK4)
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_60
    | ~ spl13_63 ),
    inference(subsumption_resolution,[],[f1045,f110])).

fof(f1045,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ v1_funct_1(sK4)
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_60
    | ~ spl13_63 ),
    inference(subsumption_resolution,[],[f1044,f102])).

fof(f1044,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ v1_funct_1(sK4)
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_60
    | ~ spl13_63 ),
    inference(subsumption_resolution,[],[f1043,f967])).

fof(f1043,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ v1_funct_1(sK4)
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_63 ),
    inference(subsumption_resolution,[],[f1032,f112])).

fof(f1032,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,sK4,sK3,sK2,sK1,sK0)
    | ~ v1_funct_1(sK4)
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_63 ),
    inference(resolution,[],[f976,f743])).

fof(f976,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
    | ~ spl13_63 ),
    inference(avatar_component_clause,[],[f975])).

fof(f975,plain,
    ( spl13_63
  <=> ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_63])])).

fof(f1013,plain,(
    spl13_61 ),
    inference(avatar_contradiction_clause,[],[f1012])).

fof(f1012,plain,
    ( $false
    | ~ spl13_61 ),
    inference(subsumption_resolution,[],[f1011,f110])).

fof(f1011,plain,
    ( v2_struct_0(sK0)
    | ~ spl13_61 ),
    inference(subsumption_resolution,[],[f1010,f102])).

fof(f1010,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl13_61 ),
    inference(subsumption_resolution,[],[f1009,f100])).

fof(f1009,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl13_61 ),
    inference(subsumption_resolution,[],[f1008,f106])).

fof(f1008,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl13_61 ),
    inference(subsumption_resolution,[],[f1007,f104])).

fof(f1007,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl13_61 ),
    inference(subsumption_resolution,[],[f1005,f112])).

fof(f1005,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | ~ spl13_61 ),
    inference(resolution,[],[f970,f168])).

fof(f168,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t149_tmap_1.p',dt_k1_tsep_1)).

fof(f970,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ spl13_61 ),
    inference(avatar_component_clause,[],[f969])).

fof(f969,plain,
    ( spl13_61
  <=> ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_61])])).

fof(f977,plain,
    ( spl13_56
    | spl13_58
    | ~ spl13_61
    | ~ spl13_63
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6 ),
    inference(avatar_split_clause,[],[f955,f206,f200,f188,f975,f969,f963,f957])).

fof(f955,plain,
    ( ! [X9] :
        ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
        | k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) = sK5
        | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,X9,sK3,sK2,sK1,sK0) )
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f954,f110])).

fof(f954,plain,
    ( ! [X9] :
        ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
        | k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) = sK5
        | v2_struct_0(sK0)
        | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,X9,sK3,sK2,sK1,sK0) )
    | ~ spl13_0
    | ~ spl13_4
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f953,f201])).

fof(f953,plain,
    ( ! [X9] :
        ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
        | k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) = sK5
        | v2_struct_0(sK0)
        | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,X9,sK3,sK2,sK1,sK0) )
    | ~ spl13_0
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f952,f207])).

fof(f952,plain,
    ( ! [X9] :
        ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
        | k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) = sK5
        | v2_struct_0(sK0)
        | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,X9,sK3,sK2,sK1,sK0) )
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f951,f102])).

fof(f951,plain,
    ( ! [X9] :
        ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
        | k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) = sK5
        | v2_struct_0(sK0)
        | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,X9,sK3,sK2,sK1,sK0) )
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f950,f112])).

fof(f950,plain,
    ( ! [X9] :
        ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
        | k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) = sK5
        | v2_struct_0(sK0)
        | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,X9,sK3,sK2,sK1,sK0) )
    | ~ spl13_0 ),
    inference(subsumption_resolution,[],[f934,f111])).

fof(f934,plain,
    ( ! [X9] :
        ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
        | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
        | k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) = sK5
        | v2_struct_0(sK0)
        | ~ sP7(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK5,X9,sK3,sK2,sK1,sK0) )
    | ~ spl13_0 ),
    inference(resolution,[],[f929,f189])).

fof(f929,plain,(
    ! [X10,X8,X7,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X7,X8,sK3)),u1_struct_0(sK1))))
      | ~ v1_funct_1(k3_tmap_1(X7,sK1,k1_tsep_1(X7,X8,sK3),sK3,X9))
      | ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | ~ m1_pre_topc(k1_tsep_1(X7,X8,sK3),X7)
      | ~ m1_pre_topc(sK3,X7)
      | ~ v1_funct_1(X9)
      | ~ v1_funct_2(X9,u1_struct_0(k1_tsep_1(X7,X8,sK3)),u1_struct_0(sK1))
      | k3_tmap_1(X7,sK1,k1_tsep_1(X7,X8,sK3),sK3,X9) = sK5
      | v2_struct_0(X7)
      | ~ sP7(X9,sK5,X10,sK3,X8,sK1,X7) ) ),
    inference(subsumption_resolution,[],[f928,f109])).

fof(f928,plain,(
    ! [X10,X8,X7,X9] :
      ( k3_tmap_1(X7,sK1,k1_tsep_1(X7,X8,sK3),sK3,X9) = sK5
      | ~ v1_funct_1(k3_tmap_1(X7,sK1,k1_tsep_1(X7,X8,sK3),sK3,X9))
      | ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | ~ m1_pre_topc(k1_tsep_1(X7,X8,sK3),X7)
      | ~ m1_pre_topc(sK3,X7)
      | ~ v1_funct_1(X9)
      | ~ v1_funct_2(X9,u1_struct_0(k1_tsep_1(X7,X8,sK3)),u1_struct_0(sK1))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X7,X8,sK3)),u1_struct_0(sK1))))
      | v2_struct_0(X7)
      | ~ sP7(X9,sK5,X10,sK3,X8,sK1,X7)
      | ~ l1_pre_topc(sK1) ) ),
    inference(subsumption_resolution,[],[f927,f108])).

fof(f927,plain,(
    ! [X10,X8,X7,X9] :
      ( k3_tmap_1(X7,sK1,k1_tsep_1(X7,X8,sK3),sK3,X9) = sK5
      | ~ v1_funct_1(k3_tmap_1(X7,sK1,k1_tsep_1(X7,X8,sK3),sK3,X9))
      | ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | ~ m1_pre_topc(k1_tsep_1(X7,X8,sK3),X7)
      | ~ m1_pre_topc(sK3,X7)
      | ~ v1_funct_1(X9)
      | ~ v1_funct_2(X9,u1_struct_0(k1_tsep_1(X7,X8,sK3)),u1_struct_0(sK1))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X7,X8,sK3)),u1_struct_0(sK1))))
      | v2_struct_0(X7)
      | ~ sP7(X9,sK5,X10,sK3,X8,sK1,X7)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1) ) ),
    inference(subsumption_resolution,[],[f916,f107])).

fof(f916,plain,(
    ! [X10,X8,X7,X9] :
      ( k3_tmap_1(X7,sK1,k1_tsep_1(X7,X8,sK3),sK3,X9) = sK5
      | ~ v1_funct_1(k3_tmap_1(X7,sK1,k1_tsep_1(X7,X8,sK3),sK3,X9))
      | ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | ~ m1_pre_topc(k1_tsep_1(X7,X8,sK3),X7)
      | ~ m1_pre_topc(sK3,X7)
      | ~ v1_funct_1(X9)
      | ~ v1_funct_2(X9,u1_struct_0(k1_tsep_1(X7,X8,sK3)),u1_struct_0(sK1))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X7,X8,sK3)),u1_struct_0(sK1))))
      | v2_struct_0(X7)
      | ~ sP7(X9,sK5,X10,sK3,X8,sK1,X7)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1) ) ),
    inference(duplicate_literal_removal,[],[f911])).

fof(f911,plain,(
    ! [X10,X8,X7,X9] :
      ( k3_tmap_1(X7,sK1,k1_tsep_1(X7,X8,sK3),sK3,X9) = sK5
      | ~ v1_funct_1(k3_tmap_1(X7,sK1,k1_tsep_1(X7,X8,sK3),sK3,X9))
      | ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | ~ m1_pre_topc(k1_tsep_1(X7,X8,sK3),X7)
      | ~ m1_pre_topc(sK3,X7)
      | ~ v1_funct_1(X9)
      | ~ v1_funct_2(X9,u1_struct_0(k1_tsep_1(X7,X8,sK3)),u1_struct_0(sK1))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X7,X8,sK3)),u1_struct_0(sK1))))
      | v2_struct_0(X7)
      | ~ sP7(X9,sK5,X10,sK3,X8,sK1,X7)
      | ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(k1_tsep_1(X7,X8,sK3),X7)
      | ~ m1_pre_topc(sK3,X7)
      | ~ v1_funct_1(X9)
      | ~ v1_funct_2(X9,u1_struct_0(k1_tsep_1(X7,X8,sK3)),u1_struct_0(sK1))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X7,X8,sK3)),u1_struct_0(sK1))))
      | v2_struct_0(X7) ) ),
    inference(resolution,[],[f890,f176])).

fof(f890,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(k3_tmap_1(X0,sK1,k1_tsep_1(X0,X1,sK3),sK3,X2),u1_struct_0(sK3),u1_struct_0(sK1))
      | k3_tmap_1(X0,sK1,k1_tsep_1(X0,X1,sK3),sK3,X2) = sK5
      | ~ v1_funct_1(k3_tmap_1(X0,sK1,k1_tsep_1(X0,X1,sK3),sK3,X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(k1_tsep_1(X0,X1,sK3),X0)
      | ~ m1_pre_topc(sK3,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,sK3)),u1_struct_0(sK1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,sK3)),u1_struct_0(sK1))))
      | v2_struct_0(X0)
      | ~ sP7(X2,sK5,X3,sK3,X1,sK1,X0) ) ),
    inference(resolution,[],[f445,f131])).

fof(f131,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
      | ~ sP7(X6,X5,X4,X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f445,plain,(
    ! [X8,X7,X9] :
      ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(X7,sK1,X8,sK3,X9),sK5)
      | ~ v1_funct_1(k3_tmap_1(X7,sK1,X8,sK3,X9))
      | k3_tmap_1(X7,sK1,X8,sK3,X9) = sK5
      | ~ v1_funct_2(k3_tmap_1(X7,sK1,X8,sK3,X9),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | ~ m1_pre_topc(X8,X7)
      | ~ m1_pre_topc(sK3,X7)
      | ~ v1_funct_1(X9)
      | ~ v1_funct_2(X9,u1_struct_0(X8),u1_struct_0(sK1))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK1))))
      | v2_struct_0(X7) ) ),
    inference(subsumption_resolution,[],[f444,f109])).

fof(f444,plain,(
    ! [X8,X7,X9] :
      ( ~ v1_funct_2(k3_tmap_1(X7,sK1,X8,sK3,X9),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(X7,sK1,X8,sK3,X9))
      | k3_tmap_1(X7,sK1,X8,sK3,X9) = sK5
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(X7,sK1,X8,sK3,X9),sK5)
      | ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(X8,X7)
      | ~ m1_pre_topc(sK3,X7)
      | ~ v1_funct_1(X9)
      | ~ v1_funct_2(X9,u1_struct_0(X8),u1_struct_0(sK1))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK1))))
      | v2_struct_0(X7) ) ),
    inference(subsumption_resolution,[],[f443,f108])).

fof(f443,plain,(
    ! [X8,X7,X9] :
      ( ~ v1_funct_2(k3_tmap_1(X7,sK1,X8,sK3,X9),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(X7,sK1,X8,sK3,X9))
      | k3_tmap_1(X7,sK1,X8,sK3,X9) = sK5
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(X7,sK1,X8,sK3,X9),sK5)
      | ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(X8,X7)
      | ~ m1_pre_topc(sK3,X7)
      | ~ v1_funct_1(X9)
      | ~ v1_funct_2(X9,u1_struct_0(X8),u1_struct_0(sK1))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK1))))
      | v2_struct_0(X7) ) ),
    inference(subsumption_resolution,[],[f431,f107])).

fof(f431,plain,(
    ! [X8,X7,X9] :
      ( ~ v1_funct_2(k3_tmap_1(X7,sK1,X8,sK3,X9),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(X7,sK1,X8,sK3,X9))
      | k3_tmap_1(X7,sK1,X8,sK3,X9) = sK5
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(X7,sK1,X8,sK3,X9),sK5)
      | ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(X8,X7)
      | ~ m1_pre_topc(sK3,X7)
      | ~ v1_funct_1(X9)
      | ~ v1_funct_2(X9,u1_struct_0(X8),u1_struct_0(sK1))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK1))))
      | v2_struct_0(X7) ) ),
    inference(resolution,[],[f245,f177])).

fof(f245,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(X5)
      | sK5 = X5
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),X5,sK5) ) ),
    inference(subsumption_resolution,[],[f244,f93])).

fof(f244,plain,(
    ! [X5] :
      ( ~ v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(X5)
      | sK5 = X5
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),X5,sK5) ) ),
    inference(subsumption_resolution,[],[f225,f92])).

fof(f225,plain,(
    ! [X5] :
      ( ~ v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(X5)
      | sK5 = X5
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),X5,sK5) ) ),
    inference(resolution,[],[f95,f174])).

fof(f336,plain,(
    spl13_1 ),
    inference(avatar_contradiction_clause,[],[f335])).

fof(f335,plain,
    ( $false
    | ~ spl13_1 ),
    inference(subsumption_resolution,[],[f334,f110])).

fof(f334,plain,
    ( v2_struct_0(sK0)
    | ~ spl13_1 ),
    inference(subsumption_resolution,[],[f333,f95])).

fof(f333,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_1 ),
    inference(subsumption_resolution,[],[f332,f93])).

fof(f332,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_1 ),
    inference(subsumption_resolution,[],[f331,f92])).

fof(f331,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_1 ),
    inference(subsumption_resolution,[],[f330,f99])).

fof(f330,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_1 ),
    inference(subsumption_resolution,[],[f329,f97])).

fof(f329,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_1 ),
    inference(subsumption_resolution,[],[f328,f96])).

fof(f328,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_1 ),
    inference(subsumption_resolution,[],[f327,f102])).

fof(f327,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_1 ),
    inference(subsumption_resolution,[],[f326,f100])).

fof(f326,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_1 ),
    inference(subsumption_resolution,[],[f325,f106])).

fof(f325,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_1 ),
    inference(subsumption_resolution,[],[f324,f104])).

fof(f324,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_1 ),
    inference(subsumption_resolution,[],[f323,f109])).

fof(f323,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_1 ),
    inference(subsumption_resolution,[],[f322,f108])).

fof(f322,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_1 ),
    inference(subsumption_resolution,[],[f321,f107])).

fof(f321,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_1 ),
    inference(subsumption_resolution,[],[f320,f112])).

fof(f320,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_1 ),
    inference(subsumption_resolution,[],[f317,f111])).

fof(f317,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_1 ),
    inference(resolution,[],[f192,f180])).

fof(f180,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f89])).

fof(f89,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t149_tmap_1.p',dt_k10_tmap_1)).

fof(f192,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ spl13_1 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl13_1
  <=> ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f315,plain,(
    spl13_5 ),
    inference(avatar_contradiction_clause,[],[f314])).

fof(f314,plain,
    ( $false
    | ~ spl13_5 ),
    inference(subsumption_resolution,[],[f313,f110])).

fof(f313,plain,
    ( v2_struct_0(sK0)
    | ~ spl13_5 ),
    inference(subsumption_resolution,[],[f312,f95])).

fof(f312,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_5 ),
    inference(subsumption_resolution,[],[f311,f93])).

fof(f311,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_5 ),
    inference(subsumption_resolution,[],[f310,f92])).

fof(f310,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_5 ),
    inference(subsumption_resolution,[],[f309,f99])).

fof(f309,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_5 ),
    inference(subsumption_resolution,[],[f308,f97])).

fof(f308,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_5 ),
    inference(subsumption_resolution,[],[f307,f96])).

fof(f307,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_5 ),
    inference(subsumption_resolution,[],[f306,f102])).

fof(f306,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_5 ),
    inference(subsumption_resolution,[],[f305,f100])).

fof(f305,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_5 ),
    inference(subsumption_resolution,[],[f304,f106])).

fof(f304,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_5 ),
    inference(subsumption_resolution,[],[f303,f104])).

fof(f303,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_5 ),
    inference(subsumption_resolution,[],[f302,f109])).

fof(f302,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_5 ),
    inference(subsumption_resolution,[],[f301,f108])).

fof(f301,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_5 ),
    inference(subsumption_resolution,[],[f300,f107])).

fof(f300,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_5 ),
    inference(subsumption_resolution,[],[f299,f112])).

fof(f299,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_5 ),
    inference(subsumption_resolution,[],[f297,f111])).

fof(f297,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | ~ spl13_5 ),
    inference(resolution,[],[f204,f179])).

fof(f179,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f204,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ spl13_5 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl13_5
  <=> ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).

fof(f295,plain,(
    spl13_7 ),
    inference(avatar_contradiction_clause,[],[f294])).

fof(f294,plain,
    ( $false
    | ~ spl13_7 ),
    inference(unit_resulting_resolution,[],[f112,f110,f108,f92,f111,f107,f96,f104,f100,f109,f102,f106,f93,f97,f95,f99,f210,f178])).

fof(f178,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | v2_struct_0(X0)
      | v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f210,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl13_7 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl13_7
  <=> ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).

fof(f211,plain,
    ( ~ spl13_1
    | ~ spl13_3
    | ~ spl13_5
    | ~ spl13_7 ),
    inference(avatar_split_clause,[],[f91,f209,f203,f197,f191])).

fof(f91,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
