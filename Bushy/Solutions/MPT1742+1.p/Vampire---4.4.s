%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t51_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:16 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  129 (11908 expanded)
%              Number of leaves         :   17 (6996 expanded)
%              Depth                    :   19
%              Number of atoms          : 1124 (262854 expanded)
%              Number of equality atoms :   39 (25507 expanded)
%              Maximal formula depth    :   24 (  10 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f589,plain,(
    $false ),
    inference(global_subsumption,[],[f547,f588])).

fof(f588,plain,(
    ~ m1_subset_1(sK8(sK1,sK2,sK3,sK5,sK7(sK0,sK2,sK3,sK5)),u1_pre_topc(sK0)) ),
    inference(unit_resulting_resolution,[],[f545,f539,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t51_tmap_1.p',t2_subset)).

fof(f539,plain,(
    ~ r2_hidden(sK8(sK1,sK2,sK3,sK5,sK7(sK0,sK2,sK3,sK5)),u1_pre_topc(sK0)) ),
    inference(unit_resulting_resolution,[],[f81,f435,f502,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t51_tmap_1.p',d5_pre_topc)).

fof(f502,plain,(
    ~ v3_pre_topc(sK8(sK1,sK2,sK3,sK5,sK7(sK0,sK2,sK3,sK5)),sK0) ),
    inference(unit_resulting_resolution,[],[f79,f80,f81,f85,f86,f87,f90,f101,f91,f92,f415,f435,f453,f218])).

fof(f218,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK7(X0,X1,X2,X3))
      | r1_tmap_1(X0,X1,X2,X3)
      | ~ r2_hidden(X3,X5)
      | ~ v3_pre_topc(X5,X0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f109,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t51_tmap_1.p',t4_subset)).

fof(f109,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X0,X1,X2,X3)
      | ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK7(X0,X1,X2,X3))
      | ~ r2_hidden(X3,X5)
      | ~ v3_pre_topc(X5,X0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r1_tmap_1(X0,X1,X2,X3)
                      | ( ! [X5] :
                            ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK7(X0,X1,X2,X3))
                            | ~ r2_hidden(X3,X5)
                            | ~ v3_pre_topc(X5,X0)
                            | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                        & r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),sK7(X0,X1,X2,X3))
                        & v3_pre_topc(sK7(X0,X1,X2,X3),X1)
                        & m1_subset_1(sK7(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1))) ) )
                    & ( ! [X6] :
                          ( ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK8(X0,X1,X2,X3,X6)),X6)
                            & r2_hidden(X3,sK8(X0,X1,X2,X3,X6))
                            & v3_pre_topc(sK8(X0,X1,X2,X3,X6),X0)
                            & m1_subset_1(sK8(X0,X1,X2,X3,X6),k1_zfmisc_1(u1_struct_0(X0))) )
                          | ~ r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X6)
                          | ~ v3_pre_topc(X6,X1)
                          | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
                      | ~ r1_tmap_1(X0,X1,X2,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f68,f70,f69])).

fof(f69,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
              | ~ r2_hidden(X3,X5)
              | ~ v3_pre_topc(X5,X0)
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X4)
          & v3_pre_topc(X4,X1)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ! [X5] :
            ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK7(X0,X1,X2,X3))
            | ~ r2_hidden(X3,X5)
            | ~ v3_pre_topc(X5,X0)
            | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),sK7(X0,X1,X2,X3))
        & v3_pre_topc(sK7(X0,X1,X2,X3),X1)
        & m1_subset_1(sK7(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X6,X3,X2,X1,X0] :
      ( ? [X7] :
          ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X7),X6)
          & r2_hidden(X3,X7)
          & v3_pre_topc(X7,X0)
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK8(X0,X1,X2,X3,X6)),X6)
        & r2_hidden(X3,sK8(X0,X1,X2,X3,X6))
        & v3_pre_topc(sK8(X0,X1,X2,X3,X6),X0)
        & m1_subset_1(sK8(X0,X1,X2,X3,X6),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r1_tmap_1(X0,X1,X2,X3)
                      | ? [X4] :
                          ( ! [X5] :
                              ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                              | ~ r2_hidden(X3,X5)
                              | ~ v3_pre_topc(X5,X0)
                              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                          & r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X4)
                          & v3_pre_topc(X4,X1)
                          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) ) )
                    & ( ! [X6] :
                          ( ? [X7] :
                              ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X7),X6)
                              & r2_hidden(X3,X7)
                              & v3_pre_topc(X7,X0)
                              & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
                          | ~ r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X6)
                          | ~ v3_pre_topc(X6,X1)
                          | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) )
                      | ~ r1_tmap_1(X0,X1,X2,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r1_tmap_1(X0,X1,X2,X3)
                      | ? [X4] :
                          ( ! [X5] :
                              ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                              | ~ r2_hidden(X3,X5)
                              | ~ v3_pre_topc(X5,X0)
                              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                          & r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X4)
                          & v3_pre_topc(X4,X1)
                          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) ) )
                    & ( ! [X4] :
                          ( ? [X5] :
                              ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                              & r2_hidden(X3,X5)
                              & v3_pre_topc(X5,X0)
                              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                          | ~ r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X4)
                          | ~ v3_pre_topc(X4,X1)
                          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                      | ~ r1_tmap_1(X0,X1,X2,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r1_tmap_1(X0,X1,X2,X3)
                  <=> ! [X4] :
                        ( ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & r2_hidden(X3,X5)
                            & v3_pre_topc(X5,X0)
                            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X4)
                        | ~ v3_pre_topc(X4,X1)
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r1_tmap_1(X0,X1,X2,X3)
                  <=> ! [X4] :
                        ( ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & r2_hidden(X3,X5)
                            & v3_pre_topc(X5,X0)
                            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X4)
                        | ~ v3_pre_topc(X4,X1)
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
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
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_tmap_1(X0,X1,X2,X3)
                  <=> ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ~ ( ! [X5] :
                                ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
                               => ~ ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                                    & r2_hidden(X3,X5)
                                    & v3_pre_topc(X5,X0) ) )
                            & r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X4)
                            & v3_pre_topc(X4,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t51_tmap_1.p',t48_tmap_1)).

fof(f453,plain,(
    r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK2),sK3,sK8(sK1,sK2,sK3,sK5,sK7(sK0,sK2,sK3,sK5))),sK7(sK0,sK2,sK3,sK5)) ),
    inference(unit_resulting_resolution,[],[f85,f86,f87,f90,f97,f336,f91,f170,f182,f197,f92,f294])).

fof(f294,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k3_funct_2(u1_struct_0(sK0),u1_struct_0(X0),X1,X2),X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,sK8(sK1,X0,X1,X2,X3)),X3)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tmap_1(sK1,X0,X1,X2)
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f293,f88])).

fof(f88,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,
    ( ~ r1_tmap_1(sK0,sK2,sK3,sK5)
    & r1_tmap_1(sK1,sK2,sK4,sK6)
    & sK5 = sK6
    & m1_subset_1(sK6,u1_struct_0(sK1))
    & m1_subset_1(sK5,u1_struct_0(sK0))
    & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    & v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2))
    & v1_funct_1(sK3)
    & r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0))
    & u1_struct_0(sK0) = u1_struct_0(sK1)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f36,f65,f64,f63,f62,f61,f60,f59])).

fof(f59,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ~ r1_tmap_1(X0,X2,X3,X5)
                                & r1_tmap_1(X1,X2,X4,X6)
                                & X5 = X6
                                & m1_subset_1(X6,u1_struct_0(X1)) )
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_funct_2(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X2),X3,X4)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                        & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                        & v1_funct_1(X4) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                    & v1_funct_1(X3) )
                & r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
                & u1_struct_0(X0) = u1_struct_0(X1)
                & l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(sK0,X2,X3,X5)
                              & r1_tmap_1(X1,X2,X4,X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X1)) )
                          & m1_subset_1(X5,u1_struct_0(sK0)) )
                      & r1_funct_2(u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X2),X3,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
                  & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X1),u1_pre_topc(sK0))
              & u1_struct_0(sK0) = u1_struct_0(X1)
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X0,X2,X3,X5)
                              & r1_tmap_1(X1,X2,X4,X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X1)) )
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & r1_funct_2(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X2),X3,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
              & u1_struct_0(X0) = u1_struct_0(X1)
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ~ r1_tmap_1(X0,X2,X3,X5)
                            & r1_tmap_1(sK1,X2,X4,X6)
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(sK1)) )
                        & m1_subset_1(X5,u1_struct_0(X0)) )
                    & r1_funct_2(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(sK1),u1_struct_0(X2),X3,X4)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X2))))
                    & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(X2))
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                & v1_funct_1(X3) )
            & r1_tarski(u1_pre_topc(sK1),u1_pre_topc(X0))
            & u1_struct_0(sK1) = u1_struct_0(X0)
            & l1_pre_topc(X2)
            & v2_pre_topc(X2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ r1_tmap_1(X0,X2,X3,X5)
                          & r1_tmap_1(X1,X2,X4,X6)
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X1)) )
                      & m1_subset_1(X5,u1_struct_0(X0)) )
                  & r1_funct_2(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X2),X3,X4)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                  & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
              & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
              & v1_funct_1(X3) )
          & r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
          & u1_struct_0(X0) = u1_struct_0(X1)
          & l1_pre_topc(X2)
          & v2_pre_topc(X2)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ r1_tmap_1(X0,sK2,X3,X5)
                        & r1_tmap_1(X1,sK2,X4,X6)
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(X1)) )
                    & m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_funct_2(u1_struct_0(X0),u1_struct_0(sK2),u1_struct_0(X1),u1_struct_0(sK2),X3,X4)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
                & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(sK2))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
            & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(sK2))
            & v1_funct_1(X3) )
        & r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
        & u1_struct_0(X0) = u1_struct_0(X1)
        & l1_pre_topc(sK2)
        & v2_pre_topc(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ r1_tmap_1(X0,X2,X3,X5)
                      & r1_tmap_1(X1,X2,X4,X6)
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(X1)) )
                  & m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X2),X3,X4)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
              & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
          & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
          & v1_funct_1(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ r1_tmap_1(X0,X2,sK3,X5)
                    & r1_tmap_1(X1,X2,X4,X6)
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(X1)) )
                & m1_subset_1(X5,u1_struct_0(X0)) )
            & r1_funct_2(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X2),sK3,X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
            & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
            & v1_funct_1(X4) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
        & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X2))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ r1_tmap_1(X0,X2,X3,X5)
                  & r1_tmap_1(X1,X2,X4,X6)
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(X1)) )
              & m1_subset_1(X5,u1_struct_0(X0)) )
          & r1_funct_2(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X2),X3,X4)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
          & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ~ r1_tmap_1(X0,X2,X3,X5)
                & r1_tmap_1(X1,X2,sK4,X6)
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(X1)) )
            & m1_subset_1(X5,u1_struct_0(X0)) )
        & r1_funct_2(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X2),X3,sK4)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        & v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X2))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_tmap_1(X0,X2,X3,X5)
              & r1_tmap_1(X1,X2,X4,X6)
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(X1)) )
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ? [X6] :
            ( ~ r1_tmap_1(X0,X2,X3,sK5)
            & r1_tmap_1(X1,X2,X4,X6)
            & sK5 = X6
            & m1_subset_1(X6,u1_struct_0(X1)) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ~ r1_tmap_1(X0,X2,X3,X5)
          & r1_tmap_1(X1,X2,X4,X6)
          & X5 = X6
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( ~ r1_tmap_1(X0,X2,X3,X5)
        & r1_tmap_1(X1,X2,X4,sK6)
        & sK6 = X5
        & m1_subset_1(sK6,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X0,X2,X3,X5)
                              & r1_tmap_1(X1,X2,X4,X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X1)) )
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & r1_funct_2(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X2),X3,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
              & u1_struct_0(X0) = u1_struct_0(X1)
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X0,X2,X3,X5)
                              & r1_tmap_1(X1,X2,X4,X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X1)) )
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & r1_funct_2(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X2),X3,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
              & u1_struct_0(X0) = u1_struct_0(X1)
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
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
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2)
                  & ~ v2_struct_0(X2) )
               => ( ( r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
                    & u1_struct_0(X0) = u1_struct_0(X1) )
                 => ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                        & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                        & v1_funct_1(X3) )
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                            & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                            & v1_funct_1(X4) )
                         => ( r1_funct_2(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X2),X3,X4)
                           => ! [X5] :
                                ( m1_subset_1(X5,u1_struct_0(X0))
                               => ! [X6] :
                                    ( m1_subset_1(X6,u1_struct_0(X1))
                                   => ( ( r1_tmap_1(X1,X2,X4,X6)
                                        & X5 = X6 )
                                     => r1_tmap_1(X0,X2,X3,X5) ) ) ) ) ) ) ) ) ) ) ),
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
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ( ( r1_tarski(u1_pre_topc(X1),u1_pre_topc(X0))
                  & u1_struct_0(X0) = u1_struct_0(X1) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                      & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                          & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                          & v1_funct_1(X4) )
                       => ( r1_funct_2(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X2),X3,X4)
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X0))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X1))
                                 => ( ( r1_tmap_1(X1,X2,X4,X6)
                                      & X5 = X6 )
                                   => r1_tmap_1(X0,X2,X3,X5) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t51_tmap_1.p',t51_tmap_1)).

fof(f293,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,sK8(sK1,X0,X1,X2,X3)),X3)
      | ~ r2_hidden(k3_funct_2(u1_struct_0(sK0),u1_struct_0(X0),X1,X2),X3)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tmap_1(sK1,X0,X1,X2)
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f292,f88])).

fof(f292,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,sK8(sK1,X0,X1,X2,X3)),X3)
      | ~ r2_hidden(k3_funct_2(u1_struct_0(sK0),u1_struct_0(X0),X1,X2),X3)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tmap_1(sK1,X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f291,f88])).

fof(f291,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1,sK8(sK1,X0,X1,X2,X3)),X3)
      | ~ r2_hidden(k3_funct_2(u1_struct_0(sK0),u1_struct_0(X0),X1,X2),X3)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tmap_1(sK1,X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f290,f88])).

fof(f290,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k3_funct_2(u1_struct_0(sK0),u1_struct_0(X0),X1,X2),X3)
      | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(X0),X1,sK8(sK1,X0,X1,X2,X3)),X3)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tmap_1(sK1,X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f289,f82])).

fof(f82,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f289,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k3_funct_2(u1_struct_0(sK0),u1_struct_0(X0),X1,X2),X3)
      | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(X0),X1,sK8(sK1,X0,X1,X2,X3)),X3)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tmap_1(sK1,X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f288,f83])).

fof(f83,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f288,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k3_funct_2(u1_struct_0(sK0),u1_struct_0(X0),X1,X2),X3)
      | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(X0),X1,sK8(sK1,X0,X1,X2,X3)),X3)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tmap_1(sK1,X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f286,f84])).

fof(f84,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f286,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k3_funct_2(u1_struct_0(sK0),u1_struct_0(X0),X1,X2),X3)
      | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(X0),X1,sK8(sK1,X0,X1,X2,X3)),X3)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tmap_1(sK1,X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(superposition,[],[f105,f88])).

fof(f105,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( ~ r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X6)
      | r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK8(X0,X1,X2,X3,X6)),X6)
      | ~ v3_pre_topc(X6,X1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tmap_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f197,plain,(
    r2_hidden(k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK2),sK3,sK5),sK7(sK0,sK2,sK3,sK5)) ),
    inference(unit_resulting_resolution,[],[f79,f80,f81,f85,f86,f87,f90,f97,f101,f91,f92,f108])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),sK7(X0,X1,X2,X3))
      | r1_tmap_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f182,plain,(
    m1_subset_1(sK7(sK0,sK2,sK3,sK5),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unit_resulting_resolution,[],[f79,f80,f81,f85,f86,f87,f90,f97,f101,f91,f92,f106])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | m1_subset_1(sK7(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_tmap_1(X0,X1,X2,X3)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f170,plain,(
    v3_pre_topc(sK7(sK0,sK2,sK3,sK5),sK2) ),
    inference(unit_resulting_resolution,[],[f79,f80,f81,f85,f86,f87,f90,f97,f101,f91,f92,f107])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v3_pre_topc(sK7(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_tmap_1(X0,X1,X2,X3)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f336,plain,(
    r1_tmap_1(sK1,sK2,sK3,sK5) ),
    inference(backward_demodulation,[],[f313,f134])).

fof(f134,plain,(
    r1_tmap_1(sK1,sK2,sK4,sK5) ),
    inference(forward_demodulation,[],[f100,f99])).

fof(f99,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f66])).

fof(f100,plain,(
    r1_tmap_1(sK1,sK2,sK4,sK6) ),
    inference(cnf_transformation,[],[f66])).

fof(f313,plain,(
    sK3 = sK4 ),
    inference(unit_resulting_resolution,[],[f90,f93,f307,f135,f136,f137,f91,f92,f307,f110])).

fof(f110,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
      | X4 = X5
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
          | X4 != X5 )
        & ( X4 = X5
          | ~ r1_funct_2(X0,X1,X2,X3,X4,X5) ) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t51_tmap_1.p',redefinition_r1_funct_2)).

fof(f137,plain,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),u1_struct_0(sK2),sK3,sK4) ),
    inference(forward_demodulation,[],[f96,f88])).

fof(f96,plain,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK2),sK3,sK4) ),
    inference(cnf_transformation,[],[f66])).

fof(f136,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) ),
    inference(forward_demodulation,[],[f95,f88])).

fof(f95,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f66])).

fof(f135,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f94,f88])).

fof(f94,plain,(
    v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f66])).

fof(f307,plain,(
    ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f182,f197,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t51_tmap_1.p',t5_subset)).

fof(f93,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f66])).

fof(f97,plain,(
    m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f66])).

fof(f415,plain,(
    r2_hidden(sK5,sK8(sK1,sK2,sK3,sK5,sK7(sK0,sK2,sK3,sK5))) ),
    inference(unit_resulting_resolution,[],[f85,f86,f87,f90,f97,f336,f91,f170,f182,f197,f92,f264])).

fof(f264,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k3_funct_2(u1_struct_0(sK0),u1_struct_0(X0),X1,X2),X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | r2_hidden(X2,sK8(sK1,X0,X1,X2,X3))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tmap_1(sK1,X0,X1,X2)
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f263,f88])).

fof(f263,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(k3_funct_2(u1_struct_0(sK0),u1_struct_0(X0),X1,X2),X3)
      | r2_hidden(X2,sK8(sK1,X0,X1,X2,X3))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tmap_1(sK1,X0,X1,X2)
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f262,f88])).

fof(f262,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(k3_funct_2(u1_struct_0(sK0),u1_struct_0(X0),X1,X2),X3)
      | r2_hidden(X2,sK8(sK1,X0,X1,X2,X3))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tmap_1(sK1,X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f261,f88])).

fof(f261,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k3_funct_2(u1_struct_0(sK0),u1_struct_0(X0),X1,X2),X3)
      | r2_hidden(X2,sK8(sK1,X0,X1,X2,X3))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tmap_1(sK1,X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f260,f82])).

fof(f260,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k3_funct_2(u1_struct_0(sK0),u1_struct_0(X0),X1,X2),X3)
      | r2_hidden(X2,sK8(sK1,X0,X1,X2,X3))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tmap_1(sK1,X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f259,f83])).

fof(f259,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k3_funct_2(u1_struct_0(sK0),u1_struct_0(X0),X1,X2),X3)
      | r2_hidden(X2,sK8(sK1,X0,X1,X2,X3))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tmap_1(sK1,X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f257,f84])).

fof(f257,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k3_funct_2(u1_struct_0(sK0),u1_struct_0(X0),X1,X2),X3)
      | r2_hidden(X2,sK8(sK1,X0,X1,X2,X3))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tmap_1(sK1,X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(superposition,[],[f104,f88])).

fof(f104,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( ~ r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X6)
      | r2_hidden(X3,sK8(X0,X1,X2,X3,X6))
      | ~ v3_pre_topc(X6,X1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tmap_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f92,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f66])).

fof(f91,plain,(
    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f66])).

fof(f101,plain,(
    ~ r1_tmap_1(sK0,sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f66])).

fof(f90,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f66])).

fof(f87,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f66])).

fof(f86,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f66])).

fof(f85,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f66])).

fof(f80,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f66])).

fof(f79,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f66])).

fof(f435,plain,(
    m1_subset_1(sK8(sK1,sK2,sK3,sK5,sK7(sK0,sK2,sK3,sK5)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f85,f86,f87,f90,f97,f336,f91,f170,f182,f197,f92,f279])).

fof(f279,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k3_funct_2(u1_struct_0(sK0),u1_struct_0(X0),X1,X2),X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | m1_subset_1(sK8(sK1,X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tmap_1(sK1,X0,X1,X2)
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f278,f88])).

fof(f278,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | m1_subset_1(sK8(sK1,X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(k3_funct_2(u1_struct_0(sK0),u1_struct_0(X0),X1,X2),X3)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tmap_1(sK1,X0,X1,X2)
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f277,f88])).

fof(f277,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | m1_subset_1(sK8(sK1,X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(k3_funct_2(u1_struct_0(sK0),u1_struct_0(X0),X1,X2),X3)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tmap_1(sK1,X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f276,f88])).

fof(f276,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK8(sK1,X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(k3_funct_2(u1_struct_0(sK0),u1_struct_0(X0),X1,X2),X3)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tmap_1(sK1,X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f275,f88])).

fof(f275,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k3_funct_2(u1_struct_0(sK0),u1_struct_0(X0),X1,X2),X3)
      | m1_subset_1(sK8(sK1,X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tmap_1(sK1,X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f274,f82])).

fof(f274,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k3_funct_2(u1_struct_0(sK0),u1_struct_0(X0),X1,X2),X3)
      | m1_subset_1(sK8(sK1,X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tmap_1(sK1,X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f273,f83])).

fof(f273,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k3_funct_2(u1_struct_0(sK0),u1_struct_0(X0),X1,X2),X3)
      | m1_subset_1(sK8(sK1,X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tmap_1(sK1,X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f271,f84])).

fof(f271,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k3_funct_2(u1_struct_0(sK0),u1_struct_0(X0),X1,X2),X3)
      | m1_subset_1(sK8(sK1,X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tmap_1(sK1,X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(superposition,[],[f102,f88])).

fof(f102,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( ~ r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X6)
      | m1_subset_1(sK8(X0,X1,X2,X3,X6),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X6,X1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tmap_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f81,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f66])).

fof(f545,plain,(
    ~ v1_xboole_0(u1_pre_topc(sK0)) ),
    inference(unit_resulting_resolution,[],[f141,f494,f121])).

fof(f494,plain,(
    r2_hidden(sK8(sK1,sK2,sK3,sK5,sK7(sK0,sK2,sK3,sK5)),u1_pre_topc(sK1)) ),
    inference(unit_resulting_resolution,[],[f399,f435,f161])).

fof(f161,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK1)
      | r2_hidden(X0,u1_pre_topc(sK1)) ) ),
    inference(subsumption_resolution,[],[f160,f84])).

fof(f160,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK1)
      | r2_hidden(X0,u1_pre_topc(sK1))
      | ~ l1_pre_topc(sK1) ) ),
    inference(superposition,[],[f128,f88])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f399,plain,(
    v3_pre_topc(sK8(sK1,sK2,sK3,sK5,sK7(sK0,sK2,sK3,sK5)),sK1) ),
    inference(unit_resulting_resolution,[],[f85,f86,f87,f90,f97,f336,f91,f170,f182,f197,f92,f244])).

fof(f244,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k3_funct_2(u1_struct_0(sK0),u1_struct_0(X0),X1,X2),X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | v3_pre_topc(sK8(sK1,X0,X1,X2,X3),sK1)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tmap_1(sK1,X0,X1,X2)
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f243,f88])).

fof(f243,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(k3_funct_2(u1_struct_0(sK0),u1_struct_0(X0),X1,X2),X3)
      | v3_pre_topc(sK8(sK1,X0,X1,X2,X3),sK1)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tmap_1(sK1,X0,X1,X2)
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f242,f88])).

fof(f242,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(k3_funct_2(u1_struct_0(sK0),u1_struct_0(X0),X1,X2),X3)
      | v3_pre_topc(sK8(sK1,X0,X1,X2,X3),sK1)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tmap_1(sK1,X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f241,f88])).

fof(f241,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k3_funct_2(u1_struct_0(sK0),u1_struct_0(X0),X1,X2),X3)
      | v3_pre_topc(sK8(sK1,X0,X1,X2,X3),sK1)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tmap_1(sK1,X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f240,f82])).

fof(f240,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k3_funct_2(u1_struct_0(sK0),u1_struct_0(X0),X1,X2),X3)
      | v3_pre_topc(sK8(sK1,X0,X1,X2,X3),sK1)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tmap_1(sK1,X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f239,f83])).

fof(f239,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k3_funct_2(u1_struct_0(sK0),u1_struct_0(X0),X1,X2),X3)
      | v3_pre_topc(sK8(sK1,X0,X1,X2,X3),sK1)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tmap_1(sK1,X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f237,f84])).

fof(f237,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k3_funct_2(u1_struct_0(sK0),u1_struct_0(X0),X1,X2),X3)
      | v3_pre_topc(sK8(sK1,X0,X1,X2,X3),sK1)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tmap_1(sK1,X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(superposition,[],[f103,f88])).

fof(f103,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( ~ r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X6)
      | v3_pre_topc(sK8(X0,X1,X2,X3,X6),X0)
      | ~ v3_pre_topc(X6,X1)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tmap_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f141,plain,(
    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(u1_pre_topc(sK0))) ),
    inference(unit_resulting_resolution,[],[f89,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t51_tmap_1.p',t3_subset)).

fof(f89,plain,(
    r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0)) ),
    inference(cnf_transformation,[],[f66])).

fof(f547,plain,(
    m1_subset_1(sK8(sK1,sK2,sK3,sK5,sK7(sK0,sK2,sK3,sK5)),u1_pre_topc(sK0)) ),
    inference(unit_resulting_resolution,[],[f141,f494,f122])).
%------------------------------------------------------------------------------
