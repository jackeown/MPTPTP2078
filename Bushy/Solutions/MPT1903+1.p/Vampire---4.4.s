%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t71_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:56 EDT 2019

% Result     : Theorem 75.99s
% Output     : Refutation 75.99s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 463 expanded)
%              Number of leaves         :   17 ( 129 expanded)
%              Depth                    :   13
%              Number of atoms          :  338 (1809 expanded)
%              Number of equality atoms :   45 ( 231 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7088,plain,(
    $false ),
    inference(subsumption_resolution,[],[f7087,f322])).

fof(f322,plain,(
    ~ v4_pre_topc(sK1(sK0),g1_pre_topc(u1_struct_0(sK0),k1_tex_1(u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f153,f155,f162,f284])).

fof(f284,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,g1_pre_topc(X0,k1_tex_1(X0)))
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_xboole_0 = X1 ) ),
    inference(forward_demodulation,[],[f273,f265])).

fof(f265,plain,(
    ! [X0] : u1_struct_0(g1_pre_topc(X0,k1_tex_1(X0))) = X0 ),
    inference(unit_resulting_resolution,[],[f146,f158,f111])).

fof(f111,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t71_tex_2.p',free_g1_pre_topc)).

fof(f158,plain,(
    ! [X0] : g1_pre_topc(X0,k1_tex_1(X0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(X0,k1_tex_1(X0))),u1_pre_topc(g1_pre_topc(X0,k1_tex_1(X0)))) ),
    inference(unit_resulting_resolution,[],[f124,f127,f101])).

fof(f101,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t71_tex_2.p',abstractness_v1_pre_topc)).

fof(f127,plain,(
    ! [X0] : l1_pre_topc(g1_pre_topc(X0,k1_tex_1(X0))) ),
    inference(definition_unfolding,[],[f108,f116])).

fof(f116,plain,(
    ! [X0] : g1_pre_topc(X0,k1_tex_1(X0)) = k2_tex_1(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : g1_pre_topc(X0,k1_tex_1(X0)) = k2_tex_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t71_tex_2.p',d3_tex_1)).

fof(f108,plain,(
    ! [X0] : l1_pre_topc(k2_tex_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : l1_pre_topc(k2_tex_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t71_tex_2.p',dt_k2_tex_1)).

fof(f124,plain,(
    ! [X0] : v1_pre_topc(g1_pre_topc(X0,k1_tex_1(X0))) ),
    inference(definition_unfolding,[],[f84,f116])).

fof(f84,plain,(
    ! [X0] : v1_pre_topc(k2_tex_1(X0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( v2_tdlat_3(k2_tex_1(X0))
      & v2_pre_topc(k2_tex_1(X0))
      & v1_pre_topc(k2_tex_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t71_tex_2.p',fc2_tex_1)).

fof(f146,plain,(
    ! [X0] : m1_subset_1(u1_pre_topc(g1_pre_topc(X0,k1_tex_1(X0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(X0,k1_tex_1(X0)))))) ),
    inference(unit_resulting_resolution,[],[f127,f102])).

fof(f102,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t71_tex_2.p',dt_u1_pre_topc)).

fof(f273,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X0,k1_tex_1(X0)))))
      | ~ v4_pre_topc(X1,g1_pre_topc(X0,k1_tex_1(X0)))
      | k1_xboole_0 = X1 ) ),
    inference(backward_demodulation,[],[f265,f195])).

fof(f195,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X0,k1_tex_1(X0)))))
      | ~ v4_pre_topc(X1,g1_pre_topc(X0,k1_tex_1(X0)))
      | k1_xboole_0 = X1
      | u1_struct_0(g1_pre_topc(X0,k1_tex_1(X0))) = X1 ) ),
    inference(subsumption_resolution,[],[f194,f123])).

fof(f123,plain,(
    ! [X0] : v2_pre_topc(g1_pre_topc(X0,k1_tex_1(X0))) ),
    inference(definition_unfolding,[],[f85,f116])).

fof(f85,plain,(
    ! [X0] : v2_pre_topc(k2_tex_1(X0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f194,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X0,k1_tex_1(X0)))))
      | ~ v4_pre_topc(X1,g1_pre_topc(X0,k1_tex_1(X0)))
      | k1_xboole_0 = X1
      | u1_struct_0(g1_pre_topc(X0,k1_tex_1(X0))) = X1
      | ~ v2_pre_topc(g1_pre_topc(X0,k1_tex_1(X0))) ) ),
    inference(subsumption_resolution,[],[f193,f127])).

fof(f193,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(g1_pre_topc(X0,k1_tex_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X0,k1_tex_1(X0)))))
      | ~ v4_pre_topc(X1,g1_pre_topc(X0,k1_tex_1(X0)))
      | k1_xboole_0 = X1
      | u1_struct_0(g1_pre_topc(X0,k1_tex_1(X0))) = X1
      | ~ v2_pre_topc(g1_pre_topc(X0,k1_tex_1(X0))) ) ),
    inference(resolution,[],[f79,f122])).

fof(f122,plain,(
    ! [X0] : v2_tdlat_3(g1_pre_topc(X0,k1_tex_1(X0))) ),
    inference(definition_unfolding,[],[f86,f116])).

fof(f86,plain,(
    ! [X0] : v2_tdlat_3(k2_tex_1(X0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k1_xboole_0 = X1
      | u1_struct_0(X0) = X1
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
      <=> ! [X1] :
            ( u1_struct_0(X0) = X1
            | k1_xboole_0 = X1
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
      <=> ! [X1] :
            ( u1_struct_0(X0) = X1
            | k1_xboole_0 = X1
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ~ ( u1_struct_0(X0) != X1
                & k1_xboole_0 != X1
                & v4_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t71_tex_2.p',t21_tdlat_3)).

fof(f162,plain,(
    m1_subset_1(sK1(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f78,f76,f77,f80])).

fof(f80,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f77,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ? [X0] :
      ( ~ v2_tdlat_3(X0)
      & ! [X1] :
          ( ! [X2] :
              ( v5_pre_topc(X2,X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ? [X0] :
      ( ~ v2_tdlat_3(X0)
      & ! [X1] :
          ( ! [X2] :
              ( v5_pre_topc(X2,X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( ! [X1] :
              ( ( l1_pre_topc(X1)
                & v2_pre_topc(X1)
                & ~ v2_struct_0(X1) )
             => ! [X2] :
                  ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X2) )
                 => v5_pre_topc(X2,X1,X0) ) )
         => v2_tdlat_3(X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X2) )
               => v5_pre_topc(X2,X1,X0) ) )
       => v2_tdlat_3(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t71_tex_2.p',t71_tex_2)).

fof(f76,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f78,plain,(
    ~ v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f155,plain,(
    u1_struct_0(sK0) != sK1(sK0) ),
    inference(unit_resulting_resolution,[],[f78,f76,f77,f83])).

fof(f83,plain,(
    ! [X0] :
      ( u1_struct_0(X0) != sK1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f153,plain,(
    k1_xboole_0 != sK1(sK0) ),
    inference(unit_resulting_resolution,[],[f78,f76,f77,f82])).

fof(f82,plain,(
    ! [X0] :
      ( k1_xboole_0 != sK1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f7087,plain,(
    v4_pre_topc(sK1(sK0),g1_pre_topc(u1_struct_0(sK0),k1_tex_1(u1_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f7085,f166])).

fof(f166,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k6_relat_1(u1_struct_0(sK0)),sK1(sK0)) = sK1(sK0) ),
    inference(unit_resulting_resolution,[],[f162,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f113,f114])).

fof(f114,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t71_tex_2.p',redefinition_k6_partfun1)).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t71_tex_2.p',t171_funct_2)).

fof(f7085,plain,(
    v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k6_relat_1(u1_struct_0(sK0)),sK1(sK0)),g1_pre_topc(u1_struct_0(sK0),k1_tex_1(u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f77,f152,f162,f104,f172,f1717,f125,f439])).

fof(f439,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ v1_funct_1(X9)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X8,u1_struct_0(X10))))
      | ~ v1_funct_2(X9,X8,u1_struct_0(X10))
      | ~ l1_pre_topc(X10)
      | v4_pre_topc(k8_relset_1(X8,u1_struct_0(X10),X9,X11),g1_pre_topc(X8,k1_tex_1(X8)))
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
      | ~ v4_pre_topc(X11,X10)
      | ~ v5_pre_topc(X9,g1_pre_topc(X8,k1_tex_1(X8)),X10) ) ),
    inference(forward_demodulation,[],[f438,f265])).

fof(f438,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X8,u1_struct_0(X10))))
      | ~ v1_funct_2(X9,X8,u1_struct_0(X10))
      | ~ l1_pre_topc(X10)
      | ~ v1_funct_1(X9)
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
      | ~ v4_pre_topc(X11,X10)
      | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(X8,k1_tex_1(X8))),u1_struct_0(X10),X9,X11),g1_pre_topc(X8,k1_tex_1(X8)))
      | ~ v5_pre_topc(X9,g1_pre_topc(X8,k1_tex_1(X8)),X10) ) ),
    inference(forward_demodulation,[],[f437,f265])).

fof(f437,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ v1_funct_2(X9,X8,u1_struct_0(X10))
      | ~ l1_pre_topc(X10)
      | ~ v1_funct_1(X9)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X8,k1_tex_1(X8))),u1_struct_0(X10))))
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
      | ~ v4_pre_topc(X11,X10)
      | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(X8,k1_tex_1(X8))),u1_struct_0(X10),X9,X11),g1_pre_topc(X8,k1_tex_1(X8)))
      | ~ v5_pre_topc(X9,g1_pre_topc(X8,k1_tex_1(X8)),X10) ) ),
    inference(subsumption_resolution,[],[f424,f127])).

fof(f424,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ v1_funct_2(X9,X8,u1_struct_0(X10))
      | ~ l1_pre_topc(X10)
      | ~ v1_funct_1(X9)
      | ~ l1_pre_topc(g1_pre_topc(X8,k1_tex_1(X8)))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X8,k1_tex_1(X8))),u1_struct_0(X10))))
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
      | ~ v4_pre_topc(X11,X10)
      | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(X8,k1_tex_1(X8))),u1_struct_0(X10),X9,X11),g1_pre_topc(X8,k1_tex_1(X8)))
      | ~ v5_pre_topc(X9,g1_pre_topc(X8,k1_tex_1(X8)),X10) ) ),
    inference(superposition,[],[f87,f265])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(X3,X1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
      | ~ v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( v4_pre_topc(X3,X1)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t71_tex_2.p',d12_pre_topc)).

fof(f125,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f99,f114])).

fof(f99,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t71_tex_2.p',dt_k6_partfun1)).

fof(f1717,plain,(
    v5_pre_topc(k6_relat_1(u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),k1_tex_1(u1_struct_0(sK0))),sK0) ),
    inference(unit_resulting_resolution,[],[f104,f134,f172,f125,f432])).

fof(f432,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(X1,g1_pre_topc(X0,k1_tex_1(X0)),sK0)
      | ~ v1_funct_2(X1,X0,u1_struct_0(sK0))
      | ~ v1_funct_1(X1)
      | v2_struct_0(g1_pre_topc(X0,k1_tex_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK0)))) ) ),
    inference(forward_demodulation,[],[f431,f265])).

fof(f431,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,u1_struct_0(sK0))
      | ~ v1_funct_1(X1)
      | v2_struct_0(g1_pre_topc(X0,k1_tex_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X0,k1_tex_1(X0))),u1_struct_0(sK0))))
      | v5_pre_topc(X1,g1_pre_topc(X0,k1_tex_1(X0)),sK0) ) ),
    inference(subsumption_resolution,[],[f430,f127])).

fof(f430,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,u1_struct_0(sK0))
      | ~ l1_pre_topc(g1_pre_topc(X0,k1_tex_1(X0)))
      | ~ v1_funct_1(X1)
      | v2_struct_0(g1_pre_topc(X0,k1_tex_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X0,k1_tex_1(X0))),u1_struct_0(sK0))))
      | v5_pre_topc(X1,g1_pre_topc(X0,k1_tex_1(X0)),sK0) ) ),
    inference(subsumption_resolution,[],[f421,f123])).

fof(f421,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,u1_struct_0(sK0))
      | ~ v2_pre_topc(g1_pre_topc(X0,k1_tex_1(X0)))
      | ~ l1_pre_topc(g1_pre_topc(X0,k1_tex_1(X0)))
      | ~ v1_funct_1(X1)
      | v2_struct_0(g1_pre_topc(X0,k1_tex_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X0,k1_tex_1(X0))),u1_struct_0(sK0))))
      | v5_pre_topc(X1,g1_pre_topc(X0,k1_tex_1(X0)),sK0) ) ),
    inference(superposition,[],[f74,f265])).

fof(f74,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0))
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
      | v5_pre_topc(X2,X1,sK0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f134,plain,(
    ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),k1_tex_1(u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f133,f128])).

fof(f128,plain,(
    ! [X0] :
      ( ~ v2_struct_0(g1_pre_topc(X0,k1_tex_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f109,f116])).

fof(f109,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ v2_struct_0(k2_tex_1(X0)) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_tex_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ~ v2_struct_0(k2_tex_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t71_tex_2.p',fc3_tex_1)).

fof(f133,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f75,f130,f100])).

fof(f100,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t71_tex_2.p',fc2_struct_0)).

fof(f130,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f77,f120])).

fof(f120,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t71_tex_2.p',dt_l1_pre_topc)).

fof(f75,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f172,plain,(
    ! [X0] : v1_funct_2(k6_relat_1(X0),X0,X0) ),
    inference(unit_resulting_resolution,[],[f104,f126,f125,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t71_tex_2.p',cc1_funct_2)).

fof(f126,plain,(
    ! [X0] : v1_partfun1(k6_relat_1(X0),X0) ),
    inference(definition_unfolding,[],[f98,f114])).

fof(f98,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f104,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t71_tex_2.p',fc3_funct_1)).

fof(f152,plain,(
    v4_pre_topc(sK1(sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f78,f76,f77,f81])).

fof(f81,plain,(
    ! [X0] :
      ( v4_pre_topc(sK1(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f48])).
%------------------------------------------------------------------------------
