%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t112_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:03 EDT 2019

% Result     : Theorem 2.34s
% Output     : Refutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :  292 (3825 expanded)
%              Number of leaves         :   51 (1424 expanded)
%              Depth                    :   24
%              Number of atoms          : 1221 (34071 expanded)
%              Number of equality atoms :   46 (3880 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12406,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f285,f323,f2920,f6306,f6336,f6350,f6356,f6359,f6738,f6768,f10148,f10191,f10201,f10208,f10219,f12332,f12334,f12345,f12354,f12405])).

fof(f12405,plain,
    ( spl12_5
    | ~ spl12_224 ),
    inference(avatar_contradiction_clause,[],[f12404])).

fof(f12404,plain,
    ( $false
    | ~ spl12_5
    | ~ spl12_224 ),
    inference(subsumption_resolution,[],[f10172,f10192])).

fof(f10192,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),sK2,k6_tmap_1(sK0,sK1))
    | ~ spl12_5 ),
    inference(forward_demodulation,[],[f278,f6890])).

fof(f6890,plain,(
    k7_tmap_1(sK0,o_0_0_xboole_0) = k7_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f6865,f620])).

fof(f620,plain,(
    m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f614,f295])).

fof(f295,plain,(
    ! [X1] : k3_xboole_0(o_0_0_xboole_0,X1) = o_0_0_xboole_0 ),
    inference(superposition,[],[f196,f253])).

fof(f253,plain,(
    ! [X0] : k3_xboole_0(X0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(definition_unfolding,[],[f173,f170,f170])).

fof(f170,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t112_tmap_1.p',d2_xboole_0)).

fof(f173,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

fof(f54,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t112_tmap_1.p',t2_boole)).

fof(f196,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t112_tmap_1.p',commutativity_k3_xboole_0)).

fof(f614,plain,(
    ! [X1] : m1_subset_1(k3_xboole_0(X1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f604,f602])).

fof(f602,plain,(
    ! [X1] : k3_xboole_0(X1,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X1) ),
    inference(subsumption_resolution,[],[f596,f164])).

fof(f164,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f138])).

fof(f138,plain,
    ( ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK2,k6_tmap_1(sK0,sK1))
      | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
      | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2)) )
    & u1_struct_0(sK2) = sK1
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f70,f137,f136,f135])).

fof(f135,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                  | ~ v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                  | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                  | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
                & u1_struct_0(X2) = X1
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(sK0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2),X2,k6_tmap_1(sK0,X1))
                | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(sK0,X1)))
                | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X2)) )
              & u1_struct_0(X2) = X1
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f136,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
              & u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,sK1),k7_tmap_1(X0,sK1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,sK1)))))
              | ~ v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,sK1),k7_tmap_1(X0,sK1),X2),X2,k6_tmap_1(X0,sK1))
              | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,sK1),k7_tmap_1(X0,sK1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,sK1)))
              | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,sK1),k7_tmap_1(X0,sK1),X2)) )
            & u1_struct_0(X2) = sK1
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
            | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
            | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
          & u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(X0,X1)))))
          | ~ v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),sK2),sK2,k6_tmap_1(X0,X1))
          | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(X0,X1)))
          | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),sK2)) )
        & u1_struct_0(sK2) = X1
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
              & u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                | ~ v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                | ~ v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                | ~ v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
              & u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
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
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( u1_struct_0(X2) = X1
                 => ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                    & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                    & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                    & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( u1_struct_0(X2) = X1
               => ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                  & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                  & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                  & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t112_tmap_1.p',t112_tmap_1)).

fof(f596,plain,(
    ! [X1] :
      ( k3_xboole_0(X1,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f592,f230])).

fof(f230,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f114])).

fof(f114,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f50])).

fof(f50,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t112_tmap_1.p',redefinition_k9_subset_1)).

fof(f592,plain,(
    ! [X24] : k9_subset_1(u1_struct_0(sK0),X24,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X24) ),
    inference(resolution,[],[f231,f164])).

fof(f231,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f115])).

fof(f115,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t112_tmap_1.p',commutativity_k9_subset_1)).

fof(f604,plain,(
    ! [X1] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,X1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f599,f164])).

fof(f599,plain,(
    ! [X1] :
      ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f229,f592])).

fof(f229,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f113])).

fof(f113,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t112_tmap_1.p',dt_k9_subset_1)).

fof(f6865,plain,(
    ! [X66] :
      ( ~ m1_subset_1(X66,k1_zfmisc_1(u1_struct_0(sK0)))
      | k7_tmap_1(sK0,sK1) = k7_tmap_1(sK0,X66) ) ),
    inference(resolution,[],[f3336,f164])).

fof(f3336,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k7_tmap_1(sK0,X0) = k7_tmap_1(sK0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f3329,f3329])).

fof(f3329,plain,(
    ! [X0] :
      ( k7_tmap_1(sK0,X0) = k6_relat_1(u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f3328,f162])).

fof(f162,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f138])).

fof(f3328,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | k7_tmap_1(sK0,X0) = k6_relat_1(u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f3325,f163])).

fof(f163,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f138])).

fof(f3325,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | k7_tmap_1(sK0,X0) = k6_relat_1(u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f257,f161])).

fof(f161,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f138])).

fof(f257,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | k7_tmap_1(X0,X1) = k6_relat_1(u1_struct_0(X0)) ) ),
    inference(definition_unfolding,[],[f183,f174])).

fof(f174,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t112_tmap_1.p',redefinition_k6_partfun1)).

fof(f183,plain,(
    ! [X0,X1] :
      ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t112_tmap_1.p',d10_tmap_1)).

fof(f278,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK2,k6_tmap_1(sK0,sK1))
    | ~ spl12_5 ),
    inference(avatar_component_clause,[],[f277])).

fof(f277,plain,
    ( spl12_5
  <=> ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK2,k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).

fof(f10172,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),sK2,k6_tmap_1(sK0,sK1))
    | ~ spl12_224 ),
    inference(avatar_component_clause,[],[f10171])).

fof(f10171,plain,
    ( spl12_224
  <=> v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),sK2,k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_224])])).

fof(f12354,plain,(
    ~ spl12_218 ),
    inference(avatar_contradiction_clause,[],[f12353])).

fof(f12353,plain,
    ( $false
    | ~ spl12_218 ),
    inference(subsumption_resolution,[],[f12352,f161])).

fof(f12352,plain,
    ( v2_struct_0(sK0)
    | ~ spl12_218 ),
    inference(subsumption_resolution,[],[f12351,f162])).

fof(f12351,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_218 ),
    inference(subsumption_resolution,[],[f12350,f163])).

fof(f12350,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_218 ),
    inference(subsumption_resolution,[],[f12349,f164])).

fof(f12349,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_218 ),
    inference(resolution,[],[f10154,f206])).

fof(f206,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f65])).

fof(f65,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t112_tmap_1.p',fc4_tmap_1)).

fof(f10154,plain,
    ( v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl12_218 ),
    inference(avatar_component_clause,[],[f10153])).

fof(f10153,plain,
    ( spl12_218
  <=> v2_struct_0(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_218])])).

fof(f12345,plain,
    ( spl12_7
    | ~ spl12_158
    | ~ spl12_160
    | ~ spl12_164 ),
    inference(avatar_contradiction_clause,[],[f12344])).

fof(f12344,plain,
    ( $false
    | ~ spl12_7
    | ~ spl12_158
    | ~ spl12_160
    | ~ spl12_164 ),
    inference(subsumption_resolution,[],[f12343,f6269])).

fof(f6269,plain,
    ( l1_struct_0(sK0)
    | ~ spl12_158 ),
    inference(avatar_component_clause,[],[f6268])).

fof(f6268,plain,
    ( spl12_158
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_158])])).

fof(f12343,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl12_7
    | ~ spl12_160
    | ~ spl12_164 ),
    inference(subsumption_resolution,[],[f12342,f6275])).

fof(f6275,plain,
    ( l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl12_160 ),
    inference(avatar_component_clause,[],[f6274])).

fof(f6274,plain,
    ( spl12_160
  <=> l1_struct_0(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_160])])).

fof(f12342,plain,
    ( ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | ~ spl12_7
    | ~ spl12_164 ),
    inference(subsumption_resolution,[],[f12341,f6917])).

fof(f6917,plain,(
    v1_funct_1(k7_tmap_1(sK0,o_0_0_xboole_0)) ),
    inference(subsumption_resolution,[],[f6916,f161])).

fof(f6916,plain,
    ( v1_funct_1(k7_tmap_1(sK0,o_0_0_xboole_0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f6915,f162])).

fof(f6915,plain,
    ( v1_funct_1(k7_tmap_1(sK0,o_0_0_xboole_0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f6914,f163])).

fof(f6914,plain,
    ( v1_funct_1(k7_tmap_1(sK0,o_0_0_xboole_0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f6909,f164])).

fof(f6909,plain,
    ( v1_funct_1(k7_tmap_1(sK0,o_0_0_xboole_0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f212,f6890])).

fof(f212,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t112_tmap_1.p',dt_k7_tmap_1)).

fof(f12341,plain,
    ( ~ v1_funct_1(k7_tmap_1(sK0,o_0_0_xboole_0))
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | ~ spl12_7
    | ~ spl12_164 ),
    inference(subsumption_resolution,[],[f12340,f6912])).

fof(f6912,plain,(
    v1_funct_2(k7_tmap_1(sK0,o_0_0_xboole_0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f6907,f164])).

fof(f6907,plain,
    ( v1_funct_2(k7_tmap_1(sK0,o_0_0_xboole_0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f4842,f6890])).

fof(f4842,plain,(
    ! [X0] :
      ( v1_funct_2(k7_tmap_1(sK0,X0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f4841,f162])).

fof(f4841,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | v1_funct_2(k7_tmap_1(sK0,X0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0))) ) ),
    inference(subsumption_resolution,[],[f4838,f163])).

fof(f4838,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v1_funct_2(k7_tmap_1(sK0,X0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0))) ) ),
    inference(resolution,[],[f213,f161])).

fof(f213,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f106])).

fof(f12340,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK0,o_0_0_xboole_0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,o_0_0_xboole_0))
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | ~ spl12_7
    | ~ spl12_164 ),
    inference(subsumption_resolution,[],[f12338,f6910])).

fof(f6910,plain,(
    m1_subset_1(k7_tmap_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) ),
    inference(subsumption_resolution,[],[f6905,f164])).

fof(f6905,plain,
    ( m1_subset_1(k7_tmap_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f5194,f6890])).

fof(f5194,plain,(
    ! [X0] :
      ( m1_subset_1(k7_tmap_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0)))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f5193,f162])).

fof(f5193,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | m1_subset_1(k7_tmap_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0))))) ) ),
    inference(subsumption_resolution,[],[f5190,f163])).

fof(f5190,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | m1_subset_1(k7_tmap_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X0))))) ) ),
    inference(resolution,[],[f214,f161])).

fof(f214,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) ) ),
    inference(cnf_transformation,[],[f106])).

fof(f12338,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,o_0_0_xboole_0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,o_0_0_xboole_0))
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | ~ spl12_7
    | ~ spl12_164 ),
    inference(resolution,[],[f12336,f6605])).

fof(f6605,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k2_tmap_1(X0,X1,X2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,u1_struct_0(X1))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | ~ l1_struct_0(X1)
        | ~ l1_struct_0(X0) )
    | ~ spl12_164 ),
    inference(subsumption_resolution,[],[f6603,f6287])).

fof(f6287,plain,
    ( l1_struct_0(sK2)
    | ~ spl12_164 ),
    inference(avatar_component_clause,[],[f6286])).

fof(f6286,plain,
    ( spl12_164
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_164])])).

fof(f6603,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,u1_struct_0(X1))))
      | ~ l1_struct_0(sK2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(superposition,[],[f246,f167])).

fof(f167,plain,(
    u1_struct_0(sK2) = sK1 ),
    inference(cnf_transformation,[],[f138])).

fof(f246,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f130])).

fof(f130,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f129])).

fof(f129,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( l1_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t112_tmap_1.p',dt_k2_tmap_1)).

fof(f12336,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ spl12_7 ),
    inference(forward_demodulation,[],[f12335,f6890])).

fof(f12335,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ spl12_7 ),
    inference(forward_demodulation,[],[f284,f167])).

fof(f284,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ spl12_7 ),
    inference(avatar_component_clause,[],[f283])).

fof(f283,plain,
    ( spl12_7
  <=> ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f12334,plain,
    ( ~ spl12_2
    | spl12_231 ),
    inference(avatar_contradiction_clause,[],[f12333])).

fof(f12333,plain,
    ( $false
    | ~ spl12_2
    | ~ spl12_231 ),
    inference(subsumption_resolution,[],[f10190,f10194])).

fof(f10194,plain,
    ( v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ spl12_2 ),
    inference(forward_demodulation,[],[f10193,f6890])).

fof(f10193,plain,
    ( v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ spl12_2 ),
    inference(forward_demodulation,[],[f269,f167])).

fof(f269,plain,
    ( v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl12_2
  <=> v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f10190,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ spl12_231 ),
    inference(avatar_component_clause,[],[f10189])).

fof(f10189,plain,
    ( spl12_231
  <=> ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),sK1,u1_struct_0(k6_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_231])])).

fof(f12332,plain,
    ( ~ spl12_158
    | ~ spl12_160
    | ~ spl12_164
    | spl12_229 ),
    inference(avatar_contradiction_clause,[],[f12331])).

fof(f12331,plain,
    ( $false
    | ~ spl12_158
    | ~ spl12_160
    | ~ spl12_164
    | ~ spl12_229 ),
    inference(subsumption_resolution,[],[f12330,f6269])).

fof(f12330,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl12_160
    | ~ spl12_164
    | ~ spl12_229 ),
    inference(subsumption_resolution,[],[f12329,f6275])).

fof(f12329,plain,
    ( ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | ~ spl12_164
    | ~ spl12_229 ),
    inference(subsumption_resolution,[],[f12328,f6917])).

fof(f12328,plain,
    ( ~ v1_funct_1(k7_tmap_1(sK0,o_0_0_xboole_0))
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | ~ spl12_164
    | ~ spl12_229 ),
    inference(subsumption_resolution,[],[f12327,f6912])).

fof(f12327,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK0,o_0_0_xboole_0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,o_0_0_xboole_0))
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | ~ spl12_164
    | ~ spl12_229 ),
    inference(subsumption_resolution,[],[f12325,f6910])).

fof(f12325,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,o_0_0_xboole_0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,o_0_0_xboole_0))
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | ~ spl12_164
    | ~ spl12_229 ),
    inference(resolution,[],[f10184,f6605])).

fof(f10184,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ spl12_229 ),
    inference(avatar_component_clause,[],[f10183])).

fof(f10183,plain,
    ( spl12_229
  <=> ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,u1_struct_0(k6_tmap_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_229])])).

fof(f10219,plain,
    ( spl12_218
    | spl12_226
    | ~ spl12_229
    | ~ spl12_231
    | ~ spl12_0
    | spl12_5
    | ~ spl12_8
    | ~ spl12_74
    | ~ spl12_220
    | ~ spl12_222 ),
    inference(avatar_split_clause,[],[f10218,f10162,f10156,f2901,f308,f277,f262,f10189,f10183,f10174,f10153])).

fof(f10174,plain,
    ( spl12_226
  <=> m1_subset_1(sK4(k6_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_226])])).

fof(f262,plain,
    ( spl12_0
  <=> v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_0])])).

fof(f308,plain,
    ( spl12_8
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f2901,plain,
    ( spl12_74
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_74])])).

fof(f10156,plain,
    ( spl12_220
  <=> v2_pre_topc(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_220])])).

fof(f10162,plain,
    ( spl12_222
  <=> l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_222])])).

fof(f10218,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | m1_subset_1(sK4(k6_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2)),sK1)
    | v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl12_0
    | ~ spl12_5
    | ~ spl12_8
    | ~ spl12_74
    | ~ spl12_220
    | ~ spl12_222 ),
    inference(forward_demodulation,[],[f10217,f167])).

fof(f10217,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | m1_subset_1(sK4(k6_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2)),sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl12_0
    | ~ spl12_5
    | ~ spl12_8
    | ~ spl12_74
    | ~ spl12_220
    | ~ spl12_222 ),
    inference(forward_demodulation,[],[f10216,f167])).

fof(f10216,plain,
    ( m1_subset_1(sK4(k6_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2)),sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl12_0
    | ~ spl12_5
    | ~ spl12_8
    | ~ spl12_74
    | ~ spl12_220
    | ~ spl12_222 ),
    inference(forward_demodulation,[],[f10215,f167])).

fof(f10215,plain,
    ( m1_subset_1(sK4(k6_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2)),u1_struct_0(sK2))
    | ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl12_0
    | ~ spl12_5
    | ~ spl12_8
    | ~ spl12_74
    | ~ spl12_220
    | ~ spl12_222 ),
    inference(subsumption_resolution,[],[f10214,f10157])).

fof(f10157,plain,
    ( v2_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ spl12_220 ),
    inference(avatar_component_clause,[],[f10156])).

fof(f10214,plain,
    ( m1_subset_1(sK4(k6_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2)),u1_struct_0(sK2))
    | ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl12_0
    | ~ spl12_5
    | ~ spl12_8
    | ~ spl12_74
    | ~ spl12_222 ),
    inference(subsumption_resolution,[],[f10213,f10163])).

fof(f10163,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ spl12_222 ),
    inference(avatar_component_clause,[],[f10162])).

fof(f10213,plain,
    ( m1_subset_1(sK4(k6_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2)),u1_struct_0(sK2))
    | ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl12_0
    | ~ spl12_5
    | ~ spl12_8
    | ~ spl12_74 ),
    inference(subsumption_resolution,[],[f10212,f165])).

fof(f165,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f138])).

fof(f10212,plain,
    ( m1_subset_1(sK4(k6_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2)),u1_struct_0(sK2))
    | ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl12_0
    | ~ spl12_5
    | ~ spl12_8
    | ~ spl12_74 ),
    inference(subsumption_resolution,[],[f10211,f2902])).

fof(f2902,plain,
    ( v2_pre_topc(sK2)
    | ~ spl12_74 ),
    inference(avatar_component_clause,[],[f2901])).

fof(f10211,plain,
    ( m1_subset_1(sK4(k6_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2)),u1_struct_0(sK2))
    | ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl12_0
    | ~ spl12_5
    | ~ spl12_8 ),
    inference(subsumption_resolution,[],[f10210,f309])).

fof(f309,plain,
    ( l1_pre_topc(sK2)
    | ~ spl12_8 ),
    inference(avatar_component_clause,[],[f308])).

fof(f10210,plain,
    ( m1_subset_1(sK4(k6_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2)),u1_struct_0(sK2))
    | ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl12_0
    | ~ spl12_5 ),
    inference(subsumption_resolution,[],[f10209,f6898])).

fof(f6898,plain,
    ( v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2))
    | ~ spl12_0 ),
    inference(backward_demodulation,[],[f6890,f263])).

fof(f263,plain,
    ( v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2))
    | ~ spl12_0 ),
    inference(avatar_component_clause,[],[f262])).

fof(f10209,plain,
    ( m1_subset_1(sK4(k6_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2)),u1_struct_0(sK2))
    | ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl12_5 ),
    inference(resolution,[],[f10192,f188])).

fof(f188,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X1,X0)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f144])).

fof(f144,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ( ~ r1_tmap_1(X1,X0,X2,sK4(X0,X1,X2))
                    & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) )
                & ( ! [X4] :
                      ( r1_tmap_1(X1,X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f142,f143])).

fof(f143,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tmap_1(X1,X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_tmap_1(X1,X0,X2,sK4(X0,X1,X2))
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f142,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ? [X3] :
                      ( ~ r1_tmap_1(X1,X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ! [X4] :
                      ( r1_tmap_1(X1,X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f141])).

fof(f141,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ? [X3] :
                      ( ~ r1_tmap_1(X1,X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ! [X3] :
                      ( r1_tmap_1(X1,X0,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f86])).

fof(f86,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f58])).

fof(f58,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => r1_tmap_1(X1,X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t112_tmap_1.p',t49_tmap_1)).

fof(f10208,plain,(
    spl12_223 ),
    inference(avatar_contradiction_clause,[],[f10207])).

fof(f10207,plain,
    ( $false
    | ~ spl12_223 ),
    inference(subsumption_resolution,[],[f10206,f161])).

fof(f10206,plain,
    ( v2_struct_0(sK0)
    | ~ spl12_223 ),
    inference(subsumption_resolution,[],[f10205,f162])).

fof(f10205,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_223 ),
    inference(subsumption_resolution,[],[f10204,f163])).

fof(f10204,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_223 ),
    inference(subsumption_resolution,[],[f10202,f164])).

fof(f10202,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_223 ),
    inference(resolution,[],[f10166,f211])).

fof(f211,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t112_tmap_1.p',dt_k6_tmap_1)).

fof(f10166,plain,
    ( ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ spl12_223 ),
    inference(avatar_component_clause,[],[f10165])).

fof(f10165,plain,
    ( spl12_223
  <=> ~ l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_223])])).

fof(f10201,plain,(
    spl12_221 ),
    inference(avatar_contradiction_clause,[],[f10200])).

fof(f10200,plain,
    ( $false
    | ~ spl12_221 ),
    inference(subsumption_resolution,[],[f10199,f161])).

fof(f10199,plain,
    ( v2_struct_0(sK0)
    | ~ spl12_221 ),
    inference(subsumption_resolution,[],[f10198,f162])).

fof(f10198,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_221 ),
    inference(subsumption_resolution,[],[f10197,f163])).

fof(f10197,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_221 ),
    inference(subsumption_resolution,[],[f10195,f164])).

fof(f10195,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_221 ),
    inference(resolution,[],[f10160,f208])).

fof(f208,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f10160,plain,
    ( ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ spl12_221 ),
    inference(avatar_component_clause,[],[f10159])).

fof(f10159,plain,
    ( spl12_221
  <=> ~ v2_pre_topc(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_221])])).

fof(f10191,plain,
    ( spl12_218
    | ~ spl12_221
    | ~ spl12_223
    | spl12_224
    | ~ spl12_227
    | ~ spl12_229
    | ~ spl12_231
    | ~ spl12_0
    | ~ spl12_8
    | ~ spl12_74 ),
    inference(avatar_split_clause,[],[f9337,f2901,f308,f262,f10189,f10183,f10177,f10171,f10165,f10159,f10153])).

fof(f10177,plain,
    ( spl12_227
  <=> ~ m1_subset_1(sK4(k6_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_227])])).

fof(f9337,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ m1_subset_1(sK4(k6_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2)),sK1)
    | v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),sK2,k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl12_0
    | ~ spl12_8
    | ~ spl12_74 ),
    inference(forward_demodulation,[],[f9336,f167])).

fof(f9336,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ m1_subset_1(sK4(k6_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2)),sK1)
    | v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),sK2,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl12_0
    | ~ spl12_8
    | ~ spl12_74 ),
    inference(forward_demodulation,[],[f9335,f167])).

fof(f9335,plain,
    ( ~ m1_subset_1(sK4(k6_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2)),sK1)
    | v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),sK2,k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl12_0
    | ~ spl12_8
    | ~ spl12_74 ),
    inference(subsumption_resolution,[],[f9334,f165])).

fof(f9334,plain,
    ( ~ m1_subset_1(sK4(k6_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2)),sK1)
    | v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),sK2,k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl12_0
    | ~ spl12_8
    | ~ spl12_74 ),
    inference(subsumption_resolution,[],[f9333,f2902])).

fof(f9333,plain,
    ( ~ m1_subset_1(sK4(k6_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2)),sK1)
    | v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),sK2,k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl12_0
    | ~ spl12_8 ),
    inference(subsumption_resolution,[],[f9332,f309])).

fof(f9332,plain,
    ( ~ m1_subset_1(sK4(k6_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2)),sK1)
    | v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),sK2,k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl12_0 ),
    inference(subsumption_resolution,[],[f9331,f6898])).

fof(f9331,plain,
    ( ~ m1_subset_1(sK4(k6_tmap_1(sK0,sK1),sK2,k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2)),sK1)
    | v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),sK2,k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | v2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f9195,f189])).

fof(f189,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(X1,X0,X2,sK4(X0,X1,X2))
      | v5_pre_topc(X2,X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f144])).

fof(f9195,plain,(
    ! [X0] :
      ( r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),X0)
      | ~ m1_subset_1(X0,sK1) ) ),
    inference(forward_demodulation,[],[f6749,f6890])).

fof(f6749,plain,(
    ! [X0] :
      ( r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),X0)
      | ~ m1_subset_1(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f6748,f164])).

fof(f6748,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),X0)
      | ~ m1_subset_1(X0,sK1) ) ),
    inference(forward_demodulation,[],[f6747,f167])).

fof(f6747,plain,(
    ! [X0] :
      ( r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),X0)
      | ~ m1_subset_1(X0,sK1)
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f6746,f167])).

fof(f6746,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | r1_tmap_1(sK2,k6_tmap_1(sK0,u1_struct_0(sK2)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK2)),k7_tmap_1(sK0,u1_struct_0(sK2)),sK2),X0)
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f6745,f167])).

fof(f6745,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_tmap_1(sK2,k6_tmap_1(sK0,u1_struct_0(sK2)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK2)),k7_tmap_1(sK0,u1_struct_0(sK2)),sK2),X0)
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f6744,f161])).

fof(f6744,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_tmap_1(sK2,k6_tmap_1(sK0,u1_struct_0(sK2)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK2)),k7_tmap_1(sK0,u1_struct_0(sK2)),sK2),X0)
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f6743,f162])).

fof(f6743,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_tmap_1(sK2,k6_tmap_1(sK0,u1_struct_0(sK2)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK2)),k7_tmap_1(sK0,u1_struct_0(sK2)),sK2),X0)
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f6742,f163])).

fof(f6742,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_tmap_1(sK2,k6_tmap_1(sK0,u1_struct_0(sK2)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK2)),k7_tmap_1(sK0,u1_struct_0(sK2)),sK2),X0)
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f6739,f165])).

fof(f6739,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_tmap_1(sK2,k6_tmap_1(sK0,u1_struct_0(sK2)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK2)),k7_tmap_1(sK0,u1_struct_0(sK2)),sK2),X0)
      | v2_struct_0(sK2)
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f258,f166])).

fof(f166,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f138])).

fof(f258,plain,(
    ! [X2,X0,X3] :
      ( ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | r1_tmap_1(X2,k6_tmap_1(X0,u1_struct_0(X2)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X3)
      | v2_struct_0(X2)
      | ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f186])).

fof(f186,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | u1_struct_0(X2) != X1
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f84])).

fof(f84,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f51])).

fof(f51,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( u1_struct_0(X2) = X1
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X2))
                   => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t112_tmap_1.p',t110_tmap_1)).

fof(f10148,plain,
    ( spl12_3
    | ~ spl12_158
    | ~ spl12_160
    | ~ spl12_164 ),
    inference(avatar_contradiction_clause,[],[f10147])).

fof(f10147,plain,
    ( $false
    | ~ spl12_3
    | ~ spl12_158
    | ~ spl12_160
    | ~ spl12_164 ),
    inference(subsumption_resolution,[],[f9115,f6910])).

fof(f9115,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ spl12_3
    | ~ spl12_158
    | ~ spl12_160
    | ~ spl12_164 ),
    inference(subsumption_resolution,[],[f9114,f6269])).

fof(f9114,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ l1_struct_0(sK0)
    | ~ spl12_3
    | ~ spl12_160
    | ~ spl12_164 ),
    inference(subsumption_resolution,[],[f9113,f6275])).

fof(f9113,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | ~ spl12_3
    | ~ spl12_164 ),
    inference(subsumption_resolution,[],[f9112,f6917])).

fof(f9112,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_1(k7_tmap_1(sK0,o_0_0_xboole_0))
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | ~ spl12_3
    | ~ spl12_164 ),
    inference(subsumption_resolution,[],[f9111,f6912])).

fof(f9111,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,o_0_0_xboole_0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,o_0_0_xboole_0))
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | ~ spl12_3
    | ~ spl12_164 ),
    inference(resolution,[],[f6902,f6387])).

fof(f6387,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k2_tmap_1(X0,X1,X2,sK2),sK1,u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | ~ l1_struct_0(X1)
        | ~ l1_struct_0(X0) )
    | ~ spl12_164 ),
    inference(subsumption_resolution,[],[f6385,f6287])).

fof(f6385,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,sK2),sK1,u1_struct_0(X1))
      | ~ l1_struct_0(sK2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(superposition,[],[f245,f167])).

fof(f245,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f130])).

fof(f6902,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,o_0_0_xboole_0),sK2),sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ spl12_3 ),
    inference(backward_demodulation,[],[f6890,f6769])).

fof(f6769,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK1,u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ spl12_3 ),
    inference(forward_demodulation,[],[f272,f167])).

fof(f272,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f271])).

fof(f271,plain,
    ( spl12_3
  <=> ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f6768,plain,(
    spl12_177 ),
    inference(avatar_contradiction_clause,[],[f6767])).

fof(f6767,plain,
    ( $false
    | ~ spl12_177 ),
    inference(subsumption_resolution,[],[f6762,f164])).

fof(f6762,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl12_177 ),
    inference(resolution,[],[f5194,f6349])).

fof(f6349,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ spl12_177 ),
    inference(avatar_component_clause,[],[f6348])).

fof(f6348,plain,
    ( spl12_177
  <=> ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_177])])).

fof(f6738,plain,(
    spl12_175 ),
    inference(avatar_contradiction_clause,[],[f6737])).

fof(f6737,plain,
    ( $false
    | ~ spl12_175 ),
    inference(subsumption_resolution,[],[f6734,f164])).

fof(f6734,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl12_175 ),
    inference(resolution,[],[f4842,f6343])).

fof(f6343,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ spl12_175 ),
    inference(avatar_component_clause,[],[f6342])).

fof(f6342,plain,
    ( spl12_175
  <=> ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_175])])).

fof(f6359,plain,
    ( ~ spl12_8
    | spl12_165 ),
    inference(avatar_contradiction_clause,[],[f6358])).

fof(f6358,plain,
    ( $false
    | ~ spl12_8
    | ~ spl12_165 ),
    inference(subsumption_resolution,[],[f6357,f309])).

fof(f6357,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ spl12_165 ),
    inference(resolution,[],[f6290,f178])).

fof(f178,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t112_tmap_1.p',dt_l1_pre_topc)).

fof(f6290,plain,
    ( ~ l1_struct_0(sK2)
    | ~ spl12_165 ),
    inference(avatar_component_clause,[],[f6289])).

fof(f6289,plain,
    ( spl12_165
  <=> ~ l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_165])])).

fof(f6356,plain,(
    spl12_163 ),
    inference(avatar_contradiction_clause,[],[f6355])).

fof(f6355,plain,
    ( $false
    | ~ spl12_163 ),
    inference(subsumption_resolution,[],[f6354,f161])).

fof(f6354,plain,
    ( v2_struct_0(sK0)
    | ~ spl12_163 ),
    inference(subsumption_resolution,[],[f6353,f162])).

fof(f6353,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_163 ),
    inference(subsumption_resolution,[],[f6352,f163])).

fof(f6352,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_163 ),
    inference(subsumption_resolution,[],[f6351,f164])).

fof(f6351,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_163 ),
    inference(resolution,[],[f6284,f212])).

fof(f6284,plain,
    ( ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ spl12_163 ),
    inference(avatar_component_clause,[],[f6283])).

fof(f6283,plain,
    ( spl12_163
  <=> ~ v1_funct_1(k7_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_163])])).

fof(f6350,plain,
    ( ~ spl12_161
    | ~ spl12_163
    | ~ spl12_175
    | ~ spl12_177
    | ~ spl12_165
    | spl12_1
    | ~ spl12_158 ),
    inference(avatar_split_clause,[],[f6337,f6268,f265,f6289,f6348,f6342,f6283,f6277])).

fof(f6277,plain,
    ( spl12_161
  <=> ~ l1_struct_0(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_161])])).

fof(f265,plain,
    ( spl12_1
  <=> ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f6337,plain,
    ( ~ l1_struct_0(sK2)
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl12_1
    | ~ spl12_158 ),
    inference(subsumption_resolution,[],[f6264,f6269])).

fof(f6264,plain,
    ( ~ l1_struct_0(sK2)
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK0)
    | ~ spl12_1 ),
    inference(resolution,[],[f244,f266])).

fof(f266,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2))
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f265])).

fof(f244,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f130])).

fof(f6336,plain,(
    spl12_161 ),
    inference(avatar_contradiction_clause,[],[f6335])).

fof(f6335,plain,
    ( $false
    | ~ spl12_161 ),
    inference(subsumption_resolution,[],[f6312,f164])).

fof(f6312,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl12_161 ),
    inference(subsumption_resolution,[],[f6311,f161])).

fof(f6311,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl12_161 ),
    inference(subsumption_resolution,[],[f6310,f162])).

fof(f6310,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_161 ),
    inference(subsumption_resolution,[],[f6308,f163])).

fof(f6308,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_161 ),
    inference(resolution,[],[f6307,f211])).

fof(f6307,plain,
    ( ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ spl12_161 ),
    inference(resolution,[],[f6278,f178])).

fof(f6278,plain,
    ( ~ l1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl12_161 ),
    inference(avatar_component_clause,[],[f6277])).

fof(f6306,plain,(
    spl12_159 ),
    inference(avatar_contradiction_clause,[],[f6305])).

fof(f6305,plain,
    ( $false
    | ~ spl12_159 ),
    inference(subsumption_resolution,[],[f6304,f163])).

fof(f6304,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl12_159 ),
    inference(resolution,[],[f6272,f178])).

fof(f6272,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl12_159 ),
    inference(avatar_component_clause,[],[f6271])).

fof(f6271,plain,
    ( spl12_159
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_159])])).

fof(f2920,plain,(
    spl12_75 ),
    inference(avatar_contradiction_clause,[],[f2919])).

fof(f2919,plain,
    ( $false
    | ~ spl12_75 ),
    inference(subsumption_resolution,[],[f2918,f162])).

fof(f2918,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl12_75 ),
    inference(subsumption_resolution,[],[f2917,f163])).

fof(f2917,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl12_75 ),
    inference(resolution,[],[f2916,f166])).

fof(f2916,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl12_75 ),
    inference(resolution,[],[f2905,f191])).

fof(f191,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f90])).

fof(f90,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f64])).

fof(f64,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t112_tmap_1.p',cc1_pre_topc)).

fof(f2905,plain,
    ( ~ v2_pre_topc(sK2)
    | ~ spl12_75 ),
    inference(avatar_component_clause,[],[f2904])).

fof(f2904,plain,
    ( spl12_75
  <=> ~ v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_75])])).

fof(f323,plain,(
    spl12_9 ),
    inference(avatar_contradiction_clause,[],[f322])).

fof(f322,plain,
    ( $false
    | ~ spl12_9 ),
    inference(subsumption_resolution,[],[f321,f163])).

fof(f321,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl12_9 ),
    inference(resolution,[],[f320,f166])).

fof(f320,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl12_9 ),
    inference(resolution,[],[f312,f181])).

fof(f181,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t112_tmap_1.p',dt_m1_pre_topc)).

fof(f312,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ spl12_9 ),
    inference(avatar_component_clause,[],[f311])).

fof(f311,plain,
    ( spl12_9
  <=> ~ l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).

fof(f285,plain,
    ( ~ spl12_1
    | ~ spl12_3
    | ~ spl12_5
    | ~ spl12_7 ),
    inference(avatar_split_clause,[],[f168,f283,f277,f271,f265])).

fof(f168,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK2,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2)) ),
    inference(cnf_transformation,[],[f138])).
%------------------------------------------------------------------------------
