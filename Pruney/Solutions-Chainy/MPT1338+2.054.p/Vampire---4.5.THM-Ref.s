%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  143 (2593 expanded)
%              Number of leaves         :   22 ( 937 expanded)
%              Depth                    :   24
%              Number of atoms          :  440 (21369 expanded)
%              Number of equality atoms :  167 (7137 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f232,plain,(
    $false ),
    inference(subsumption_resolution,[],[f216,f56])).

fof(f56,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f216,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f116,f210])).

fof(f210,plain,(
    k1_xboole_0 = k2_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f208,f190])).

fof(f190,plain,(
    k2_struct_0(sK1) != k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f189,f182])).

fof(f182,plain,(
    k1_relat_1(sK3) = k2_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) ),
    inference(forward_demodulation,[],[f175,f103])).

fof(f103,plain,(
    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f102,f96])).

fof(f96,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f68,f88])).

fof(f88,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) ),
    inference(forward_demodulation,[],[f85,f83])).

fof(f83,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(resolution,[],[f61,f49])).

fof(f49,plain,(
    l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))
      | k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) )
    & v2_funct_1(sK3)
    & k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    & v1_funct_1(sK3)
    & l1_struct_0(sK2)
    & ~ v2_struct_0(sK2)
    & l1_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f21,f44,f43,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                  | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
                & v2_funct_1(X2)
                & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2))
              | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2)) )
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),X2))
            | k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),X2)) )
          & v2_funct_1(X2)
          & k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
          & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK2))
          & v1_funct_1(X2) )
      & l1_struct_0(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X2] :
        ( ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),X2))
          | k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),X2)) )
        & v2_funct_1(X2)
        & k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK2))
        & v1_funct_1(X2) )
   => ( ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))
        | k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) )
      & v2_funct_1(sK3)
      & k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
      & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( ( l1_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                    & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                  & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).

fof(f61,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f85,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(backward_demodulation,[],[f52,f82])).

fof(f82,plain,(
    k2_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(resolution,[],[f61,f47])).

fof(f47,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f52,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f45])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f102,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f101,f50])).

fof(f50,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f101,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f64,f54])).

fof(f54,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f175,plain,(
    k2_relat_1(k2_funct_1(sK3)) = k2_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) ),
    inference(resolution,[],[f159,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f159,plain,(
    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_struct_0(sK1)))) ),
    inference(resolution,[],[f158,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | ~ sP0(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f158,plain,(
    sP0(k2_struct_0(sK1),k2_relat_1(sK3),sK3) ),
    inference(subsumption_resolution,[],[f157,f50])).

fof(f157,plain,
    ( sP0(k2_struct_0(sK1),k2_relat_1(sK3),sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f156,f118])).

fof(f118,plain,(
    v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f87,f113])).

fof(f113,plain,(
    k2_struct_0(sK2) = k2_relat_1(sK3) ),
    inference(backward_demodulation,[],[f89,f111])).

fof(f111,plain,(
    k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f70,f88])).

fof(f89,plain,(
    k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) ),
    inference(forward_demodulation,[],[f84,f83])).

fof(f84,plain,(
    k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK2),sK3) ),
    inference(backward_demodulation,[],[f53,f82])).

fof(f53,plain,(
    k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f87,plain,(
    v1_funct_2(sK3,k2_struct_0(sK1),k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f86,f83])).

fof(f86,plain,(
    v1_funct_2(sK3,k2_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f51,f82])).

fof(f51,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f45])).

fof(f156,plain,
    ( sP0(k2_struct_0(sK1),k2_relat_1(sK3),sK3)
    | ~ v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f155,f54])).

fof(f155,plain,
    ( ~ v2_funct_1(sK3)
    | sP0(k2_struct_0(sK1),k2_relat_1(sK3),sK3)
    | ~ v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f152,f114])).

fof(f114,plain,(
    k2_relat_1(sK3) = k2_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3) ),
    inference(backward_demodulation,[],[f111,f113])).

fof(f152,plain,
    ( k2_relat_1(sK3) != k2_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3)
    | ~ v2_funct_1(sK3)
    | sP0(k2_struct_0(sK1),k2_relat_1(sK3),sK3)
    | ~ v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f76,f117])).

fof(f117,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) ),
    inference(backward_demodulation,[],[f88,f113])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | sP0(X0,X1,X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( sP0(X0,X1,X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f35,f40])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f189,plain,(
    k2_struct_0(sK1) != k2_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f172,f181])).

fof(f181,plain,(
    k2_relat_1(sK3) = k1_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) ),
    inference(forward_demodulation,[],[f174,f100])).

fof(f100,plain,(
    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f99,f96])).

fof(f99,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f98,f50])).

fof(f98,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f63,f54])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f174,plain,(
    k1_relat_1(k2_funct_1(sK3)) = k1_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) ),
    inference(resolution,[],[f159,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f172,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) ),
    inference(forward_demodulation,[],[f171,f170])).

fof(f170,plain,(
    k2_funct_1(sK3) = k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) ),
    inference(subsumption_resolution,[],[f169,f50])).

fof(f169,plain,
    ( k2_funct_1(sK3) = k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f168,f118])).

fof(f168,plain,
    ( k2_funct_1(sK3) = k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)
    | ~ v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f167,f114])).

fof(f167,plain,
    ( k2_relat_1(sK3) != k2_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3)
    | k2_funct_1(sK3) = k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)
    | ~ v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f164,f54])).

fof(f164,plain,
    ( ~ v2_funct_1(sK3)
    | k2_relat_1(sK3) != k2_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3)
    | k2_funct_1(sK3) = k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)
    | ~ v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f77,f117])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

% (11594)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% (11596)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% (11606)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% (11608)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f171,plain,
    ( k2_relat_1(sK3) != k1_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3))
    | k2_struct_0(sK1) != k2_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)) ),
    inference(backward_demodulation,[],[f149,f170])).

fof(f149,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3))
    | k2_relat_1(sK3) != k1_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)) ),
    inference(forward_demodulation,[],[f148,f113])).

fof(f148,plain,
    ( k2_struct_0(sK2) != k1_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3))
    | k2_struct_0(sK1) != k2_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)) ),
    inference(forward_demodulation,[],[f147,f82])).

fof(f147,plain,
    ( k2_struct_0(sK2) != k1_relset_1(k2_relat_1(sK3),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),k2_relat_1(sK3),sK3))
    | k2_struct_0(sK1) != k2_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)) ),
    inference(forward_demodulation,[],[f146,f119])).

fof(f119,plain,(
    u1_struct_0(sK2) = k2_relat_1(sK3) ),
    inference(backward_demodulation,[],[f83,f113])).

fof(f146,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3))
    | k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
    inference(forward_demodulation,[],[f145,f82])).

fof(f145,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_relat_1(sK3),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),k2_relat_1(sK3),sK3))
    | k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
    inference(forward_demodulation,[],[f55,f119])).

fof(f55,plain,
    ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))
    | k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
    inference(cnf_transformation,[],[f45])).

fof(f208,plain,
    ( k2_struct_0(sK1) = k1_relat_1(sK3)
    | k1_xboole_0 = k2_relat_1(sK3) ),
    inference(superposition,[],[f207,f144])).

fof(f144,plain,(
    ! [X2] : k1_relat_1(k6_partfun1(X2)) = X2 ),
    inference(backward_demodulation,[],[f109,f142])).

fof(f142,plain,(
    ! [X2] : k1_relset_1(X2,X2,k6_partfun1(X2)) = X2 ),
    inference(forward_demodulation,[],[f139,f104])).

fof(f104,plain,(
    ! [X0] : k8_relset_1(X0,X0,k6_partfun1(X0),X0) = X0 ),
    inference(resolution,[],[f67,f81])).

fof(f81,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f59,f57])).

fof(f57,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

fof(f139,plain,(
    ! [X2] : k1_relset_1(X2,X2,k6_partfun1(X2)) = k8_relset_1(X2,X2,k6_partfun1(X2),X2) ),
    inference(resolution,[],[f72,f80])).

fof(f80,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f60,f58])).

fof(f58,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f109,plain,(
    ! [X2] : k1_relset_1(X2,X2,k6_partfun1(X2)) = k1_relat_1(k6_partfun1(X2)) ),
    inference(resolution,[],[f69,f80])).

fof(f207,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k6_partfun1(k2_struct_0(sK1)))
    | k1_xboole_0 = k2_relat_1(sK3) ),
    inference(superposition,[],[f127,f205])).

fof(f205,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k2_struct_0(sK1))
    | k1_xboole_0 = k2_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f204,f50])).

fof(f204,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k2_struct_0(sK1))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f203,f118])).

fof(f203,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k2_struct_0(sK1))
    | ~ v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f202,f114])).

fof(f202,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | k2_relat_1(sK3) != k2_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3)
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k2_struct_0(sK1))
    | ~ v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f196,f54])).

fof(f196,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | k2_relat_1(sK3) != k2_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3)
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k2_struct_0(sK1))
    | ~ v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f78,f117])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f127,plain,(
    k1_relat_1(sK3) = k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) ),
    inference(subsumption_resolution,[],[f126,f96])).

fof(f126,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f125,f50])).

fof(f125,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f65,f54])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(f116,plain,(
    ~ v1_xboole_0(k2_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f94,f113])).

fof(f94,plain,(
    ~ v1_xboole_0(k2_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f93,f48])).

fof(f48,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f93,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK2))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f91,f49])).

fof(f91,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK2))
    | ~ l1_struct_0(sK2)
    | v2_struct_0(sK2) ),
    inference(superposition,[],[f62,f83])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:15:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (11602)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.46  % (11597)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (11603)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.47  % (11592)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (11605)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.47  % (11603)Refutation not found, incomplete strategy% (11603)------------------------------
% 0.20/0.47  % (11603)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (11603)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (11603)Memory used [KB]: 11001
% 0.20/0.47  % (11603)Time elapsed: 0.067 s
% 0.20/0.47  % (11603)------------------------------
% 0.20/0.47  % (11603)------------------------------
% 0.20/0.48  % (11595)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  % (11604)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.48  % (11600)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.48  % (11599)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (11604)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f232,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(subsumption_resolution,[],[f216,f56])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.48  fof(f216,plain,(
% 0.20/0.48    ~v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    inference(backward_demodulation,[],[f116,f210])).
% 0.20/0.48  fof(f210,plain,(
% 0.20/0.48    k1_xboole_0 = k2_relat_1(sK3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f208,f190])).
% 0.20/0.48  fof(f190,plain,(
% 0.20/0.48    k2_struct_0(sK1) != k1_relat_1(sK3)),
% 0.20/0.48    inference(forward_demodulation,[],[f189,f182])).
% 0.20/0.48  fof(f182,plain,(
% 0.20/0.48    k1_relat_1(sK3) = k2_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3))),
% 0.20/0.48    inference(forward_demodulation,[],[f175,f103])).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))),
% 0.20/0.48    inference(subsumption_resolution,[],[f102,f96])).
% 0.20/0.48  fof(f96,plain,(
% 0.20/0.48    v1_relat_1(sK3)),
% 0.20/0.48    inference(resolution,[],[f68,f88])).
% 0.20/0.48  fof(f88,plain,(
% 0.20/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))))),
% 0.20/0.48    inference(forward_demodulation,[],[f85,f83])).
% 0.20/0.48  fof(f83,plain,(
% 0.20/0.48    u1_struct_0(sK2) = k2_struct_0(sK2)),
% 0.20/0.48    inference(resolution,[],[f61,f49])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    l1_struct_0(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f45])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    (((k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) | k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))) & v2_funct_1(sK3) & k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3)) & l1_struct_0(sK2) & ~v2_struct_0(sK2)) & l1_struct_0(sK1)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f21,f44,f43,f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK1))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ? [X1] : (? [X2] : ((k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),X2)) | k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),X2))) & v2_funct_1(X2) & k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_struct_0(sK2) & ~v2_struct_0(sK2))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ? [X2] : ((k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),X2)) | k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),X2))) & v2_funct_1(X2) & k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(X2)) => ((k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) | k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))) & v2_funct_1(sK3) & k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : (((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,negated_conjecture,(
% 0.20/0.48    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.20/0.48    inference(negated_conjecture,[],[f18])).
% 0.20/0.48  fof(f18,conjecture,(
% 0.20/0.48    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,axiom,(
% 0.20/0.48    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.48  fof(f85,plain,(
% 0.20/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK2))))),
% 0.20/0.48    inference(backward_demodulation,[],[f52,f82])).
% 0.20/0.48  fof(f82,plain,(
% 0.20/0.48    k2_struct_0(sK1) = u1_struct_0(sK1)),
% 0.20/0.48    inference(resolution,[],[f61,f47])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    l1_struct_0(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f45])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 0.20/0.48    inference(cnf_transformation,[],[f45])).
% 0.20/0.48  fof(f68,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.48  fof(f102,plain,(
% 0.20/0.48    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f101,f50])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    v1_funct_1(sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f45])).
% 0.20/0.48  fof(f101,plain,(
% 0.20/0.48    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.20/0.48    inference(resolution,[],[f64,f54])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    v2_funct_1(sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f45])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.20/0.48  fof(f175,plain,(
% 0.20/0.48    k2_relat_1(k2_funct_1(sK3)) = k2_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3))),
% 0.20/0.48    inference(resolution,[],[f159,f70])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.48  fof(f159,plain,(
% 0.20/0.48    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_struct_0(sK1))))),
% 0.20/0.48    inference(resolution,[],[f158,f75])).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f46])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | ~sP0(X0,X1,X2))),
% 0.20/0.48    inference(nnf_transformation,[],[f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | ~sP0(X0,X1,X2))),
% 0.20/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.48  fof(f158,plain,(
% 0.20/0.48    sP0(k2_struct_0(sK1),k2_relat_1(sK3),sK3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f157,f50])).
% 0.20/0.48  fof(f157,plain,(
% 0.20/0.48    sP0(k2_struct_0(sK1),k2_relat_1(sK3),sK3) | ~v1_funct_1(sK3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f156,f118])).
% 0.20/0.48  fof(f118,plain,(
% 0.20/0.48    v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3))),
% 0.20/0.48    inference(backward_demodulation,[],[f87,f113])).
% 0.20/0.48  fof(f113,plain,(
% 0.20/0.48    k2_struct_0(sK2) = k2_relat_1(sK3)),
% 0.20/0.48    inference(backward_demodulation,[],[f89,f111])).
% 0.20/0.48  fof(f111,plain,(
% 0.20/0.48    k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_relat_1(sK3)),
% 0.20/0.48    inference(resolution,[],[f70,f88])).
% 0.20/0.48  fof(f89,plain,(
% 0.20/0.48    k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3)),
% 0.20/0.48    inference(forward_demodulation,[],[f84,f83])).
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK2),sK3)),
% 0.20/0.48    inference(backward_demodulation,[],[f53,f82])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f45])).
% 0.20/0.48  fof(f87,plain,(
% 0.20/0.48    v1_funct_2(sK3,k2_struct_0(sK1),k2_struct_0(sK2))),
% 0.20/0.48    inference(forward_demodulation,[],[f86,f83])).
% 0.20/0.48  fof(f86,plain,(
% 0.20/0.48    v1_funct_2(sK3,k2_struct_0(sK1),u1_struct_0(sK2))),
% 0.20/0.48    inference(backward_demodulation,[],[f51,f82])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))),
% 0.20/0.48    inference(cnf_transformation,[],[f45])).
% 0.20/0.48  fof(f156,plain,(
% 0.20/0.48    sP0(k2_struct_0(sK1),k2_relat_1(sK3),sK3) | ~v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) | ~v1_funct_1(sK3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f155,f54])).
% 0.20/0.48  fof(f155,plain,(
% 0.20/0.48    ~v2_funct_1(sK3) | sP0(k2_struct_0(sK1),k2_relat_1(sK3),sK3) | ~v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) | ~v1_funct_1(sK3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f152,f114])).
% 0.20/0.48  fof(f114,plain,(
% 0.20/0.48    k2_relat_1(sK3) = k2_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3)),
% 0.20/0.48    inference(backward_demodulation,[],[f111,f113])).
% 0.20/0.48  fof(f152,plain,(
% 0.20/0.48    k2_relat_1(sK3) != k2_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3) | ~v2_funct_1(sK3) | sP0(k2_struct_0(sK1),k2_relat_1(sK3),sK3) | ~v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) | ~v1_funct_1(sK3)),
% 0.20/0.48    inference(resolution,[],[f76,f117])).
% 0.20/0.48  fof(f117,plain,(
% 0.20/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3))))),
% 0.20/0.48    inference(backward_demodulation,[],[f88,f113])).
% 0.20/0.48  fof(f76,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | sP0(X0,X1,X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (sP0(X0,X1,X2) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.48    inference(definition_folding,[],[f35,f40])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.48    inference(flattening,[],[f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.48    inference(ennf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.20/0.48  fof(f189,plain,(
% 0.20/0.48    k2_struct_0(sK1) != k2_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3))),
% 0.20/0.48    inference(subsumption_resolution,[],[f172,f181])).
% 0.20/0.48  fof(f181,plain,(
% 0.20/0.48    k2_relat_1(sK3) = k1_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3))),
% 0.20/0.48    inference(forward_demodulation,[],[f174,f100])).
% 0.20/0.48  fof(f100,plain,(
% 0.20/0.48    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))),
% 0.20/0.48    inference(subsumption_resolution,[],[f99,f96])).
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f98,f50])).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.20/0.48    inference(resolution,[],[f63,f54])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f26])).
% 0.20/0.48  fof(f174,plain,(
% 0.20/0.48    k1_relat_1(k2_funct_1(sK3)) = k1_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3))),
% 0.20/0.48    inference(resolution,[],[f159,f69])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.48  fof(f172,plain,(
% 0.20/0.48    k2_struct_0(sK1) != k2_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3))),
% 0.20/0.48    inference(forward_demodulation,[],[f171,f170])).
% 0.20/0.48  fof(f170,plain,(
% 0.20/0.48    k2_funct_1(sK3) = k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f169,f50])).
% 0.20/0.48  fof(f169,plain,(
% 0.20/0.48    k2_funct_1(sK3) = k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) | ~v1_funct_1(sK3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f168,f118])).
% 0.20/0.48  fof(f168,plain,(
% 0.20/0.48    k2_funct_1(sK3) = k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) | ~v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) | ~v1_funct_1(sK3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f167,f114])).
% 0.20/0.48  fof(f167,plain,(
% 0.20/0.48    k2_relat_1(sK3) != k2_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3) | k2_funct_1(sK3) = k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) | ~v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) | ~v1_funct_1(sK3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f164,f54])).
% 0.20/0.48  fof(f164,plain,(
% 0.20/0.48    ~v2_funct_1(sK3) | k2_relat_1(sK3) != k2_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3) | k2_funct_1(sK3) = k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) | ~v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) | ~v1_funct_1(sK3)),
% 0.20/0.48    inference(resolution,[],[f77,f117])).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.48    inference(flattening,[],[f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.48    inference(ennf_transformation,[],[f17])).
% 0.20/0.49  % (11594)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.49  % (11596)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (11606)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.49  % (11608)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.49  fof(f17,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 0.20/0.49  fof(f171,plain,(
% 0.20/0.49    k2_relat_1(sK3) != k1_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) | k2_struct_0(sK1) != k2_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3))),
% 0.20/0.49    inference(backward_demodulation,[],[f149,f170])).
% 0.20/0.49  fof(f149,plain,(
% 0.20/0.49    k2_struct_0(sK1) != k2_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)) | k2_relat_1(sK3) != k1_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3))),
% 0.20/0.49    inference(forward_demodulation,[],[f148,f113])).
% 0.20/0.49  fof(f148,plain,(
% 0.20/0.49    k2_struct_0(sK2) != k1_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)) | k2_struct_0(sK1) != k2_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3))),
% 0.20/0.49    inference(forward_demodulation,[],[f147,f82])).
% 0.20/0.49  fof(f147,plain,(
% 0.20/0.49    k2_struct_0(sK2) != k1_relset_1(k2_relat_1(sK3),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),k2_relat_1(sK3),sK3)) | k2_struct_0(sK1) != k2_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3))),
% 0.20/0.49    inference(forward_demodulation,[],[f146,f119])).
% 0.20/0.49  fof(f119,plain,(
% 0.20/0.49    u1_struct_0(sK2) = k2_relat_1(sK3)),
% 0.20/0.49    inference(backward_demodulation,[],[f83,f113])).
% 0.20/0.49  fof(f146,plain,(
% 0.20/0.49    k2_struct_0(sK1) != k2_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)) | k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))),
% 0.20/0.49    inference(forward_demodulation,[],[f145,f82])).
% 0.20/0.49  fof(f145,plain,(
% 0.20/0.49    k2_struct_0(sK1) != k2_relset_1(k2_relat_1(sK3),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),k2_relat_1(sK3),sK3)) | k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))),
% 0.20/0.49    inference(forward_demodulation,[],[f55,f119])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) | k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))),
% 0.20/0.49    inference(cnf_transformation,[],[f45])).
% 0.20/0.49  fof(f208,plain,(
% 0.20/0.49    k2_struct_0(sK1) = k1_relat_1(sK3) | k1_xboole_0 = k2_relat_1(sK3)),
% 0.20/0.49    inference(superposition,[],[f207,f144])).
% 0.20/0.49  fof(f144,plain,(
% 0.20/0.49    ( ! [X2] : (k1_relat_1(k6_partfun1(X2)) = X2) )),
% 0.20/0.49    inference(backward_demodulation,[],[f109,f142])).
% 0.20/0.49  fof(f142,plain,(
% 0.20/0.49    ( ! [X2] : (k1_relset_1(X2,X2,k6_partfun1(X2)) = X2) )),
% 0.20/0.49    inference(forward_demodulation,[],[f139,f104])).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    ( ! [X0] : (k8_relset_1(X0,X0,k6_partfun1(X0),X0) = X0) )),
% 0.20/0.49    inference(resolution,[],[f67,f81])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f59,f57])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).
% 0.20/0.49  fof(f139,plain,(
% 0.20/0.49    ( ! [X2] : (k1_relset_1(X2,X2,k6_partfun1(X2)) = k8_relset_1(X2,X2,k6_partfun1(X2),X2)) )),
% 0.20/0.49    inference(resolution,[],[f72,f80])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f60,f58])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 0.20/0.49  fof(f109,plain,(
% 0.20/0.49    ( ! [X2] : (k1_relset_1(X2,X2,k6_partfun1(X2)) = k1_relat_1(k6_partfun1(X2))) )),
% 0.20/0.49    inference(resolution,[],[f69,f80])).
% 0.20/0.49  fof(f207,plain,(
% 0.20/0.49    k1_relat_1(sK3) = k1_relat_1(k6_partfun1(k2_struct_0(sK1))) | k1_xboole_0 = k2_relat_1(sK3)),
% 0.20/0.49    inference(superposition,[],[f127,f205])).
% 0.20/0.49  fof(f205,plain,(
% 0.20/0.49    k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k2_struct_0(sK1)) | k1_xboole_0 = k2_relat_1(sK3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f204,f50])).
% 0.20/0.49  fof(f204,plain,(
% 0.20/0.49    k1_xboole_0 = k2_relat_1(sK3) | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k2_struct_0(sK1)) | ~v1_funct_1(sK3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f203,f118])).
% 0.20/0.49  fof(f203,plain,(
% 0.20/0.49    k1_xboole_0 = k2_relat_1(sK3) | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k2_struct_0(sK1)) | ~v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) | ~v1_funct_1(sK3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f202,f114])).
% 0.20/0.49  fof(f202,plain,(
% 0.20/0.49    k1_xboole_0 = k2_relat_1(sK3) | k2_relat_1(sK3) != k2_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3) | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k2_struct_0(sK1)) | ~v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) | ~v1_funct_1(sK3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f196,f54])).
% 0.20/0.49  fof(f196,plain,(
% 0.20/0.49    k1_xboole_0 = k2_relat_1(sK3) | ~v2_funct_1(sK3) | k2_relat_1(sK3) != k2_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3) | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k2_struct_0(sK1)) | ~v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) | ~v1_funct_1(sK3)),
% 0.20/0.49    inference(resolution,[],[f78,f117])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.49    inference(flattening,[],[f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.49    inference(ennf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 0.20/0.49  fof(f127,plain,(
% 0.20/0.49    k1_relat_1(sK3) = k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)))),
% 0.20/0.49    inference(subsumption_resolution,[],[f126,f96])).
% 0.20/0.49  fof(f126,plain,(
% 0.20/0.49    k1_relat_1(sK3) = k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) | ~v1_relat_1(sK3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f125,f50])).
% 0.20/0.49  fof(f125,plain,(
% 0.20/0.49    k1_relat_1(sK3) = k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.20/0.49    inference(resolution,[],[f65,f54])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(flattening,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    ~v1_xboole_0(k2_relat_1(sK3))),
% 0.20/0.49    inference(backward_demodulation,[],[f94,f113])).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    ~v1_xboole_0(k2_struct_0(sK2))),
% 0.20/0.49    inference(subsumption_resolution,[],[f93,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ~v2_struct_0(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f45])).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    ~v1_xboole_0(k2_struct_0(sK2)) | v2_struct_0(sK2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f91,f49])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    ~v1_xboole_0(k2_struct_0(sK2)) | ~l1_struct_0(sK2) | v2_struct_0(sK2)),
% 0.20/0.49    inference(superposition,[],[f62,f83])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,axiom,(
% 0.20/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (11604)------------------------------
% 0.20/0.49  % (11604)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (11604)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (11604)Memory used [KB]: 1791
% 0.20/0.49  % (11604)Time elapsed: 0.081 s
% 0.20/0.49  % (11604)------------------------------
% 0.20/0.49  % (11604)------------------------------
% 0.20/0.49  % (11591)Success in time 0.139 s
%------------------------------------------------------------------------------
