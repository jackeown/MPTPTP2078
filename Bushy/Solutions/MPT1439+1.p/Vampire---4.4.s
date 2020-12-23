%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : filter_1__t34_filter_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:09 EDT 2019

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 189 expanded)
%              Number of leaves         :    7 (  67 expanded)
%              Depth                    :   27
%              Number of atoms          :  394 (2101 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   20 (   8 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4262,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4261,f201])).

fof(f201,plain,(
    r1_filter_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f159])).

fof(f159,plain,
    ( ~ r1_filter_1(sK0,sK2)
    & r1_filter_1(sK1,sK2)
    & r1_filter_1(sK0,sK1)
    & l3_lattices(sK2)
    & v10_lattices(sK2)
    & ~ v2_struct_0(sK2)
    & l3_lattices(sK1)
    & v10_lattices(sK1)
    & ~ v2_struct_0(sK1)
    & l3_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f71,f158,f157,f156])).

fof(f156,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_filter_1(X0,X2)
                & r1_filter_1(X1,X2)
                & r1_filter_1(X0,X1)
                & l3_lattices(X2)
                & v10_lattices(X2)
                & ~ v2_struct_0(X2) )
            & l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1) )
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_filter_1(sK0,X2)
              & r1_filter_1(X1,X2)
              & r1_filter_1(sK0,X1)
              & l3_lattices(X2)
              & v10_lattices(X2)
              & ~ v2_struct_0(X2) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f157,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_filter_1(X0,X2)
              & r1_filter_1(X1,X2)
              & r1_filter_1(X0,X1)
              & l3_lattices(X2)
              & v10_lattices(X2)
              & ~ v2_struct_0(X2) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ~ r1_filter_1(X0,X2)
            & r1_filter_1(sK1,X2)
            & r1_filter_1(X0,sK1)
            & l3_lattices(X2)
            & v10_lattices(X2)
            & ~ v2_struct_0(X2) )
        & l3_lattices(sK1)
        & v10_lattices(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f158,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_filter_1(X0,X2)
          & r1_filter_1(X1,X2)
          & r1_filter_1(X0,X1)
          & l3_lattices(X2)
          & v10_lattices(X2)
          & ~ v2_struct_0(X2) )
     => ( ~ r1_filter_1(X0,sK2)
        & r1_filter_1(X1,sK2)
        & r1_filter_1(X0,X1)
        & l3_lattices(sK2)
        & v10_lattices(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_filter_1(X0,X2)
              & r1_filter_1(X1,X2)
              & r1_filter_1(X0,X1)
              & l3_lattices(X2)
              & v10_lattices(X2)
              & ~ v2_struct_0(X2) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_filter_1(X0,X2)
              & r1_filter_1(X1,X2)
              & r1_filter_1(X0,X1)
              & l3_lattices(X2)
              & v10_lattices(X2)
              & ~ v2_struct_0(X2) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l3_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( l3_lattices(X2)
                  & v10_lattices(X2)
                  & ~ v2_struct_0(X2) )
               => ( ( r1_filter_1(X1,X2)
                    & r1_filter_1(X0,X1) )
                 => r1_filter_1(X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( l3_lattices(X2)
                & v10_lattices(X2)
                & ~ v2_struct_0(X2) )
             => ( ( r1_filter_1(X1,X2)
                  & r1_filter_1(X0,X1) )
               => r1_filter_1(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t34_filter_1.p',t34_filter_1)).

fof(f4261,plain,(
    ~ r1_filter_1(sK1,sK2) ),
    inference(subsumption_resolution,[],[f4260,f194])).

fof(f194,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f159])).

fof(f4260,plain,
    ( v2_struct_0(sK1)
    | ~ r1_filter_1(sK1,sK2) ),
    inference(subsumption_resolution,[],[f4259,f200])).

fof(f200,plain,(
    r1_filter_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f159])).

fof(f4259,plain,
    ( ~ r1_filter_1(sK0,sK1)
    | v2_struct_0(sK1)
    | ~ r1_filter_1(sK1,sK2) ),
    inference(subsumption_resolution,[],[f4257,f196])).

fof(f196,plain,(
    l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f159])).

fof(f4257,plain,
    ( ~ l3_lattices(sK1)
    | ~ r1_filter_1(sK0,sK1)
    | v2_struct_0(sK1)
    | ~ r1_filter_1(sK1,sK2) ),
    inference(resolution,[],[f4253,f195])).

fof(f195,plain,(
    v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f159])).

fof(f4253,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ r1_filter_1(sK0,X0)
      | v2_struct_0(X0)
      | ~ r1_filter_1(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f4252,f197])).

fof(f197,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f159])).

fof(f4252,plain,(
    ! [X0] :
      ( ~ r1_filter_1(sK0,X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ r1_filter_1(X0,sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f4251,f198])).

fof(f198,plain,(
    v10_lattices(sK2) ),
    inference(cnf_transformation,[],[f159])).

fof(f4251,plain,(
    ! [X0] :
      ( ~ r1_filter_1(sK0,X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ r1_filter_1(X0,sK2)
      | ~ v10_lattices(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f4250,f199])).

fof(f199,plain,(
    l3_lattices(sK2) ),
    inference(cnf_transformation,[],[f159])).

fof(f4250,plain,(
    ! [X0] :
      ( ~ r1_filter_1(sK0,X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ r1_filter_1(X0,sK2)
      | ~ l3_lattices(sK2)
      | ~ v10_lattices(sK2)
      | v2_struct_0(sK2) ) ),
    inference(duplicate_literal_removal,[],[f4248])).

fof(f4248,plain,(
    ! [X0] :
      ( ~ r1_filter_1(sK0,X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ r1_filter_1(X0,sK2)
      | ~ l3_lattices(sK2)
      | ~ v10_lattices(sK2)
      | v2_struct_0(sK2)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f4241,f251])).

fof(f251,plain,(
    ! [X0,X1] :
      ( r4_wellord1(k8_filter_1(X0),k8_filter_1(X1))
      | ~ r1_filter_1(X0,X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f160])).

fof(f160,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_filter_1(X0,X1)
              | ~ r4_wellord1(k8_filter_1(X0),k8_filter_1(X1)) )
            & ( r4_wellord1(k8_filter_1(X0),k8_filter_1(X1))
              | ~ r1_filter_1(X0,X1) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f118])).

fof(f118,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_filter_1(X0,X1)
          <=> r4_wellord1(k8_filter_1(X0),k8_filter_1(X1)) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f117])).

fof(f117,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_filter_1(X0,X1)
          <=> r4_wellord1(k8_filter_1(X0),k8_filter_1(X1)) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1) )
         => ( r1_filter_1(X0,X1)
          <=> r4_wellord1(k8_filter_1(X0),k8_filter_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t34_filter_1.p',d9_filter_1)).

fof(f4241,plain,(
    ! [X0] :
      ( ~ r4_wellord1(k8_filter_1(X0),k8_filter_1(sK2))
      | ~ r1_filter_1(sK0,X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f4240,f199])).

fof(f4240,plain,(
    ! [X0] :
      ( ~ r4_wellord1(k8_filter_1(X0),k8_filter_1(sK2))
      | ~ l3_lattices(sK2)
      | ~ r1_filter_1(sK0,X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f4239,f191])).

fof(f191,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f159])).

fof(f4239,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ r4_wellord1(k8_filter_1(X0),k8_filter_1(sK2))
      | ~ l3_lattices(sK2)
      | ~ r1_filter_1(sK0,X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f4238,f192])).

fof(f192,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f159])).

fof(f4238,plain,(
    ! [X0] :
      ( ~ v10_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ r4_wellord1(k8_filter_1(X0),k8_filter_1(sK2))
      | ~ l3_lattices(sK2)
      | ~ r1_filter_1(sK0,X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f4237,f193])).

fof(f193,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f159])).

fof(f4237,plain,(
    ! [X0] :
      ( ~ l3_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ r4_wellord1(k8_filter_1(X0),k8_filter_1(sK2))
      | ~ l3_lattices(sK2)
      | ~ r1_filter_1(sK0,X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f4236,f197])).

fof(f4236,plain,(
    ! [X0] :
      ( v2_struct_0(sK2)
      | ~ l3_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ r4_wellord1(k8_filter_1(X0),k8_filter_1(sK2))
      | ~ l3_lattices(sK2)
      | ~ r1_filter_1(sK0,X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f4234,f198])).

fof(f4234,plain,(
    ! [X0] :
      ( ~ v10_lattices(sK2)
      | v2_struct_0(sK2)
      | ~ l3_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ r4_wellord1(k8_filter_1(X0),k8_filter_1(sK2))
      | ~ l3_lattices(sK2)
      | ~ r1_filter_1(sK0,X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f1286,f202])).

fof(f202,plain,(
    ~ r1_filter_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f159])).

fof(f1286,plain,(
    ! [X2,X0,X1] :
      ( r1_filter_1(X1,X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ r4_wellord1(k8_filter_1(X2),k8_filter_1(X0))
      | ~ l3_lattices(X0)
      | ~ r1_filter_1(X1,X2)
      | ~ l3_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f1285,f249])).

fof(f249,plain,(
    ! [X0] :
      ( v1_relat_1(k8_filter_1(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f114])).

fof(f114,plain,(
    ! [X0] :
      ( v1_relat_1(k8_filter_1(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f113])).

fof(f113,plain,(
    ! [X0] :
      ( v1_relat_1(k8_filter_1(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => v1_relat_1(k8_filter_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t34_filter_1.p',dt_k8_filter_1)).

fof(f1285,plain,(
    ! [X2,X0,X1] :
      ( ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ r4_wellord1(k8_filter_1(X2),k8_filter_1(X0))
      | r1_filter_1(X1,X0)
      | ~ v1_relat_1(k8_filter_1(X2))
      | ~ r1_filter_1(X1,X2)
      | ~ l3_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(duplicate_literal_removal,[],[f1282])).

fof(f1282,plain,(
    ! [X2,X0,X1] :
      ( ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ r4_wellord1(k8_filter_1(X2),k8_filter_1(X0))
      | r1_filter_1(X1,X0)
      | ~ v1_relat_1(k8_filter_1(X2))
      | ~ r1_filter_1(X1,X2)
      | ~ l3_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f373,f251])).

fof(f373,plain,(
    ! [X4,X2,X3] :
      ( ~ r4_wellord1(k8_filter_1(X2),X4)
      | ~ l3_lattices(X3)
      | ~ v10_lattices(X3)
      | v2_struct_0(X3)
      | ~ l3_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2)
      | ~ r4_wellord1(X4,k8_filter_1(X3))
      | r1_filter_1(X2,X3)
      | ~ v1_relat_1(X4) ) ),
    inference(subsumption_resolution,[],[f372,f249])).

fof(f372,plain,(
    ! [X4,X2,X3] :
      ( r1_filter_1(X2,X3)
      | ~ l3_lattices(X3)
      | ~ v10_lattices(X3)
      | v2_struct_0(X3)
      | ~ l3_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2)
      | ~ r4_wellord1(X4,k8_filter_1(X3))
      | ~ r4_wellord1(k8_filter_1(X2),X4)
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(k8_filter_1(X2)) ) ),
    inference(subsumption_resolution,[],[f370,f249])).

fof(f370,plain,(
    ! [X4,X2,X3] :
      ( r1_filter_1(X2,X3)
      | ~ l3_lattices(X3)
      | ~ v10_lattices(X3)
      | v2_struct_0(X3)
      | ~ l3_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2)
      | ~ r4_wellord1(X4,k8_filter_1(X3))
      | ~ r4_wellord1(k8_filter_1(X2),X4)
      | ~ v1_relat_1(k8_filter_1(X3))
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(k8_filter_1(X2)) ) ),
    inference(resolution,[],[f252,f242])).

fof(f242,plain,(
    ! [X2,X0,X1] :
      ( r4_wellord1(X0,X2)
      | ~ r4_wellord1(X1,X2)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f103])).

fof(f103,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_wellord1(X0,X2)
              | ~ r4_wellord1(X1,X2)
              | ~ r4_wellord1(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f102])).

fof(f102,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_wellord1(X0,X2)
              | ~ r4_wellord1(X1,X2)
              | ~ r4_wellord1(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f66])).

fof(f66,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( ( r4_wellord1(X1,X2)
                  & r4_wellord1(X0,X1) )
               => r4_wellord1(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t34_filter_1.p',t52_wellord1)).

fof(f252,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k8_filter_1(X0),k8_filter_1(X1))
      | r1_filter_1(X0,X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f160])).
%------------------------------------------------------------------------------
