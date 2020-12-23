%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT2012+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:46 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 111 expanded)
%              Number of leaves         :   22 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :   79 ( 220 expanded)
%              Number of equality atoms :   20 (  67 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_waybel_0 > l1_waybel_0 > v1_orders_2 > l1_orders_2 > k3_relset_1 > u1_waybel_0 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k7_lattice3 > k3_waybel_9 > k3_struct_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v6_waybel_0,type,(
    v6_waybel_0: ( $i * $i ) > $o )).

tff(k3_waybel_9,type,(
    k3_waybel_9: $i > $i )).

tff(k3_relset_1,type,(
    k3_relset_1: ( $i * $i * $i ) > $i )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff(k7_lattice3,type,(
    k7_lattice3: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(u1_waybel_0,type,(
    u1_waybel_0: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k3_struct_0,type,(
    k3_struct_0: $i > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => g1_orders_2(u1_struct_0(k7_lattice3(A)),u1_orders_2(k7_lattice3(A))) = g1_orders_2(u1_struct_0(k3_waybel_9(A)),u1_orders_2(k3_waybel_9(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_waybel_9)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_orders_2(k7_lattice3(A))
        & l1_orders_2(k7_lattice3(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattice3)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v6_waybel_0(k3_waybel_9(A),A)
        & l1_waybel_0(k3_waybel_9(A),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_waybel_9)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( ( v6_waybel_0(B,A)
            & l1_waybel_0(B,A) )
         => ( B = k3_waybel_9(A)
          <=> ( u1_struct_0(B) = u1_struct_0(A)
              & u1_orders_2(B) = k3_relset_1(u1_struct_0(A),u1_struct_0(A),u1_orders_2(A))
              & u1_waybel_0(A,B) = k3_struct_0(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_waybel_9)).

tff(f_34,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k7_lattice3(A) = g1_orders_2(u1_struct_0(A),k3_relset_1(u1_struct_0(A),u1_struct_0(A),u1_orders_2(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_lattice3)).

tff(f_30,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_orders_2(A)
       => A = g1_orders_2(u1_struct_0(A),u1_orders_2(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

tff(c_24,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_20,plain,(
    ! [A_7] :
      ( v1_orders_2(k7_lattice3(A_7))
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14,plain,(
    ! [A_6] :
      ( l1_waybel_0(k3_waybel_9(A_6),A_6)
      | ~ l1_orders_2(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    ! [A_6] :
      ( v6_waybel_0(k3_waybel_9(A_6),A_6)
      | ~ l1_orders_2(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_137,plain,(
    ! [A_21] :
      ( k3_relset_1(u1_struct_0(A_21),u1_struct_0(A_21),u1_orders_2(A_21)) = u1_orders_2(k3_waybel_9(A_21))
      | ~ l1_waybel_0(k3_waybel_9(A_21),A_21)
      | ~ v6_waybel_0(k3_waybel_9(A_21),A_21)
      | ~ l1_orders_2(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [A_2] :
      ( g1_orders_2(u1_struct_0(A_2),k3_relset_1(u1_struct_0(A_2),u1_struct_0(A_2),u1_orders_2(A_2))) = k7_lattice3(A_2)
      | ~ l1_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_155,plain,(
    ! [A_22] :
      ( g1_orders_2(u1_struct_0(A_22),u1_orders_2(k3_waybel_9(A_22))) = k7_lattice3(A_22)
      | ~ l1_orders_2(A_22)
      | ~ l1_waybel_0(k3_waybel_9(A_22),A_22)
      | ~ v6_waybel_0(k3_waybel_9(A_22),A_22)
      | ~ l1_orders_2(A_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_4])).

tff(c_50,plain,(
    ! [A_14] :
      ( u1_struct_0(k3_waybel_9(A_14)) = u1_struct_0(A_14)
      | ~ l1_waybel_0(k3_waybel_9(A_14),A_14)
      | ~ v6_waybel_0(k3_waybel_9(A_14),A_14)
      | ~ l1_orders_2(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_65,plain,(
    ! [A_15] :
      ( u1_struct_0(k3_waybel_9(A_15)) = u1_struct_0(A_15)
      | ~ l1_waybel_0(k3_waybel_9(A_15),A_15)
      | ~ l1_orders_2(A_15) ) ),
    inference(resolution,[status(thm)],[c_16,c_50])).

tff(c_69,plain,(
    ! [A_6] :
      ( u1_struct_0(k3_waybel_9(A_6)) = u1_struct_0(A_6)
      | ~ l1_orders_2(A_6) ) ),
    inference(resolution,[status(thm)],[c_14,c_65])).

tff(c_18,plain,(
    ! [A_7] :
      ( l1_orders_2(k7_lattice3(A_7))
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_orders_2(u1_struct_0(A_1),u1_orders_2(A_1)) = A_1
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_22,plain,(
    g1_orders_2(u1_struct_0(k7_lattice3('#skF_1')),u1_orders_2(k7_lattice3('#skF_1'))) != g1_orders_2(u1_struct_0(k3_waybel_9('#skF_1')),u1_orders_2(k3_waybel_9('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_49,plain,
    ( g1_orders_2(u1_struct_0(k3_waybel_9('#skF_1')),u1_orders_2(k3_waybel_9('#skF_1'))) != k7_lattice3('#skF_1')
    | ~ v1_orders_2(k7_lattice3('#skF_1'))
    | ~ l1_orders_2(k7_lattice3('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_22])).

tff(c_55,plain,(
    ~ l1_orders_2(k7_lattice3('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_49])).

tff(c_58,plain,(
    ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_55])).

tff(c_62,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_58])).

tff(c_63,plain,
    ( ~ v1_orders_2(k7_lattice3('#skF_1'))
    | g1_orders_2(u1_struct_0(k3_waybel_9('#skF_1')),u1_orders_2(k3_waybel_9('#skF_1'))) != k7_lattice3('#skF_1') ),
    inference(splitRight,[status(thm)],[c_49])).

tff(c_91,plain,(
    g1_orders_2(u1_struct_0(k3_waybel_9('#skF_1')),u1_orders_2(k3_waybel_9('#skF_1'))) != k7_lattice3('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_99,plain,
    ( g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2(k3_waybel_9('#skF_1'))) != k7_lattice3('#skF_1')
    | ~ l1_orders_2('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_91])).

tff(c_104,plain,(
    g1_orders_2(u1_struct_0('#skF_1'),u1_orders_2(k3_waybel_9('#skF_1'))) != k7_lattice3('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_99])).

tff(c_164,plain,
    ( ~ l1_waybel_0(k3_waybel_9('#skF_1'),'#skF_1')
    | ~ v6_waybel_0(k3_waybel_9('#skF_1'),'#skF_1')
    | ~ l1_orders_2('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_104])).

tff(c_177,plain,
    ( ~ l1_waybel_0(k3_waybel_9('#skF_1'),'#skF_1')
    | ~ v6_waybel_0(k3_waybel_9('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_164])).

tff(c_186,plain,(
    ~ v6_waybel_0(k3_waybel_9('#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_177])).

tff(c_189,plain,(
    ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_186])).

tff(c_193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_189])).

tff(c_194,plain,(
    ~ l1_waybel_0(k3_waybel_9('#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_198,plain,(
    ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_194])).

tff(c_202,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_198])).

tff(c_203,plain,(
    ~ v1_orders_2(k7_lattice3('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_207,plain,(
    ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_203])).

tff(c_211,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_207])).

%------------------------------------------------------------------------------
