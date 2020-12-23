%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:37 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 539 expanded)
%              Number of leaves         :   19 ( 202 expanded)
%              Depth                    :   11
%              Number of atoms          :  444 (2412 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_lattices > v2_struct_0 > v15_lattices > v14_lattices > v13_lattices > v10_lattices > l3_lattices > k7_filter_1 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v14_lattices,type,(
    v14_lattices: $i > $o )).

tff(v13_lattices,type,(
    v13_lattices: $i > $o )).

tff(k7_filter_1,type,(
    k7_filter_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v3_lattices,type,(
    v3_lattices: $i > $o )).

tff(v15_lattices,type,(
    v15_lattices: $i > $o )).

tff(f_129,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v10_lattices(B)
              & l3_lattices(B) )
           => ( ( v15_lattices(A)
                & v15_lattices(B) )
            <=> v15_lattices(k7_filter_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_filter_1)).

tff(f_36,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( v15_lattices(A)
      <=> ( v13_lattices(A)
          & v14_lattices(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_lattices)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A)
        & ~ v2_struct_0(B)
        & l3_lattices(B) )
     => ( v3_lattices(k7_filter_1(A,B))
        & l3_lattices(k7_filter_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_filter_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A)
        & ~ v2_struct_0(B)
        & l3_lattices(B) )
     => ( ~ v2_struct_0(k7_filter_1(A,B))
        & v3_lattices(k7_filter_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_filter_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v10_lattices(B)
            & l3_lattices(B) )
         => ( ( v13_lattices(A)
              & v13_lattices(B) )
          <=> v13_lattices(k7_filter_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_filter_1)).

tff(f_107,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v10_lattices(B)
            & l3_lattices(B) )
         => ( ( v14_lattices(A)
              & v14_lattices(B) )
          <=> v14_lattices(k7_filter_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_filter_1)).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_36,plain,(
    v10_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_34,plain,(
    l3_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_30,plain,(
    v10_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_28,plain,(
    l3_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_50,plain,
    ( v15_lattices('#skF_1')
    | v15_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_51,plain,(
    v15_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_40,plain,
    ( ~ v15_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v15_lattices('#skF_2')
    | ~ v15_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_54,plain,
    ( ~ v15_lattices('#skF_2')
    | ~ v15_lattices('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_40])).

tff(c_55,plain,(
    ~ v15_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_351,plain,(
    ! [A_79] :
      ( v15_lattices(A_79)
      | ~ v14_lattices(A_79)
      | ~ v13_lattices(A_79)
      | ~ l3_lattices(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_357,plain,
    ( v15_lattices('#skF_1')
    | ~ v14_lattices('#skF_1')
    | ~ v13_lattices('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_351,c_38])).

tff(c_363,plain,
    ( v15_lattices('#skF_1')
    | ~ v14_lattices('#skF_1')
    | ~ v13_lattices('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_357])).

tff(c_364,plain,
    ( ~ v14_lattices('#skF_1')
    | ~ v13_lattices('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_363])).

tff(c_365,plain,(
    ~ v13_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_364])).

tff(c_8,plain,(
    ! [A_2,B_3] :
      ( l3_lattices(k7_filter_1(A_2,B_3))
      | ~ l3_lattices(B_3)
      | v2_struct_0(B_3)
      | ~ l3_lattices(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6,plain,(
    ! [A_1] :
      ( v13_lattices(A_1)
      | ~ v15_lattices(A_1)
      | ~ l3_lattices(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_366,plain,(
    ! [A_80,B_81] :
      ( ~ v2_struct_0(k7_filter_1(A_80,B_81))
      | ~ l3_lattices(B_81)
      | v2_struct_0(B_81)
      | ~ l3_lattices(A_80)
      | v2_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_403,plain,(
    ! [B_98,A_99] :
      ( ~ l3_lattices(B_98)
      | v2_struct_0(B_98)
      | ~ l3_lattices(A_99)
      | v2_struct_0(A_99)
      | v13_lattices(k7_filter_1(A_99,B_98))
      | ~ v15_lattices(k7_filter_1(A_99,B_98))
      | ~ l3_lattices(k7_filter_1(A_99,B_98)) ) ),
    inference(resolution,[status(thm)],[c_6,c_366])).

tff(c_406,plain,
    ( ~ l3_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | v13_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_51,c_403])).

tff(c_409,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1')
    | v13_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_406])).

tff(c_410,plain,
    ( v13_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_409])).

tff(c_411,plain,(
    ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_410])).

tff(c_414,plain,
    ( ~ l3_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_411])).

tff(c_417,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_414])).

tff(c_419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_417])).

tff(c_420,plain,(
    v13_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_410])).

tff(c_20,plain,(
    ! [A_6,B_8] :
      ( v13_lattices(A_6)
      | ~ v13_lattices(k7_filter_1(A_6,B_8))
      | ~ l3_lattices(B_8)
      | ~ v10_lattices(B_8)
      | v2_struct_0(B_8)
      | ~ l3_lattices(A_6)
      | ~ v10_lattices(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_424,plain,
    ( v13_lattices('#skF_1')
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_420,c_20])).

tff(c_430,plain,
    ( v13_lattices('#skF_1')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_28,c_424])).

tff(c_432,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_365,c_430])).

tff(c_433,plain,(
    ~ v14_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_364])).

tff(c_4,plain,(
    ! [A_1] :
      ( v14_lattices(A_1)
      | ~ v15_lattices(A_1)
      | ~ l3_lattices(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_435,plain,(
    ! [A_100,B_101] :
      ( ~ v2_struct_0(k7_filter_1(A_100,B_101))
      | ~ l3_lattices(B_101)
      | v2_struct_0(B_101)
      | ~ l3_lattices(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_472,plain,(
    ! [B_118,A_119] :
      ( ~ l3_lattices(B_118)
      | v2_struct_0(B_118)
      | ~ l3_lattices(A_119)
      | v2_struct_0(A_119)
      | v14_lattices(k7_filter_1(A_119,B_118))
      | ~ v15_lattices(k7_filter_1(A_119,B_118))
      | ~ l3_lattices(k7_filter_1(A_119,B_118)) ) ),
    inference(resolution,[status(thm)],[c_4,c_435])).

tff(c_475,plain,
    ( ~ l3_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | v14_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_51,c_472])).

tff(c_478,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1')
    | v14_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_475])).

tff(c_479,plain,
    ( v14_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_478])).

tff(c_488,plain,(
    ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_479])).

tff(c_491,plain,
    ( ~ l3_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_488])).

tff(c_494,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_491])).

tff(c_496,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_494])).

tff(c_497,plain,(
    v14_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_479])).

tff(c_26,plain,(
    ! [A_9,B_11] :
      ( v14_lattices(A_9)
      | ~ v14_lattices(k7_filter_1(A_9,B_11))
      | ~ l3_lattices(B_11)
      | ~ v10_lattices(B_11)
      | v2_struct_0(B_11)
      | ~ l3_lattices(A_9)
      | ~ v10_lattices(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_517,plain,
    ( v14_lattices('#skF_1')
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_497,c_26])).

tff(c_523,plain,
    ( v14_lattices('#skF_1')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_28,c_517])).

tff(c_525,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_433,c_523])).

tff(c_526,plain,(
    ~ v15_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_554,plain,(
    ! [A_124] :
      ( v15_lattices(A_124)
      | ~ v14_lattices(A_124)
      | ~ v13_lattices(A_124)
      | ~ l3_lattices(A_124)
      | v2_struct_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_557,plain,
    ( v15_lattices('#skF_2')
    | ~ v14_lattices('#skF_2')
    | ~ v13_lattices('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_554,c_32])).

tff(c_563,plain,
    ( v15_lattices('#skF_2')
    | ~ v14_lattices('#skF_2')
    | ~ v13_lattices('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_557])).

tff(c_564,plain,
    ( ~ v14_lattices('#skF_2')
    | ~ v13_lattices('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_526,c_563])).

tff(c_568,plain,(
    ~ v13_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_564])).

tff(c_571,plain,(
    ! [A_129,B_130] :
      ( ~ v2_struct_0(k7_filter_1(A_129,B_130))
      | ~ l3_lattices(B_130)
      | v2_struct_0(B_130)
      | ~ l3_lattices(A_129)
      | v2_struct_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_606,plain,(
    ! [B_143,A_144] :
      ( ~ l3_lattices(B_143)
      | v2_struct_0(B_143)
      | ~ l3_lattices(A_144)
      | v2_struct_0(A_144)
      | v14_lattices(k7_filter_1(A_144,B_143))
      | ~ v15_lattices(k7_filter_1(A_144,B_143))
      | ~ l3_lattices(k7_filter_1(A_144,B_143)) ) ),
    inference(resolution,[status(thm)],[c_4,c_571])).

tff(c_609,plain,
    ( ~ l3_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | v14_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_51,c_606])).

tff(c_612,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1')
    | v14_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_609])).

tff(c_613,plain,
    ( v14_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_612])).

tff(c_614,plain,(
    ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_613])).

tff(c_617,plain,
    ( ~ l3_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_614])).

tff(c_620,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_617])).

tff(c_622,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_620])).

tff(c_624,plain,(
    l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_613])).

tff(c_639,plain,(
    ! [B_145,A_146] :
      ( ~ l3_lattices(B_145)
      | v2_struct_0(B_145)
      | ~ l3_lattices(A_146)
      | v2_struct_0(A_146)
      | v13_lattices(k7_filter_1(A_146,B_145))
      | ~ v15_lattices(k7_filter_1(A_146,B_145))
      | ~ l3_lattices(k7_filter_1(A_146,B_145)) ) ),
    inference(resolution,[status(thm)],[c_6,c_571])).

tff(c_642,plain,
    ( ~ l3_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | v13_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_51,c_639])).

tff(c_645,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1')
    | v13_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_624,c_34,c_28,c_642])).

tff(c_646,plain,(
    v13_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_645])).

tff(c_18,plain,(
    ! [B_8,A_6] :
      ( v13_lattices(B_8)
      | ~ v13_lattices(k7_filter_1(A_6,B_8))
      | ~ l3_lattices(B_8)
      | ~ v10_lattices(B_8)
      | v2_struct_0(B_8)
      | ~ l3_lattices(A_6)
      | ~ v10_lattices(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_652,plain,
    ( v13_lattices('#skF_2')
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_646,c_18])).

tff(c_659,plain,
    ( v13_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_28,c_652])).

tff(c_661,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_568,c_659])).

tff(c_662,plain,(
    ~ v14_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_564])).

tff(c_664,plain,(
    ! [A_147,B_148] :
      ( ~ v2_struct_0(k7_filter_1(A_147,B_148))
      | ~ l3_lattices(B_148)
      | v2_struct_0(B_148)
      | ~ l3_lattices(A_147)
      | v2_struct_0(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_701,plain,(
    ! [B_165,A_166] :
      ( ~ l3_lattices(B_165)
      | v2_struct_0(B_165)
      | ~ l3_lattices(A_166)
      | v2_struct_0(A_166)
      | v14_lattices(k7_filter_1(A_166,B_165))
      | ~ v15_lattices(k7_filter_1(A_166,B_165))
      | ~ l3_lattices(k7_filter_1(A_166,B_165)) ) ),
    inference(resolution,[status(thm)],[c_4,c_664])).

tff(c_704,plain,
    ( ~ l3_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | v14_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_51,c_701])).

tff(c_707,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1')
    | v14_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_704])).

tff(c_708,plain,
    ( v14_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_707])).

tff(c_709,plain,(
    ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_708])).

tff(c_712,plain,
    ( ~ l3_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_709])).

tff(c_715,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_712])).

tff(c_717,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_715])).

tff(c_718,plain,(
    v14_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_708])).

tff(c_24,plain,(
    ! [B_11,A_9] :
      ( v14_lattices(B_11)
      | ~ v14_lattices(k7_filter_1(A_9,B_11))
      | ~ l3_lattices(B_11)
      | ~ v10_lattices(B_11)
      | v2_struct_0(B_11)
      | ~ l3_lattices(A_9)
      | ~ v10_lattices(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_725,plain,
    ( v14_lattices('#skF_2')
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_718,c_24])).

tff(c_732,plain,
    ( v14_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_28,c_725])).

tff(c_734,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_662,c_732])).

tff(c_735,plain,(
    v15_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_753,plain,(
    ! [A_168] :
      ( v13_lattices(A_168)
      | ~ v15_lattices(A_168)
      | ~ l3_lattices(A_168)
      | v2_struct_0(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_759,plain,
    ( v13_lattices('#skF_1')
    | ~ v15_lattices('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_753,c_38])).

tff(c_765,plain,(
    v13_lattices('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_735,c_759])).

tff(c_736,plain,(
    ~ v15_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,
    ( v15_lattices('#skF_2')
    | v15_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_737,plain,(
    v15_lattices('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_736,c_48])).

tff(c_756,plain,
    ( v13_lattices('#skF_2')
    | ~ v15_lattices('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_753,c_32])).

tff(c_762,plain,(
    v13_lattices('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_737,c_756])).

tff(c_16,plain,(
    ! [A_6,B_8] :
      ( v13_lattices(k7_filter_1(A_6,B_8))
      | ~ v13_lattices(B_8)
      | ~ v13_lattices(A_6)
      | ~ l3_lattices(B_8)
      | ~ v10_lattices(B_8)
      | v2_struct_0(B_8)
      | ~ l3_lattices(A_6)
      | ~ v10_lattices(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_738,plain,(
    ! [A_167] :
      ( v14_lattices(A_167)
      | ~ v15_lattices(A_167)
      | ~ l3_lattices(A_167)
      | v2_struct_0(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_744,plain,
    ( v14_lattices('#skF_1')
    | ~ v15_lattices('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_738,c_38])).

tff(c_750,plain,(
    v14_lattices('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_735,c_744])).

tff(c_741,plain,
    ( v14_lattices('#skF_2')
    | ~ v15_lattices('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_738,c_32])).

tff(c_747,plain,(
    v14_lattices('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_737,c_741])).

tff(c_22,plain,(
    ! [A_9,B_11] :
      ( v14_lattices(k7_filter_1(A_9,B_11))
      | ~ v14_lattices(B_11)
      | ~ v14_lattices(A_9)
      | ~ l3_lattices(B_11)
      | ~ v10_lattices(B_11)
      | v2_struct_0(B_11)
      | ~ l3_lattices(A_9)
      | ~ v10_lattices(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2,plain,(
    ! [A_1] :
      ( v15_lattices(A_1)
      | ~ v14_lattices(A_1)
      | ~ v13_lattices(A_1)
      | ~ l3_lattices(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_780,plain,(
    ! [A_172,B_173] :
      ( ~ v2_struct_0(k7_filter_1(A_172,B_173))
      | ~ l3_lattices(B_173)
      | v2_struct_0(B_173)
      | ~ l3_lattices(A_172)
      | v2_struct_0(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_818,plain,(
    ! [B_192,A_193] :
      ( ~ l3_lattices(B_192)
      | v2_struct_0(B_192)
      | ~ l3_lattices(A_193)
      | v2_struct_0(A_193)
      | v15_lattices(k7_filter_1(A_193,B_192))
      | ~ v14_lattices(k7_filter_1(A_193,B_192))
      | ~ v13_lattices(k7_filter_1(A_193,B_192))
      | ~ l3_lattices(k7_filter_1(A_193,B_192)) ) ),
    inference(resolution,[status(thm)],[c_2,c_780])).

tff(c_827,plain,
    ( ~ l3_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ v14_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v13_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_818,c_736])).

tff(c_832,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1')
    | ~ v14_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v13_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_827])).

tff(c_833,plain,
    ( ~ v14_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v13_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_832])).

tff(c_834,plain,(
    ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_833])).

tff(c_837,plain,
    ( ~ l3_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_834])).

tff(c_840,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_837])).

tff(c_842,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_840])).

tff(c_843,plain,
    ( ~ v13_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v14_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_833])).

tff(c_845,plain,(
    ~ v14_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_843])).

tff(c_848,plain,
    ( ~ v14_lattices('#skF_2')
    | ~ v14_lattices('#skF_1')
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_845])).

tff(c_851,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_28,c_750,c_747,c_848])).

tff(c_853,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_851])).

tff(c_854,plain,(
    ~ v13_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_843])).

tff(c_858,plain,
    ( ~ v13_lattices('#skF_2')
    | ~ v13_lattices('#skF_1')
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_854])).

tff(c_861,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_28,c_765,c_762,c_858])).

tff(c_863,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_861])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:57:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.48  
% 3.22/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.48  %$ v3_lattices > v2_struct_0 > v15_lattices > v14_lattices > v13_lattices > v10_lattices > l3_lattices > k7_filter_1 > #nlpp > #skF_2 > #skF_1
% 3.22/1.48  
% 3.22/1.48  %Foreground sorts:
% 3.22/1.48  
% 3.22/1.48  
% 3.22/1.48  %Background operators:
% 3.22/1.48  
% 3.22/1.48  
% 3.22/1.48  %Foreground operators:
% 3.22/1.48  tff(l3_lattices, type, l3_lattices: $i > $o).
% 3.22/1.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.22/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.22/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.22/1.48  tff(v10_lattices, type, v10_lattices: $i > $o).
% 3.22/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.48  tff(v14_lattices, type, v14_lattices: $i > $o).
% 3.22/1.48  tff(v13_lattices, type, v13_lattices: $i > $o).
% 3.22/1.48  tff(k7_filter_1, type, k7_filter_1: ($i * $i) > $i).
% 3.22/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.48  tff(v3_lattices, type, v3_lattices: $i > $o).
% 3.22/1.48  tff(v15_lattices, type, v15_lattices: $i > $o).
% 3.22/1.48  
% 3.36/1.51  tff(f_129, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => (![B]: (((~v2_struct_0(B) & v10_lattices(B)) & l3_lattices(B)) => ((v15_lattices(A) & v15_lattices(B)) <=> v15_lattices(k7_filter_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_filter_1)).
% 3.36/1.51  tff(f_36, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v15_lattices(A) <=> (v13_lattices(A) & v14_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d15_lattices)).
% 3.36/1.51  tff(f_50, axiom, (![A, B]: ((((~v2_struct_0(A) & l3_lattices(A)) & ~v2_struct_0(B)) & l3_lattices(B)) => (v3_lattices(k7_filter_1(A, B)) & l3_lattices(k7_filter_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_filter_1)).
% 3.36/1.51  tff(f_65, axiom, (![A, B]: ((((~v2_struct_0(A) & l3_lattices(A)) & ~v2_struct_0(B)) & l3_lattices(B)) => (~v2_struct_0(k7_filter_1(A, B)) & v3_lattices(k7_filter_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_filter_1)).
% 3.36/1.51  tff(f_86, axiom, (![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => (![B]: (((~v2_struct_0(B) & v10_lattices(B)) & l3_lattices(B)) => ((v13_lattices(A) & v13_lattices(B)) <=> v13_lattices(k7_filter_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_filter_1)).
% 3.36/1.51  tff(f_107, axiom, (![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => (![B]: (((~v2_struct_0(B) & v10_lattices(B)) & l3_lattices(B)) => ((v14_lattices(A) & v14_lattices(B)) <=> v14_lattices(k7_filter_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_filter_1)).
% 3.36/1.51  tff(c_38, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.36/1.51  tff(c_32, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.36/1.51  tff(c_36, plain, (v10_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.36/1.51  tff(c_34, plain, (l3_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.36/1.51  tff(c_30, plain, (v10_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.36/1.51  tff(c_28, plain, (l3_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.36/1.51  tff(c_50, plain, (v15_lattices('#skF_1') | v15_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.36/1.51  tff(c_51, plain, (v15_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_50])).
% 3.36/1.51  tff(c_40, plain, (~v15_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v15_lattices('#skF_2') | ~v15_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.36/1.51  tff(c_54, plain, (~v15_lattices('#skF_2') | ~v15_lattices('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_51, c_40])).
% 3.36/1.51  tff(c_55, plain, (~v15_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_54])).
% 3.36/1.51  tff(c_351, plain, (![A_79]: (v15_lattices(A_79) | ~v14_lattices(A_79) | ~v13_lattices(A_79) | ~l3_lattices(A_79) | v2_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.36/1.51  tff(c_357, plain, (v15_lattices('#skF_1') | ~v14_lattices('#skF_1') | ~v13_lattices('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_351, c_38])).
% 3.36/1.51  tff(c_363, plain, (v15_lattices('#skF_1') | ~v14_lattices('#skF_1') | ~v13_lattices('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_357])).
% 3.36/1.51  tff(c_364, plain, (~v14_lattices('#skF_1') | ~v13_lattices('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_55, c_363])).
% 3.36/1.51  tff(c_365, plain, (~v13_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_364])).
% 3.36/1.51  tff(c_8, plain, (![A_2, B_3]: (l3_lattices(k7_filter_1(A_2, B_3)) | ~l3_lattices(B_3) | v2_struct_0(B_3) | ~l3_lattices(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.36/1.51  tff(c_6, plain, (![A_1]: (v13_lattices(A_1) | ~v15_lattices(A_1) | ~l3_lattices(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.36/1.51  tff(c_366, plain, (![A_80, B_81]: (~v2_struct_0(k7_filter_1(A_80, B_81)) | ~l3_lattices(B_81) | v2_struct_0(B_81) | ~l3_lattices(A_80) | v2_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.36/1.51  tff(c_403, plain, (![B_98, A_99]: (~l3_lattices(B_98) | v2_struct_0(B_98) | ~l3_lattices(A_99) | v2_struct_0(A_99) | v13_lattices(k7_filter_1(A_99, B_98)) | ~v15_lattices(k7_filter_1(A_99, B_98)) | ~l3_lattices(k7_filter_1(A_99, B_98)))), inference(resolution, [status(thm)], [c_6, c_366])).
% 3.36/1.51  tff(c_406, plain, (~l3_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1') | v13_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_51, c_403])).
% 3.36/1.51  tff(c_409, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1') | v13_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_406])).
% 3.36/1.51  tff(c_410, plain, (v13_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_409])).
% 3.36/1.51  tff(c_411, plain, (~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_410])).
% 3.36/1.51  tff(c_414, plain, (~l3_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_8, c_411])).
% 3.36/1.51  tff(c_417, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_414])).
% 3.36/1.51  tff(c_419, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_417])).
% 3.36/1.51  tff(c_420, plain, (v13_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_410])).
% 3.36/1.51  tff(c_20, plain, (![A_6, B_8]: (v13_lattices(A_6) | ~v13_lattices(k7_filter_1(A_6, B_8)) | ~l3_lattices(B_8) | ~v10_lattices(B_8) | v2_struct_0(B_8) | ~l3_lattices(A_6) | ~v10_lattices(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.36/1.51  tff(c_424, plain, (v13_lattices('#skF_1') | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_420, c_20])).
% 3.36/1.51  tff(c_430, plain, (v13_lattices('#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_28, c_424])).
% 3.36/1.51  tff(c_432, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_365, c_430])).
% 3.36/1.51  tff(c_433, plain, (~v14_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_364])).
% 3.36/1.51  tff(c_4, plain, (![A_1]: (v14_lattices(A_1) | ~v15_lattices(A_1) | ~l3_lattices(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.36/1.51  tff(c_435, plain, (![A_100, B_101]: (~v2_struct_0(k7_filter_1(A_100, B_101)) | ~l3_lattices(B_101) | v2_struct_0(B_101) | ~l3_lattices(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.36/1.51  tff(c_472, plain, (![B_118, A_119]: (~l3_lattices(B_118) | v2_struct_0(B_118) | ~l3_lattices(A_119) | v2_struct_0(A_119) | v14_lattices(k7_filter_1(A_119, B_118)) | ~v15_lattices(k7_filter_1(A_119, B_118)) | ~l3_lattices(k7_filter_1(A_119, B_118)))), inference(resolution, [status(thm)], [c_4, c_435])).
% 3.36/1.51  tff(c_475, plain, (~l3_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1') | v14_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_51, c_472])).
% 3.36/1.51  tff(c_478, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1') | v14_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_475])).
% 3.36/1.51  tff(c_479, plain, (v14_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_478])).
% 3.36/1.51  tff(c_488, plain, (~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_479])).
% 3.36/1.51  tff(c_491, plain, (~l3_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_8, c_488])).
% 3.36/1.51  tff(c_494, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_491])).
% 3.36/1.51  tff(c_496, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_494])).
% 3.36/1.51  tff(c_497, plain, (v14_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_479])).
% 3.36/1.51  tff(c_26, plain, (![A_9, B_11]: (v14_lattices(A_9) | ~v14_lattices(k7_filter_1(A_9, B_11)) | ~l3_lattices(B_11) | ~v10_lattices(B_11) | v2_struct_0(B_11) | ~l3_lattices(A_9) | ~v10_lattices(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.36/1.51  tff(c_517, plain, (v14_lattices('#skF_1') | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_497, c_26])).
% 3.36/1.51  tff(c_523, plain, (v14_lattices('#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_28, c_517])).
% 3.36/1.51  tff(c_525, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_433, c_523])).
% 3.36/1.51  tff(c_526, plain, (~v15_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_54])).
% 3.36/1.51  tff(c_554, plain, (![A_124]: (v15_lattices(A_124) | ~v14_lattices(A_124) | ~v13_lattices(A_124) | ~l3_lattices(A_124) | v2_struct_0(A_124))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.36/1.51  tff(c_557, plain, (v15_lattices('#skF_2') | ~v14_lattices('#skF_2') | ~v13_lattices('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_554, c_32])).
% 3.36/1.51  tff(c_563, plain, (v15_lattices('#skF_2') | ~v14_lattices('#skF_2') | ~v13_lattices('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_557])).
% 3.36/1.51  tff(c_564, plain, (~v14_lattices('#skF_2') | ~v13_lattices('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_526, c_563])).
% 3.36/1.51  tff(c_568, plain, (~v13_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_564])).
% 3.36/1.51  tff(c_571, plain, (![A_129, B_130]: (~v2_struct_0(k7_filter_1(A_129, B_130)) | ~l3_lattices(B_130) | v2_struct_0(B_130) | ~l3_lattices(A_129) | v2_struct_0(A_129))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.36/1.51  tff(c_606, plain, (![B_143, A_144]: (~l3_lattices(B_143) | v2_struct_0(B_143) | ~l3_lattices(A_144) | v2_struct_0(A_144) | v14_lattices(k7_filter_1(A_144, B_143)) | ~v15_lattices(k7_filter_1(A_144, B_143)) | ~l3_lattices(k7_filter_1(A_144, B_143)))), inference(resolution, [status(thm)], [c_4, c_571])).
% 3.36/1.51  tff(c_609, plain, (~l3_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1') | v14_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_51, c_606])).
% 3.36/1.51  tff(c_612, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1') | v14_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_609])).
% 3.36/1.51  tff(c_613, plain, (v14_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_612])).
% 3.36/1.51  tff(c_614, plain, (~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_613])).
% 3.36/1.51  tff(c_617, plain, (~l3_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_8, c_614])).
% 3.36/1.51  tff(c_620, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_617])).
% 3.36/1.51  tff(c_622, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_620])).
% 3.36/1.51  tff(c_624, plain, (l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_613])).
% 3.36/1.51  tff(c_639, plain, (![B_145, A_146]: (~l3_lattices(B_145) | v2_struct_0(B_145) | ~l3_lattices(A_146) | v2_struct_0(A_146) | v13_lattices(k7_filter_1(A_146, B_145)) | ~v15_lattices(k7_filter_1(A_146, B_145)) | ~l3_lattices(k7_filter_1(A_146, B_145)))), inference(resolution, [status(thm)], [c_6, c_571])).
% 3.36/1.51  tff(c_642, plain, (~l3_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1') | v13_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_51, c_639])).
% 3.36/1.51  tff(c_645, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1') | v13_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_624, c_34, c_28, c_642])).
% 3.36/1.51  tff(c_646, plain, (v13_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_645])).
% 3.36/1.51  tff(c_18, plain, (![B_8, A_6]: (v13_lattices(B_8) | ~v13_lattices(k7_filter_1(A_6, B_8)) | ~l3_lattices(B_8) | ~v10_lattices(B_8) | v2_struct_0(B_8) | ~l3_lattices(A_6) | ~v10_lattices(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.36/1.51  tff(c_652, plain, (v13_lattices('#skF_2') | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_646, c_18])).
% 3.36/1.51  tff(c_659, plain, (v13_lattices('#skF_2') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_28, c_652])).
% 3.36/1.51  tff(c_661, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_568, c_659])).
% 3.36/1.51  tff(c_662, plain, (~v14_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_564])).
% 3.36/1.51  tff(c_664, plain, (![A_147, B_148]: (~v2_struct_0(k7_filter_1(A_147, B_148)) | ~l3_lattices(B_148) | v2_struct_0(B_148) | ~l3_lattices(A_147) | v2_struct_0(A_147))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.36/1.51  tff(c_701, plain, (![B_165, A_166]: (~l3_lattices(B_165) | v2_struct_0(B_165) | ~l3_lattices(A_166) | v2_struct_0(A_166) | v14_lattices(k7_filter_1(A_166, B_165)) | ~v15_lattices(k7_filter_1(A_166, B_165)) | ~l3_lattices(k7_filter_1(A_166, B_165)))), inference(resolution, [status(thm)], [c_4, c_664])).
% 3.36/1.51  tff(c_704, plain, (~l3_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1') | v14_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_51, c_701])).
% 3.36/1.51  tff(c_707, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1') | v14_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_704])).
% 3.36/1.51  tff(c_708, plain, (v14_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_707])).
% 3.36/1.51  tff(c_709, plain, (~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_708])).
% 3.36/1.51  tff(c_712, plain, (~l3_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_8, c_709])).
% 3.36/1.51  tff(c_715, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_712])).
% 3.36/1.51  tff(c_717, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_715])).
% 3.36/1.51  tff(c_718, plain, (v14_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_708])).
% 3.36/1.51  tff(c_24, plain, (![B_11, A_9]: (v14_lattices(B_11) | ~v14_lattices(k7_filter_1(A_9, B_11)) | ~l3_lattices(B_11) | ~v10_lattices(B_11) | v2_struct_0(B_11) | ~l3_lattices(A_9) | ~v10_lattices(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.36/1.51  tff(c_725, plain, (v14_lattices('#skF_2') | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_718, c_24])).
% 3.36/1.51  tff(c_732, plain, (v14_lattices('#skF_2') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_28, c_725])).
% 3.36/1.51  tff(c_734, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_662, c_732])).
% 3.36/1.51  tff(c_735, plain, (v15_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_50])).
% 3.36/1.51  tff(c_753, plain, (![A_168]: (v13_lattices(A_168) | ~v15_lattices(A_168) | ~l3_lattices(A_168) | v2_struct_0(A_168))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.36/1.51  tff(c_759, plain, (v13_lattices('#skF_1') | ~v15_lattices('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_753, c_38])).
% 3.36/1.51  tff(c_765, plain, (v13_lattices('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_735, c_759])).
% 3.36/1.51  tff(c_736, plain, (~v15_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_50])).
% 3.36/1.51  tff(c_48, plain, (v15_lattices('#skF_2') | v15_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.36/1.51  tff(c_737, plain, (v15_lattices('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_736, c_48])).
% 3.36/1.51  tff(c_756, plain, (v13_lattices('#skF_2') | ~v15_lattices('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_753, c_32])).
% 3.36/1.51  tff(c_762, plain, (v13_lattices('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_737, c_756])).
% 3.36/1.51  tff(c_16, plain, (![A_6, B_8]: (v13_lattices(k7_filter_1(A_6, B_8)) | ~v13_lattices(B_8) | ~v13_lattices(A_6) | ~l3_lattices(B_8) | ~v10_lattices(B_8) | v2_struct_0(B_8) | ~l3_lattices(A_6) | ~v10_lattices(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.36/1.51  tff(c_738, plain, (![A_167]: (v14_lattices(A_167) | ~v15_lattices(A_167) | ~l3_lattices(A_167) | v2_struct_0(A_167))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.36/1.51  tff(c_744, plain, (v14_lattices('#skF_1') | ~v15_lattices('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_738, c_38])).
% 3.36/1.51  tff(c_750, plain, (v14_lattices('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_735, c_744])).
% 3.36/1.51  tff(c_741, plain, (v14_lattices('#skF_2') | ~v15_lattices('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_738, c_32])).
% 3.36/1.51  tff(c_747, plain, (v14_lattices('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_737, c_741])).
% 3.36/1.51  tff(c_22, plain, (![A_9, B_11]: (v14_lattices(k7_filter_1(A_9, B_11)) | ~v14_lattices(B_11) | ~v14_lattices(A_9) | ~l3_lattices(B_11) | ~v10_lattices(B_11) | v2_struct_0(B_11) | ~l3_lattices(A_9) | ~v10_lattices(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.36/1.51  tff(c_2, plain, (![A_1]: (v15_lattices(A_1) | ~v14_lattices(A_1) | ~v13_lattices(A_1) | ~l3_lattices(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.36/1.51  tff(c_780, plain, (![A_172, B_173]: (~v2_struct_0(k7_filter_1(A_172, B_173)) | ~l3_lattices(B_173) | v2_struct_0(B_173) | ~l3_lattices(A_172) | v2_struct_0(A_172))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.36/1.51  tff(c_818, plain, (![B_192, A_193]: (~l3_lattices(B_192) | v2_struct_0(B_192) | ~l3_lattices(A_193) | v2_struct_0(A_193) | v15_lattices(k7_filter_1(A_193, B_192)) | ~v14_lattices(k7_filter_1(A_193, B_192)) | ~v13_lattices(k7_filter_1(A_193, B_192)) | ~l3_lattices(k7_filter_1(A_193, B_192)))), inference(resolution, [status(thm)], [c_2, c_780])).
% 3.36/1.51  tff(c_827, plain, (~l3_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1') | ~v14_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v13_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_818, c_736])).
% 3.36/1.51  tff(c_832, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1') | ~v14_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v13_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_827])).
% 3.36/1.51  tff(c_833, plain, (~v14_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v13_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_832])).
% 3.36/1.51  tff(c_834, plain, (~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_833])).
% 3.36/1.51  tff(c_837, plain, (~l3_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_8, c_834])).
% 3.36/1.51  tff(c_840, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_837])).
% 3.36/1.51  tff(c_842, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_840])).
% 3.36/1.51  tff(c_843, plain, (~v13_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v14_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_833])).
% 3.36/1.51  tff(c_845, plain, (~v14_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_843])).
% 3.36/1.51  tff(c_848, plain, (~v14_lattices('#skF_2') | ~v14_lattices('#skF_1') | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_845])).
% 3.36/1.51  tff(c_851, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_28, c_750, c_747, c_848])).
% 3.36/1.51  tff(c_853, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_851])).
% 3.36/1.51  tff(c_854, plain, (~v13_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_843])).
% 3.36/1.51  tff(c_858, plain, (~v13_lattices('#skF_2') | ~v13_lattices('#skF_1') | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_854])).
% 3.36/1.51  tff(c_861, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_28, c_765, c_762, c_858])).
% 3.36/1.51  tff(c_863, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_861])).
% 3.36/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.51  
% 3.36/1.51  Inference rules
% 3.36/1.51  ----------------------
% 3.36/1.51  #Ref     : 0
% 3.36/1.51  #Sup     : 121
% 3.36/1.51  #Fact    : 0
% 3.36/1.51  #Define  : 0
% 3.36/1.51  #Split   : 17
% 3.36/1.51  #Chain   : 0
% 3.36/1.51  #Close   : 0
% 3.36/1.51  
% 3.36/1.51  Ordering : KBO
% 3.36/1.51  
% 3.36/1.51  Simplification rules
% 3.36/1.51  ----------------------
% 3.36/1.51  #Subsume      : 8
% 3.36/1.51  #Demod        : 171
% 3.36/1.51  #Tautology    : 48
% 3.36/1.51  #SimpNegUnit  : 43
% 3.36/1.51  #BackRed      : 0
% 3.36/1.51  
% 3.36/1.51  #Partial instantiations: 0
% 3.36/1.51  #Strategies tried      : 1
% 3.36/1.51  
% 3.36/1.51  Timing (in seconds)
% 3.36/1.51  ----------------------
% 3.36/1.51  Preprocessing        : 0.30
% 3.36/1.51  Parsing              : 0.17
% 3.36/1.51  CNF conversion       : 0.02
% 3.36/1.51  Main loop            : 0.41
% 3.36/1.51  Inferencing          : 0.18
% 3.36/1.51  Reduction            : 0.10
% 3.36/1.51  Demodulation         : 0.07
% 3.36/1.51  BG Simplification    : 0.02
% 3.36/1.51  Subsumption          : 0.09
% 3.36/1.51  Abstraction          : 0.01
% 3.36/1.51  MUC search           : 0.00
% 3.36/1.51  Cooper               : 0.00
% 3.36/1.51  Total                : 0.77
% 3.36/1.51  Index Insertion      : 0.00
% 3.36/1.51  Index Deletion       : 0.00
% 3.36/1.51  Index Matching       : 0.00
% 3.36/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
