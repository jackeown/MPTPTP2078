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

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 539 expanded)
%              Number of leaves         :   20 ( 202 expanded)
%              Depth                    :   11
%              Number of atoms          :  451 (2432 expanded)
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

tff(f_146,negated_conjecture,(
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

tff(f_39,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( ( ~ v2_struct_0(A)
          & v13_lattices(A)
          & v14_lattices(A) )
       => ( ~ v2_struct_0(A)
          & v15_lattices(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_lattices)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A)
        & ~ v2_struct_0(B)
        & l3_lattices(B) )
     => ( v3_lattices(k7_filter_1(A,B))
        & l3_lattices(k7_filter_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_filter_1)).

tff(f_53,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( ( ~ v2_struct_0(A)
          & v15_lattices(A) )
       => ( ~ v2_struct_0(A)
          & v13_lattices(A)
          & v14_lattices(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_lattices)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A)
        & ~ v2_struct_0(B)
        & l3_lattices(B) )
     => ( ~ v2_struct_0(k7_filter_1(A,B))
        & v3_lattices(k7_filter_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_filter_1)).

tff(f_103,axiom,(
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

tff(f_124,axiom,(
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

tff(c_42,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_40,plain,(
    v10_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_38,plain,(
    l3_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_34,plain,(
    v10_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_32,plain,(
    l3_lattices('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_54,plain,
    ( v15_lattices('#skF_1')
    | v15_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_55,plain,(
    v15_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_44,plain,
    ( ~ v15_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v15_lattices('#skF_2')
    | ~ v15_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_58,plain,
    ( ~ v15_lattices('#skF_2')
    | ~ v15_lattices('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_44])).

tff(c_59,plain,(
    ~ v15_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_355,plain,(
    ! [A_80] :
      ( v15_lattices(A_80)
      | ~ v14_lattices(A_80)
      | ~ v13_lattices(A_80)
      | v2_struct_0(A_80)
      | ~ l3_lattices(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_361,plain,
    ( v15_lattices('#skF_1')
    | ~ v14_lattices('#skF_1')
    | ~ v13_lattices('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_355,c_42])).

tff(c_367,plain,
    ( v15_lattices('#skF_1')
    | ~ v14_lattices('#skF_1')
    | ~ v13_lattices('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_361])).

tff(c_368,plain,
    ( ~ v14_lattices('#skF_1')
    | ~ v13_lattices('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_367])).

tff(c_369,plain,(
    ~ v13_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_368])).

tff(c_12,plain,(
    ! [A_3,B_4] :
      ( l3_lattices(k7_filter_1(A_3,B_4))
      | ~ l3_lattices(B_4)
      | v2_struct_0(B_4)
      | ~ l3_lattices(A_3)
      | v2_struct_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8,plain,(
    ! [A_2] :
      ( v13_lattices(A_2)
      | ~ v15_lattices(A_2)
      | v2_struct_0(A_2)
      | ~ l3_lattices(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_370,plain,(
    ! [A_81,B_82] :
      ( ~ v2_struct_0(k7_filter_1(A_81,B_82))
      | ~ l3_lattices(B_82)
      | v2_struct_0(B_82)
      | ~ l3_lattices(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_407,plain,(
    ! [B_99,A_100] :
      ( ~ l3_lattices(B_99)
      | v2_struct_0(B_99)
      | ~ l3_lattices(A_100)
      | v2_struct_0(A_100)
      | v13_lattices(k7_filter_1(A_100,B_99))
      | ~ v15_lattices(k7_filter_1(A_100,B_99))
      | ~ l3_lattices(k7_filter_1(A_100,B_99)) ) ),
    inference(resolution,[status(thm)],[c_8,c_370])).

tff(c_410,plain,
    ( ~ l3_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | v13_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_55,c_407])).

tff(c_413,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1')
    | v13_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_410])).

tff(c_414,plain,
    ( v13_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_36,c_413])).

tff(c_415,plain,(
    ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_414])).

tff(c_418,plain,
    ( ~ l3_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_415])).

tff(c_421,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_418])).

tff(c_423,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_36,c_421])).

tff(c_424,plain,(
    v13_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_414])).

tff(c_24,plain,(
    ! [A_7,B_9] :
      ( v13_lattices(A_7)
      | ~ v13_lattices(k7_filter_1(A_7,B_9))
      | ~ l3_lattices(B_9)
      | ~ v10_lattices(B_9)
      | v2_struct_0(B_9)
      | ~ l3_lattices(A_7)
      | ~ v10_lattices(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_428,plain,
    ( v13_lattices('#skF_1')
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_424,c_24])).

tff(c_434,plain,
    ( v13_lattices('#skF_1')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_34,c_32,c_428])).

tff(c_436,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_36,c_369,c_434])).

tff(c_437,plain,(
    ~ v14_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_368])).

tff(c_6,plain,(
    ! [A_2] :
      ( v14_lattices(A_2)
      | ~ v15_lattices(A_2)
      | v2_struct_0(A_2)
      | ~ l3_lattices(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_439,plain,(
    ! [A_101,B_102] :
      ( ~ v2_struct_0(k7_filter_1(A_101,B_102))
      | ~ l3_lattices(B_102)
      | v2_struct_0(B_102)
      | ~ l3_lattices(A_101)
      | v2_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_476,plain,(
    ! [B_119,A_120] :
      ( ~ l3_lattices(B_119)
      | v2_struct_0(B_119)
      | ~ l3_lattices(A_120)
      | v2_struct_0(A_120)
      | v14_lattices(k7_filter_1(A_120,B_119))
      | ~ v15_lattices(k7_filter_1(A_120,B_119))
      | ~ l3_lattices(k7_filter_1(A_120,B_119)) ) ),
    inference(resolution,[status(thm)],[c_6,c_439])).

tff(c_479,plain,
    ( ~ l3_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | v14_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_55,c_476])).

tff(c_482,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1')
    | v14_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_479])).

tff(c_483,plain,
    ( v14_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_36,c_482])).

tff(c_492,plain,(
    ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_483])).

tff(c_495,plain,
    ( ~ l3_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_492])).

tff(c_498,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_495])).

tff(c_500,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_36,c_498])).

tff(c_501,plain,(
    v14_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_483])).

tff(c_30,plain,(
    ! [A_10,B_12] :
      ( v14_lattices(A_10)
      | ~ v14_lattices(k7_filter_1(A_10,B_12))
      | ~ l3_lattices(B_12)
      | ~ v10_lattices(B_12)
      | v2_struct_0(B_12)
      | ~ l3_lattices(A_10)
      | ~ v10_lattices(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_521,plain,
    ( v14_lattices('#skF_1')
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_501,c_30])).

tff(c_527,plain,
    ( v14_lattices('#skF_1')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_34,c_32,c_521])).

tff(c_529,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_36,c_437,c_527])).

tff(c_530,plain,(
    ~ v15_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_558,plain,(
    ! [A_125] :
      ( v15_lattices(A_125)
      | ~ v14_lattices(A_125)
      | ~ v13_lattices(A_125)
      | v2_struct_0(A_125)
      | ~ l3_lattices(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_561,plain,
    ( v15_lattices('#skF_2')
    | ~ v14_lattices('#skF_2')
    | ~ v13_lattices('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_558,c_36])).

tff(c_567,plain,
    ( v15_lattices('#skF_2')
    | ~ v14_lattices('#skF_2')
    | ~ v13_lattices('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_561])).

tff(c_568,plain,
    ( ~ v14_lattices('#skF_2')
    | ~ v13_lattices('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_530,c_567])).

tff(c_572,plain,(
    ~ v13_lattices('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_568])).

tff(c_575,plain,(
    ! [A_130,B_131] :
      ( ~ v2_struct_0(k7_filter_1(A_130,B_131))
      | ~ l3_lattices(B_131)
      | v2_struct_0(B_131)
      | ~ l3_lattices(A_130)
      | v2_struct_0(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_610,plain,(
    ! [B_144,A_145] :
      ( ~ l3_lattices(B_144)
      | v2_struct_0(B_144)
      | ~ l3_lattices(A_145)
      | v2_struct_0(A_145)
      | v14_lattices(k7_filter_1(A_145,B_144))
      | ~ v15_lattices(k7_filter_1(A_145,B_144))
      | ~ l3_lattices(k7_filter_1(A_145,B_144)) ) ),
    inference(resolution,[status(thm)],[c_6,c_575])).

tff(c_613,plain,
    ( ~ l3_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | v14_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_55,c_610])).

tff(c_616,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1')
    | v14_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_613])).

tff(c_617,plain,
    ( v14_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_36,c_616])).

tff(c_618,plain,(
    ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_617])).

tff(c_621,plain,
    ( ~ l3_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_618])).

tff(c_624,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_621])).

tff(c_626,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_36,c_624])).

tff(c_628,plain,(
    l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_617])).

tff(c_643,plain,(
    ! [B_146,A_147] :
      ( ~ l3_lattices(B_146)
      | v2_struct_0(B_146)
      | ~ l3_lattices(A_147)
      | v2_struct_0(A_147)
      | v13_lattices(k7_filter_1(A_147,B_146))
      | ~ v15_lattices(k7_filter_1(A_147,B_146))
      | ~ l3_lattices(k7_filter_1(A_147,B_146)) ) ),
    inference(resolution,[status(thm)],[c_8,c_575])).

tff(c_646,plain,
    ( ~ l3_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | v13_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_55,c_643])).

tff(c_649,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1')
    | v13_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_628,c_38,c_32,c_646])).

tff(c_650,plain,(
    v13_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_36,c_649])).

tff(c_22,plain,(
    ! [B_9,A_7] :
      ( v13_lattices(B_9)
      | ~ v13_lattices(k7_filter_1(A_7,B_9))
      | ~ l3_lattices(B_9)
      | ~ v10_lattices(B_9)
      | v2_struct_0(B_9)
      | ~ l3_lattices(A_7)
      | ~ v10_lattices(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_656,plain,
    ( v13_lattices('#skF_2')
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_650,c_22])).

tff(c_663,plain,
    ( v13_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_34,c_32,c_656])).

tff(c_665,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_36,c_572,c_663])).

tff(c_666,plain,(
    ~ v14_lattices('#skF_2') ),
    inference(splitRight,[status(thm)],[c_568])).

tff(c_668,plain,(
    ! [A_148,B_149] :
      ( ~ v2_struct_0(k7_filter_1(A_148,B_149))
      | ~ l3_lattices(B_149)
      | v2_struct_0(B_149)
      | ~ l3_lattices(A_148)
      | v2_struct_0(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_705,plain,(
    ! [B_166,A_167] :
      ( ~ l3_lattices(B_166)
      | v2_struct_0(B_166)
      | ~ l3_lattices(A_167)
      | v2_struct_0(A_167)
      | v14_lattices(k7_filter_1(A_167,B_166))
      | ~ v15_lattices(k7_filter_1(A_167,B_166))
      | ~ l3_lattices(k7_filter_1(A_167,B_166)) ) ),
    inference(resolution,[status(thm)],[c_6,c_668])).

tff(c_708,plain,
    ( ~ l3_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | v14_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_55,c_705])).

tff(c_711,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1')
    | v14_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_708])).

tff(c_712,plain,
    ( v14_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_36,c_711])).

tff(c_713,plain,(
    ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_712])).

tff(c_716,plain,
    ( ~ l3_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_713])).

tff(c_719,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_716])).

tff(c_721,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_36,c_719])).

tff(c_722,plain,(
    v14_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_712])).

tff(c_28,plain,(
    ! [B_12,A_10] :
      ( v14_lattices(B_12)
      | ~ v14_lattices(k7_filter_1(A_10,B_12))
      | ~ l3_lattices(B_12)
      | ~ v10_lattices(B_12)
      | v2_struct_0(B_12)
      | ~ l3_lattices(A_10)
      | ~ v10_lattices(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_729,plain,
    ( v14_lattices('#skF_2')
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_722,c_28])).

tff(c_736,plain,
    ( v14_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_34,c_32,c_729])).

tff(c_738,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_36,c_666,c_736])).

tff(c_739,plain,(
    v15_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_757,plain,(
    ! [A_169] :
      ( v13_lattices(A_169)
      | ~ v15_lattices(A_169)
      | v2_struct_0(A_169)
      | ~ l3_lattices(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_763,plain,
    ( v13_lattices('#skF_1')
    | ~ v15_lattices('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_757,c_42])).

tff(c_769,plain,(
    v13_lattices('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_739,c_763])).

tff(c_740,plain,(
    ~ v15_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,
    ( v15_lattices('#skF_2')
    | v15_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_741,plain,(
    v15_lattices('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_740,c_52])).

tff(c_760,plain,
    ( v13_lattices('#skF_2')
    | ~ v15_lattices('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_757,c_36])).

tff(c_766,plain,(
    v13_lattices('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_741,c_760])).

tff(c_20,plain,(
    ! [A_7,B_9] :
      ( v13_lattices(k7_filter_1(A_7,B_9))
      | ~ v13_lattices(B_9)
      | ~ v13_lattices(A_7)
      | ~ l3_lattices(B_9)
      | ~ v10_lattices(B_9)
      | v2_struct_0(B_9)
      | ~ l3_lattices(A_7)
      | ~ v10_lattices(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_742,plain,(
    ! [A_168] :
      ( v14_lattices(A_168)
      | ~ v15_lattices(A_168)
      | v2_struct_0(A_168)
      | ~ l3_lattices(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_748,plain,
    ( v14_lattices('#skF_1')
    | ~ v15_lattices('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_742,c_42])).

tff(c_754,plain,(
    v14_lattices('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_739,c_748])).

tff(c_745,plain,
    ( v14_lattices('#skF_2')
    | ~ v15_lattices('#skF_2')
    | ~ l3_lattices('#skF_2') ),
    inference(resolution,[status(thm)],[c_742,c_36])).

tff(c_751,plain,(
    v14_lattices('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_741,c_745])).

tff(c_26,plain,(
    ! [A_10,B_12] :
      ( v14_lattices(k7_filter_1(A_10,B_12))
      | ~ v14_lattices(B_12)
      | ~ v14_lattices(A_10)
      | ~ l3_lattices(B_12)
      | ~ v10_lattices(B_12)
      | v2_struct_0(B_12)
      | ~ l3_lattices(A_10)
      | ~ v10_lattices(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2,plain,(
    ! [A_1] :
      ( v15_lattices(A_1)
      | ~ v14_lattices(A_1)
      | ~ v13_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_784,plain,(
    ! [A_173,B_174] :
      ( ~ v2_struct_0(k7_filter_1(A_173,B_174))
      | ~ l3_lattices(B_174)
      | v2_struct_0(B_174)
      | ~ l3_lattices(A_173)
      | v2_struct_0(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_822,plain,(
    ! [B_193,A_194] :
      ( ~ l3_lattices(B_193)
      | v2_struct_0(B_193)
      | ~ l3_lattices(A_194)
      | v2_struct_0(A_194)
      | v15_lattices(k7_filter_1(A_194,B_193))
      | ~ v14_lattices(k7_filter_1(A_194,B_193))
      | ~ v13_lattices(k7_filter_1(A_194,B_193))
      | ~ l3_lattices(k7_filter_1(A_194,B_193)) ) ),
    inference(resolution,[status(thm)],[c_2,c_784])).

tff(c_831,plain,
    ( ~ l3_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ v14_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v13_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_822,c_740])).

tff(c_836,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1')
    | ~ v14_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v13_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_831])).

tff(c_837,plain,
    ( ~ v14_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v13_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_36,c_836])).

tff(c_838,plain,(
    ~ l3_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_837])).

tff(c_841,plain,
    ( ~ l3_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_838])).

tff(c_844,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_841])).

tff(c_846,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_36,c_844])).

tff(c_847,plain,
    ( ~ v13_lattices(k7_filter_1('#skF_1','#skF_2'))
    | ~ v14_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_837])).

tff(c_849,plain,(
    ~ v14_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_847])).

tff(c_852,plain,
    ( ~ v14_lattices('#skF_2')
    | ~ v14_lattices('#skF_1')
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_849])).

tff(c_855,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_34,c_32,c_754,c_751,c_852])).

tff(c_857,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_36,c_855])).

tff(c_858,plain,(
    ~ v13_lattices(k7_filter_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_847])).

tff(c_862,plain,
    ( ~ v13_lattices('#skF_2')
    | ~ v13_lattices('#skF_1')
    | ~ l3_lattices('#skF_2')
    | ~ v10_lattices('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l3_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_858])).

tff(c_865,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_34,c_32,c_769,c_766,c_862])).

tff(c_867,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_36,c_865])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:58:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.46/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.62  
% 3.46/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.62  %$ v3_lattices > v2_struct_0 > v15_lattices > v14_lattices > v13_lattices > v10_lattices > l3_lattices > k7_filter_1 > #nlpp > #skF_2 > #skF_1
% 3.46/1.62  
% 3.46/1.62  %Foreground sorts:
% 3.46/1.62  
% 3.46/1.62  
% 3.46/1.62  %Background operators:
% 3.46/1.62  
% 3.46/1.62  
% 3.46/1.62  %Foreground operators:
% 3.46/1.62  tff(l3_lattices, type, l3_lattices: $i > $o).
% 3.46/1.62  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.46/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.46/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.46/1.62  tff('#skF_1', type, '#skF_1': $i).
% 3.46/1.62  tff(v10_lattices, type, v10_lattices: $i > $o).
% 3.46/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.46/1.62  tff(v14_lattices, type, v14_lattices: $i > $o).
% 3.46/1.62  tff(v13_lattices, type, v13_lattices: $i > $o).
% 3.46/1.62  tff(k7_filter_1, type, k7_filter_1: ($i * $i) > $i).
% 3.46/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.46/1.62  tff(v3_lattices, type, v3_lattices: $i > $o).
% 3.46/1.62  tff(v15_lattices, type, v15_lattices: $i > $o).
% 3.46/1.62  
% 3.46/1.65  tff(f_146, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => (![B]: (((~v2_struct_0(B) & v10_lattices(B)) & l3_lattices(B)) => ((v15_lattices(A) & v15_lattices(B)) <=> v15_lattices(k7_filter_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_filter_1)).
% 3.46/1.65  tff(f_39, axiom, (![A]: (l3_lattices(A) => (((~v2_struct_0(A) & v13_lattices(A)) & v14_lattices(A)) => (~v2_struct_0(A) & v15_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_lattices)).
% 3.46/1.65  tff(f_67, axiom, (![A, B]: ((((~v2_struct_0(A) & l3_lattices(A)) & ~v2_struct_0(B)) & l3_lattices(B)) => (v3_lattices(k7_filter_1(A, B)) & l3_lattices(k7_filter_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_filter_1)).
% 3.46/1.65  tff(f_53, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v15_lattices(A)) => ((~v2_struct_0(A) & v13_lattices(A)) & v14_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_lattices)).
% 3.46/1.65  tff(f_82, axiom, (![A, B]: ((((~v2_struct_0(A) & l3_lattices(A)) & ~v2_struct_0(B)) & l3_lattices(B)) => (~v2_struct_0(k7_filter_1(A, B)) & v3_lattices(k7_filter_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_filter_1)).
% 3.46/1.65  tff(f_103, axiom, (![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => (![B]: (((~v2_struct_0(B) & v10_lattices(B)) & l3_lattices(B)) => ((v13_lattices(A) & v13_lattices(B)) <=> v13_lattices(k7_filter_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_filter_1)).
% 3.46/1.65  tff(f_124, axiom, (![A]: (((~v2_struct_0(A) & v10_lattices(A)) & l3_lattices(A)) => (![B]: (((~v2_struct_0(B) & v10_lattices(B)) & l3_lattices(B)) => ((v14_lattices(A) & v14_lattices(B)) <=> v14_lattices(k7_filter_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_filter_1)).
% 3.46/1.65  tff(c_42, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.46/1.65  tff(c_36, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.46/1.65  tff(c_40, plain, (v10_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.46/1.65  tff(c_38, plain, (l3_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.46/1.65  tff(c_34, plain, (v10_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.46/1.65  tff(c_32, plain, (l3_lattices('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.46/1.65  tff(c_54, plain, (v15_lattices('#skF_1') | v15_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.46/1.65  tff(c_55, plain, (v15_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_54])).
% 3.46/1.65  tff(c_44, plain, (~v15_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v15_lattices('#skF_2') | ~v15_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.46/1.65  tff(c_58, plain, (~v15_lattices('#skF_2') | ~v15_lattices('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_44])).
% 3.46/1.65  tff(c_59, plain, (~v15_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_58])).
% 3.46/1.65  tff(c_355, plain, (![A_80]: (v15_lattices(A_80) | ~v14_lattices(A_80) | ~v13_lattices(A_80) | v2_struct_0(A_80) | ~l3_lattices(A_80))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.46/1.65  tff(c_361, plain, (v15_lattices('#skF_1') | ~v14_lattices('#skF_1') | ~v13_lattices('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_355, c_42])).
% 3.46/1.65  tff(c_367, plain, (v15_lattices('#skF_1') | ~v14_lattices('#skF_1') | ~v13_lattices('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_361])).
% 3.46/1.65  tff(c_368, plain, (~v14_lattices('#skF_1') | ~v13_lattices('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_59, c_367])).
% 3.46/1.65  tff(c_369, plain, (~v13_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_368])).
% 3.46/1.65  tff(c_12, plain, (![A_3, B_4]: (l3_lattices(k7_filter_1(A_3, B_4)) | ~l3_lattices(B_4) | v2_struct_0(B_4) | ~l3_lattices(A_3) | v2_struct_0(A_3))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.46/1.65  tff(c_8, plain, (![A_2]: (v13_lattices(A_2) | ~v15_lattices(A_2) | v2_struct_0(A_2) | ~l3_lattices(A_2))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.46/1.65  tff(c_370, plain, (![A_81, B_82]: (~v2_struct_0(k7_filter_1(A_81, B_82)) | ~l3_lattices(B_82) | v2_struct_0(B_82) | ~l3_lattices(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.46/1.65  tff(c_407, plain, (![B_99, A_100]: (~l3_lattices(B_99) | v2_struct_0(B_99) | ~l3_lattices(A_100) | v2_struct_0(A_100) | v13_lattices(k7_filter_1(A_100, B_99)) | ~v15_lattices(k7_filter_1(A_100, B_99)) | ~l3_lattices(k7_filter_1(A_100, B_99)))), inference(resolution, [status(thm)], [c_8, c_370])).
% 3.46/1.65  tff(c_410, plain, (~l3_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1') | v13_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_55, c_407])).
% 3.46/1.65  tff(c_413, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1') | v13_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_410])).
% 3.46/1.65  tff(c_414, plain, (v13_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_42, c_36, c_413])).
% 3.46/1.65  tff(c_415, plain, (~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_414])).
% 3.46/1.65  tff(c_418, plain, (~l3_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_12, c_415])).
% 3.46/1.65  tff(c_421, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_418])).
% 3.46/1.65  tff(c_423, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_36, c_421])).
% 3.46/1.65  tff(c_424, plain, (v13_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_414])).
% 3.46/1.65  tff(c_24, plain, (![A_7, B_9]: (v13_lattices(A_7) | ~v13_lattices(k7_filter_1(A_7, B_9)) | ~l3_lattices(B_9) | ~v10_lattices(B_9) | v2_struct_0(B_9) | ~l3_lattices(A_7) | ~v10_lattices(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.46/1.65  tff(c_428, plain, (v13_lattices('#skF_1') | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_424, c_24])).
% 3.46/1.65  tff(c_434, plain, (v13_lattices('#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_34, c_32, c_428])).
% 3.46/1.65  tff(c_436, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_36, c_369, c_434])).
% 3.46/1.65  tff(c_437, plain, (~v14_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_368])).
% 3.46/1.65  tff(c_6, plain, (![A_2]: (v14_lattices(A_2) | ~v15_lattices(A_2) | v2_struct_0(A_2) | ~l3_lattices(A_2))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.46/1.65  tff(c_439, plain, (![A_101, B_102]: (~v2_struct_0(k7_filter_1(A_101, B_102)) | ~l3_lattices(B_102) | v2_struct_0(B_102) | ~l3_lattices(A_101) | v2_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.46/1.65  tff(c_476, plain, (![B_119, A_120]: (~l3_lattices(B_119) | v2_struct_0(B_119) | ~l3_lattices(A_120) | v2_struct_0(A_120) | v14_lattices(k7_filter_1(A_120, B_119)) | ~v15_lattices(k7_filter_1(A_120, B_119)) | ~l3_lattices(k7_filter_1(A_120, B_119)))), inference(resolution, [status(thm)], [c_6, c_439])).
% 3.46/1.65  tff(c_479, plain, (~l3_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1') | v14_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_55, c_476])).
% 3.46/1.65  tff(c_482, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1') | v14_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_479])).
% 3.46/1.65  tff(c_483, plain, (v14_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_42, c_36, c_482])).
% 3.46/1.65  tff(c_492, plain, (~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_483])).
% 3.46/1.65  tff(c_495, plain, (~l3_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_12, c_492])).
% 3.46/1.65  tff(c_498, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_495])).
% 3.46/1.65  tff(c_500, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_36, c_498])).
% 3.46/1.65  tff(c_501, plain, (v14_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_483])).
% 3.46/1.65  tff(c_30, plain, (![A_10, B_12]: (v14_lattices(A_10) | ~v14_lattices(k7_filter_1(A_10, B_12)) | ~l3_lattices(B_12) | ~v10_lattices(B_12) | v2_struct_0(B_12) | ~l3_lattices(A_10) | ~v10_lattices(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.46/1.65  tff(c_521, plain, (v14_lattices('#skF_1') | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_501, c_30])).
% 3.46/1.65  tff(c_527, plain, (v14_lattices('#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_34, c_32, c_521])).
% 3.46/1.65  tff(c_529, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_36, c_437, c_527])).
% 3.46/1.65  tff(c_530, plain, (~v15_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_58])).
% 3.46/1.65  tff(c_558, plain, (![A_125]: (v15_lattices(A_125) | ~v14_lattices(A_125) | ~v13_lattices(A_125) | v2_struct_0(A_125) | ~l3_lattices(A_125))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.46/1.65  tff(c_561, plain, (v15_lattices('#skF_2') | ~v14_lattices('#skF_2') | ~v13_lattices('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_558, c_36])).
% 3.46/1.65  tff(c_567, plain, (v15_lattices('#skF_2') | ~v14_lattices('#skF_2') | ~v13_lattices('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_561])).
% 3.46/1.65  tff(c_568, plain, (~v14_lattices('#skF_2') | ~v13_lattices('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_530, c_567])).
% 3.46/1.65  tff(c_572, plain, (~v13_lattices('#skF_2')), inference(splitLeft, [status(thm)], [c_568])).
% 3.46/1.65  tff(c_575, plain, (![A_130, B_131]: (~v2_struct_0(k7_filter_1(A_130, B_131)) | ~l3_lattices(B_131) | v2_struct_0(B_131) | ~l3_lattices(A_130) | v2_struct_0(A_130))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.46/1.65  tff(c_610, plain, (![B_144, A_145]: (~l3_lattices(B_144) | v2_struct_0(B_144) | ~l3_lattices(A_145) | v2_struct_0(A_145) | v14_lattices(k7_filter_1(A_145, B_144)) | ~v15_lattices(k7_filter_1(A_145, B_144)) | ~l3_lattices(k7_filter_1(A_145, B_144)))), inference(resolution, [status(thm)], [c_6, c_575])).
% 3.46/1.65  tff(c_613, plain, (~l3_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1') | v14_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_55, c_610])).
% 3.46/1.65  tff(c_616, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1') | v14_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_613])).
% 3.46/1.65  tff(c_617, plain, (v14_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_42, c_36, c_616])).
% 3.46/1.65  tff(c_618, plain, (~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_617])).
% 3.46/1.65  tff(c_621, plain, (~l3_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_12, c_618])).
% 3.46/1.65  tff(c_624, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_621])).
% 3.46/1.65  tff(c_626, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_36, c_624])).
% 3.46/1.65  tff(c_628, plain, (l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_617])).
% 3.46/1.65  tff(c_643, plain, (![B_146, A_147]: (~l3_lattices(B_146) | v2_struct_0(B_146) | ~l3_lattices(A_147) | v2_struct_0(A_147) | v13_lattices(k7_filter_1(A_147, B_146)) | ~v15_lattices(k7_filter_1(A_147, B_146)) | ~l3_lattices(k7_filter_1(A_147, B_146)))), inference(resolution, [status(thm)], [c_8, c_575])).
% 3.46/1.65  tff(c_646, plain, (~l3_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1') | v13_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_55, c_643])).
% 3.46/1.65  tff(c_649, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1') | v13_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_628, c_38, c_32, c_646])).
% 3.46/1.65  tff(c_650, plain, (v13_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_42, c_36, c_649])).
% 3.46/1.65  tff(c_22, plain, (![B_9, A_7]: (v13_lattices(B_9) | ~v13_lattices(k7_filter_1(A_7, B_9)) | ~l3_lattices(B_9) | ~v10_lattices(B_9) | v2_struct_0(B_9) | ~l3_lattices(A_7) | ~v10_lattices(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.46/1.65  tff(c_656, plain, (v13_lattices('#skF_2') | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_650, c_22])).
% 3.46/1.65  tff(c_663, plain, (v13_lattices('#skF_2') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_34, c_32, c_656])).
% 3.46/1.65  tff(c_665, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_36, c_572, c_663])).
% 3.46/1.65  tff(c_666, plain, (~v14_lattices('#skF_2')), inference(splitRight, [status(thm)], [c_568])).
% 3.46/1.65  tff(c_668, plain, (![A_148, B_149]: (~v2_struct_0(k7_filter_1(A_148, B_149)) | ~l3_lattices(B_149) | v2_struct_0(B_149) | ~l3_lattices(A_148) | v2_struct_0(A_148))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.46/1.65  tff(c_705, plain, (![B_166, A_167]: (~l3_lattices(B_166) | v2_struct_0(B_166) | ~l3_lattices(A_167) | v2_struct_0(A_167) | v14_lattices(k7_filter_1(A_167, B_166)) | ~v15_lattices(k7_filter_1(A_167, B_166)) | ~l3_lattices(k7_filter_1(A_167, B_166)))), inference(resolution, [status(thm)], [c_6, c_668])).
% 3.46/1.65  tff(c_708, plain, (~l3_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1') | v14_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_55, c_705])).
% 3.46/1.65  tff(c_711, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1') | v14_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_708])).
% 3.46/1.65  tff(c_712, plain, (v14_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_42, c_36, c_711])).
% 3.46/1.65  tff(c_713, plain, (~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_712])).
% 3.46/1.65  tff(c_716, plain, (~l3_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_12, c_713])).
% 3.46/1.65  tff(c_719, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_716])).
% 3.46/1.65  tff(c_721, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_36, c_719])).
% 3.46/1.65  tff(c_722, plain, (v14_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_712])).
% 3.46/1.65  tff(c_28, plain, (![B_12, A_10]: (v14_lattices(B_12) | ~v14_lattices(k7_filter_1(A_10, B_12)) | ~l3_lattices(B_12) | ~v10_lattices(B_12) | v2_struct_0(B_12) | ~l3_lattices(A_10) | ~v10_lattices(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.46/1.65  tff(c_729, plain, (v14_lattices('#skF_2') | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_722, c_28])).
% 3.46/1.65  tff(c_736, plain, (v14_lattices('#skF_2') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_34, c_32, c_729])).
% 3.46/1.65  tff(c_738, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_36, c_666, c_736])).
% 3.46/1.65  tff(c_739, plain, (v15_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_54])).
% 3.46/1.65  tff(c_757, plain, (![A_169]: (v13_lattices(A_169) | ~v15_lattices(A_169) | v2_struct_0(A_169) | ~l3_lattices(A_169))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.46/1.65  tff(c_763, plain, (v13_lattices('#skF_1') | ~v15_lattices('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_757, c_42])).
% 3.46/1.65  tff(c_769, plain, (v13_lattices('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_739, c_763])).
% 3.46/1.65  tff(c_740, plain, (~v15_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_54])).
% 3.46/1.65  tff(c_52, plain, (v15_lattices('#skF_2') | v15_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.46/1.65  tff(c_741, plain, (v15_lattices('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_740, c_52])).
% 3.46/1.65  tff(c_760, plain, (v13_lattices('#skF_2') | ~v15_lattices('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_757, c_36])).
% 3.46/1.65  tff(c_766, plain, (v13_lattices('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_741, c_760])).
% 3.46/1.65  tff(c_20, plain, (![A_7, B_9]: (v13_lattices(k7_filter_1(A_7, B_9)) | ~v13_lattices(B_9) | ~v13_lattices(A_7) | ~l3_lattices(B_9) | ~v10_lattices(B_9) | v2_struct_0(B_9) | ~l3_lattices(A_7) | ~v10_lattices(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.46/1.65  tff(c_742, plain, (![A_168]: (v14_lattices(A_168) | ~v15_lattices(A_168) | v2_struct_0(A_168) | ~l3_lattices(A_168))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.46/1.65  tff(c_748, plain, (v14_lattices('#skF_1') | ~v15_lattices('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_742, c_42])).
% 3.46/1.65  tff(c_754, plain, (v14_lattices('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_739, c_748])).
% 3.46/1.65  tff(c_745, plain, (v14_lattices('#skF_2') | ~v15_lattices('#skF_2') | ~l3_lattices('#skF_2')), inference(resolution, [status(thm)], [c_742, c_36])).
% 3.46/1.65  tff(c_751, plain, (v14_lattices('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_741, c_745])).
% 3.46/1.65  tff(c_26, plain, (![A_10, B_12]: (v14_lattices(k7_filter_1(A_10, B_12)) | ~v14_lattices(B_12) | ~v14_lattices(A_10) | ~l3_lattices(B_12) | ~v10_lattices(B_12) | v2_struct_0(B_12) | ~l3_lattices(A_10) | ~v10_lattices(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.46/1.65  tff(c_2, plain, (![A_1]: (v15_lattices(A_1) | ~v14_lattices(A_1) | ~v13_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.46/1.65  tff(c_784, plain, (![A_173, B_174]: (~v2_struct_0(k7_filter_1(A_173, B_174)) | ~l3_lattices(B_174) | v2_struct_0(B_174) | ~l3_lattices(A_173) | v2_struct_0(A_173))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.46/1.65  tff(c_822, plain, (![B_193, A_194]: (~l3_lattices(B_193) | v2_struct_0(B_193) | ~l3_lattices(A_194) | v2_struct_0(A_194) | v15_lattices(k7_filter_1(A_194, B_193)) | ~v14_lattices(k7_filter_1(A_194, B_193)) | ~v13_lattices(k7_filter_1(A_194, B_193)) | ~l3_lattices(k7_filter_1(A_194, B_193)))), inference(resolution, [status(thm)], [c_2, c_784])).
% 3.46/1.65  tff(c_831, plain, (~l3_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1') | ~v14_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v13_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_822, c_740])).
% 3.46/1.65  tff(c_836, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1') | ~v14_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v13_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_831])).
% 3.46/1.65  tff(c_837, plain, (~v14_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v13_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_42, c_36, c_836])).
% 3.46/1.65  tff(c_838, plain, (~l3_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_837])).
% 3.46/1.65  tff(c_841, plain, (~l3_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_12, c_838])).
% 3.46/1.65  tff(c_844, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_841])).
% 3.46/1.65  tff(c_846, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_36, c_844])).
% 3.46/1.65  tff(c_847, plain, (~v13_lattices(k7_filter_1('#skF_1', '#skF_2')) | ~v14_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_837])).
% 3.46/1.65  tff(c_849, plain, (~v14_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_847])).
% 3.46/1.65  tff(c_852, plain, (~v14_lattices('#skF_2') | ~v14_lattices('#skF_1') | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_849])).
% 3.46/1.65  tff(c_855, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_34, c_32, c_754, c_751, c_852])).
% 3.46/1.65  tff(c_857, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_36, c_855])).
% 3.46/1.65  tff(c_858, plain, (~v13_lattices(k7_filter_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_847])).
% 3.46/1.65  tff(c_862, plain, (~v13_lattices('#skF_2') | ~v13_lattices('#skF_1') | ~l3_lattices('#skF_2') | ~v10_lattices('#skF_2') | v2_struct_0('#skF_2') | ~l3_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_858])).
% 3.46/1.65  tff(c_865, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_34, c_32, c_769, c_766, c_862])).
% 3.46/1.65  tff(c_867, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_36, c_865])).
% 3.46/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.65  
% 3.46/1.65  Inference rules
% 3.46/1.65  ----------------------
% 3.46/1.65  #Ref     : 0
% 3.46/1.65  #Sup     : 121
% 3.46/1.65  #Fact    : 0
% 3.46/1.65  #Define  : 0
% 3.46/1.65  #Split   : 17
% 3.46/1.65  #Chain   : 0
% 3.46/1.65  #Close   : 0
% 3.46/1.65  
% 3.46/1.65  Ordering : KBO
% 3.46/1.65  
% 3.46/1.65  Simplification rules
% 3.46/1.65  ----------------------
% 3.46/1.65  #Subsume      : 8
% 3.46/1.65  #Demod        : 171
% 3.46/1.65  #Tautology    : 50
% 3.46/1.65  #SimpNegUnit  : 43
% 3.46/1.65  #BackRed      : 0
% 3.46/1.65  
% 3.46/1.65  #Partial instantiations: 0
% 3.46/1.65  #Strategies tried      : 1
% 3.46/1.65  
% 3.46/1.65  Timing (in seconds)
% 3.46/1.65  ----------------------
% 3.46/1.65  Preprocessing        : 0.34
% 3.46/1.65  Parsing              : 0.18
% 3.46/1.65  CNF conversion       : 0.02
% 3.46/1.65  Main loop            : 0.46
% 3.46/1.65  Inferencing          : 0.19
% 3.46/1.65  Reduction            : 0.12
% 3.46/1.65  Demodulation         : 0.08
% 3.46/1.65  BG Simplification    : 0.03
% 3.46/1.65  Subsumption          : 0.09
% 3.46/1.65  Abstraction          : 0.02
% 3.46/1.65  MUC search           : 0.00
% 3.46/1.65  Cooper               : 0.00
% 3.46/1.65  Total                : 0.87
% 3.46/1.65  Index Insertion      : 0.00
% 3.46/1.65  Index Deletion       : 0.00
% 3.46/1.65  Index Matching       : 0.00
% 3.46/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
