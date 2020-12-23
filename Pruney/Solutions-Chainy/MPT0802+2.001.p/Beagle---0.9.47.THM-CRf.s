%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:49 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 255 expanded)
%              Number of leaves         :   31 ( 110 expanded)
%              Depth                    :   10
%              Number of atoms          :  295 ( 991 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_wellord1 > r8_relat_2 > r6_relat_2 > r4_relat_2 > r2_wellord1 > r1_wellord1 > r1_relat_2 > v8_relat_2 > v6_relat_2 > v4_relat_2 > v2_wellord1 > v1_wellord1 > v1_relat_2 > v1_relat_1 > v1_funct_1 > #nlpp > k3_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r4_relat_2,type,(
    r4_relat_2: ( $i * $i ) > $o )).

tff(r1_wellord1,type,(
    r1_wellord1: ( $i * $i ) > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(r3_wellord1,type,(
    r3_wellord1: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(r6_relat_2,type,(
    r6_relat_2: ( $i * $i ) > $o )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(v6_relat_2,type,(
    v6_relat_2: $i > $o )).

tff(r1_relat_2,type,(
    r1_relat_2: ( $i * $i ) > $o )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(r2_wellord1,type,(
    r2_wellord1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r8_relat_2,type,(
    r8_relat_2: ( $i * $i ) > $o )).

tff(v1_wellord1,type,(
    v1_wellord1: $i > $o )).

tff(f_125,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v1_funct_1(C) )
               => ( ( v2_wellord1(A)
                    & r3_wellord1(A,B,C) )
                 => v2_wellord1(B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_wellord1)).

tff(f_96,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ( r3_wellord1(A,B,C)
               => ( ( v1_relat_2(A)
                   => v1_relat_2(B) )
                  & ( v8_relat_2(A)
                   => v8_relat_2(B) )
                  & ( v6_relat_2(A)
                   => v6_relat_2(B) )
                  & ( v4_relat_2(A)
                   => v4_relat_2(B) )
                  & ( v1_wellord1(A)
                   => v1_wellord1(B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_wellord1)).

tff(f_108,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( r2_wellord1(A,k3_relat_1(A))
      <=> v2_wellord1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r2_wellord1(A,B)
        <=> ( r1_relat_2(A,B)
            & r8_relat_2(A,B)
            & r4_relat_2(A,B)
            & r6_relat_2(A,B)
            & r1_wellord1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_wellord1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v1_relat_2(A)
      <=> r1_relat_2(A,k3_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_relat_2)).

tff(f_102,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v1_wellord1(A)
      <=> r1_wellord1(A,k3_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_wellord1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v4_relat_2(A)
      <=> r4_relat_2(A,k3_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_2)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v6_relat_2(A)
      <=> r6_relat_2(A,k3_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_2)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v8_relat_2(A)
      <=> r8_relat_2(A,k3_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_2)).

tff(c_48,plain,(
    ~ v2_wellord1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_58,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_60,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_56,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_54,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_50,plain,(
    r3_wellord1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_345,plain,(
    ! [B_91,A_92,C_93] :
      ( v1_relat_2(B_91)
      | ~ v1_relat_2(A_92)
      | ~ r3_wellord1(A_92,B_91,C_93)
      | ~ v1_funct_1(C_93)
      | ~ v1_relat_1(C_93)
      | ~ v1_relat_1(B_91)
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_348,plain,
    ( v1_relat_2('#skF_2')
    | ~ v1_relat_2('#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_345])).

tff(c_351,plain,
    ( v1_relat_2('#skF_2')
    | ~ v1_relat_2('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_348])).

tff(c_352,plain,(
    ~ v1_relat_2('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_351])).

tff(c_52,plain,(
    v2_wellord1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_44,plain,(
    ! [A_16] :
      ( r2_wellord1(A_16,k3_relat_1(A_16))
      | ~ v2_wellord1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_103,plain,(
    ! [A_36,B_37] :
      ( r1_relat_2(A_36,B_37)
      | ~ r2_wellord1(A_36,B_37)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_371,plain,(
    ! [A_98] :
      ( r1_relat_2(A_98,k3_relat_1(A_98))
      | ~ v2_wellord1(A_98)
      | ~ v1_relat_1(A_98) ) ),
    inference(resolution,[status(thm)],[c_44,c_103])).

tff(c_26,plain,(
    ! [A_7] :
      ( v1_relat_2(A_7)
      | ~ r1_relat_2(A_7,k3_relat_1(A_7))
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_385,plain,(
    ! [A_101] :
      ( v1_relat_2(A_101)
      | ~ v2_wellord1(A_101)
      | ~ v1_relat_1(A_101) ) ),
    inference(resolution,[status(thm)],[c_371,c_26])).

tff(c_388,plain,
    ( v1_relat_2('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_385])).

tff(c_391,plain,(
    v1_relat_2('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_388])).

tff(c_393,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_352,c_391])).

tff(c_394,plain,(
    v1_relat_2('#skF_2') ),
    inference(splitRight,[status(thm)],[c_351])).

tff(c_77,plain,(
    ! [A_30] :
      ( r2_wellord1(A_30,k3_relat_1(A_30))
      | ~ v2_wellord1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_16,plain,(
    ! [A_4,B_6] :
      ( r1_wellord1(A_4,B_6)
      | ~ r2_wellord1(A_4,B_6)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_301,plain,(
    ! [A_81] :
      ( r1_wellord1(A_81,k3_relat_1(A_81))
      | ~ v2_wellord1(A_81)
      | ~ v1_relat_1(A_81) ) ),
    inference(resolution,[status(thm)],[c_77,c_16])).

tff(c_40,plain,(
    ! [A_15] :
      ( v1_wellord1(A_15)
      | ~ r1_wellord1(A_15,k3_relat_1(A_15))
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_306,plain,(
    ! [A_82] :
      ( v1_wellord1(A_82)
      | ~ v2_wellord1(A_82)
      | ~ v1_relat_1(A_82) ) ),
    inference(resolution,[status(thm)],[c_301,c_40])).

tff(c_309,plain,
    ( v1_wellord1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_306])).

tff(c_312,plain,(
    v1_wellord1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_309])).

tff(c_313,plain,(
    ! [B_83,A_84,C_85] :
      ( v1_wellord1(B_83)
      | ~ v1_wellord1(A_84)
      | ~ r3_wellord1(A_84,B_83,C_85)
      | ~ v1_funct_1(C_85)
      | ~ v1_relat_1(C_85)
      | ~ v1_relat_1(B_83)
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_316,plain,
    ( v1_wellord1('#skF_2')
    | ~ v1_wellord1('#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_313])).

tff(c_319,plain,
    ( v1_wellord1('#skF_2')
    | ~ v1_wellord1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_316])).

tff(c_321,plain,(
    v1_wellord1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_319])).

tff(c_92,plain,(
    ! [A_33,B_34] :
      ( r4_relat_2(A_33,B_34)
      | ~ r2_wellord1(A_33,B_34)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [A_1] :
      ( v4_relat_2(A_1)
      | ~ r4_relat_2(A_1,k3_relat_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_125,plain,(
    ! [A_43] :
      ( v4_relat_2(A_43)
      | ~ r2_wellord1(A_43,k3_relat_1(A_43))
      | ~ v1_relat_1(A_43) ) ),
    inference(resolution,[status(thm)],[c_92,c_2])).

tff(c_129,plain,(
    ! [A_16] :
      ( v4_relat_2(A_16)
      | ~ v2_wellord1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(resolution,[status(thm)],[c_44,c_125])).

tff(c_396,plain,(
    ! [B_102,A_103,C_104] :
      ( v4_relat_2(B_102)
      | ~ v4_relat_2(A_103)
      | ~ r3_wellord1(A_103,B_102,C_104)
      | ~ v1_funct_1(C_104)
      | ~ v1_relat_1(C_104)
      | ~ v1_relat_1(B_102)
      | ~ v1_relat_1(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_399,plain,
    ( v4_relat_2('#skF_2')
    | ~ v4_relat_2('#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_396])).

tff(c_402,plain,
    ( v4_relat_2('#skF_2')
    | ~ v4_relat_2('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_399])).

tff(c_403,plain,(
    ~ v4_relat_2('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_402])).

tff(c_406,plain,
    ( ~ v2_wellord1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_129,c_403])).

tff(c_410,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_52,c_406])).

tff(c_411,plain,(
    v4_relat_2('#skF_2') ),
    inference(splitRight,[status(thm)],[c_402])).

tff(c_119,plain,(
    ! [A_41,B_42] :
      ( r6_relat_2(A_41,B_42)
      | ~ r2_wellord1(A_41,B_42)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [A_2] :
      ( v6_relat_2(A_2)
      | ~ r6_relat_2(A_2,k3_relat_1(A_2))
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_322,plain,(
    ! [A_86] :
      ( v6_relat_2(A_86)
      | ~ r2_wellord1(A_86,k3_relat_1(A_86))
      | ~ v1_relat_1(A_86) ) ),
    inference(resolution,[status(thm)],[c_119,c_6])).

tff(c_335,plain,(
    ! [A_90] :
      ( v6_relat_2(A_90)
      | ~ v2_wellord1(A_90)
      | ~ v1_relat_1(A_90) ) ),
    inference(resolution,[status(thm)],[c_44,c_322])).

tff(c_327,plain,(
    ! [B_87,A_88,C_89] :
      ( v6_relat_2(B_87)
      | ~ v6_relat_2(A_88)
      | ~ r3_wellord1(A_88,B_87,C_89)
      | ~ v1_funct_1(C_89)
      | ~ v1_relat_1(C_89)
      | ~ v1_relat_1(B_87)
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_330,plain,
    ( v6_relat_2('#skF_2')
    | ~ v6_relat_2('#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_327])).

tff(c_333,plain,
    ( v6_relat_2('#skF_2')
    | ~ v6_relat_2('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_330])).

tff(c_334,plain,(
    ~ v6_relat_2('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_333])).

tff(c_338,plain,
    ( ~ v2_wellord1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_335,c_334])).

tff(c_342,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_52,c_338])).

tff(c_343,plain,(
    v6_relat_2('#skF_2') ),
    inference(splitRight,[status(thm)],[c_333])).

tff(c_108,plain,(
    ! [A_38,B_39] :
      ( r8_relat_2(A_38,B_39)
      | ~ r2_wellord1(A_38,B_39)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10,plain,(
    ! [A_3] :
      ( v8_relat_2(A_3)
      | ~ r8_relat_2(A_3,k3_relat_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_285,plain,(
    ! [A_78] :
      ( v8_relat_2(A_78)
      | ~ r2_wellord1(A_78,k3_relat_1(A_78))
      | ~ v1_relat_1(A_78) ) ),
    inference(resolution,[status(thm)],[c_108,c_10])).

tff(c_290,plain,(
    ! [A_79] :
      ( v8_relat_2(A_79)
      | ~ v2_wellord1(A_79)
      | ~ v1_relat_1(A_79) ) ),
    inference(resolution,[status(thm)],[c_44,c_285])).

tff(c_130,plain,(
    ! [B_44,A_45,C_46] :
      ( v8_relat_2(B_44)
      | ~ v8_relat_2(A_45)
      | ~ r3_wellord1(A_45,B_44,C_46)
      | ~ v1_funct_1(C_46)
      | ~ v1_relat_1(C_46)
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_133,plain,
    ( v8_relat_2('#skF_2')
    | ~ v8_relat_2('#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_130])).

tff(c_136,plain,
    ( v8_relat_2('#skF_2')
    | ~ v8_relat_2('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_133])).

tff(c_137,plain,(
    ~ v8_relat_2('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_293,plain,
    ( ~ v2_wellord1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_290,c_137])).

tff(c_297,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_52,c_293])).

tff(c_298,plain,(
    v8_relat_2('#skF_2') ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_28,plain,(
    ! [A_7] :
      ( r1_relat_2(A_7,k3_relat_1(A_7))
      | ~ v1_relat_2(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_42,plain,(
    ! [A_15] :
      ( r1_wellord1(A_15,k3_relat_1(A_15))
      | ~ v1_wellord1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_4,plain,(
    ! [A_1] :
      ( r4_relat_2(A_1,k3_relat_1(A_1))
      | ~ v4_relat_2(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_2] :
      ( r6_relat_2(A_2,k3_relat_1(A_2))
      | ~ v6_relat_2(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_3] :
      ( r8_relat_2(A_3,k3_relat_1(A_3))
      | ~ v8_relat_2(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_414,plain,(
    ! [A_106,B_107] :
      ( r2_wellord1(A_106,B_107)
      | ~ r1_wellord1(A_106,B_107)
      | ~ r6_relat_2(A_106,B_107)
      | ~ r4_relat_2(A_106,B_107)
      | ~ r8_relat_2(A_106,B_107)
      | ~ r1_relat_2(A_106,B_107)
      | ~ v1_relat_1(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_441,plain,(
    ! [A_112] :
      ( r2_wellord1(A_112,k3_relat_1(A_112))
      | ~ r1_wellord1(A_112,k3_relat_1(A_112))
      | ~ r6_relat_2(A_112,k3_relat_1(A_112))
      | ~ r4_relat_2(A_112,k3_relat_1(A_112))
      | ~ r1_relat_2(A_112,k3_relat_1(A_112))
      | ~ v8_relat_2(A_112)
      | ~ v1_relat_1(A_112) ) ),
    inference(resolution,[status(thm)],[c_12,c_414])).

tff(c_451,plain,(
    ! [A_113] :
      ( r2_wellord1(A_113,k3_relat_1(A_113))
      | ~ r1_wellord1(A_113,k3_relat_1(A_113))
      | ~ r4_relat_2(A_113,k3_relat_1(A_113))
      | ~ r1_relat_2(A_113,k3_relat_1(A_113))
      | ~ v8_relat_2(A_113)
      | ~ v6_relat_2(A_113)
      | ~ v1_relat_1(A_113) ) ),
    inference(resolution,[status(thm)],[c_8,c_441])).

tff(c_461,plain,(
    ! [A_114] :
      ( r2_wellord1(A_114,k3_relat_1(A_114))
      | ~ r1_wellord1(A_114,k3_relat_1(A_114))
      | ~ r1_relat_2(A_114,k3_relat_1(A_114))
      | ~ v8_relat_2(A_114)
      | ~ v6_relat_2(A_114)
      | ~ v4_relat_2(A_114)
      | ~ v1_relat_1(A_114) ) ),
    inference(resolution,[status(thm)],[c_4,c_451])).

tff(c_46,plain,(
    ! [A_16] :
      ( v2_wellord1(A_16)
      | ~ r2_wellord1(A_16,k3_relat_1(A_16))
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_486,plain,(
    ! [A_115] :
      ( v2_wellord1(A_115)
      | ~ r1_wellord1(A_115,k3_relat_1(A_115))
      | ~ r1_relat_2(A_115,k3_relat_1(A_115))
      | ~ v8_relat_2(A_115)
      | ~ v6_relat_2(A_115)
      | ~ v4_relat_2(A_115)
      | ~ v1_relat_1(A_115) ) ),
    inference(resolution,[status(thm)],[c_461,c_46])).

tff(c_495,plain,(
    ! [A_116] :
      ( v2_wellord1(A_116)
      | ~ r1_relat_2(A_116,k3_relat_1(A_116))
      | ~ v8_relat_2(A_116)
      | ~ v6_relat_2(A_116)
      | ~ v4_relat_2(A_116)
      | ~ v1_wellord1(A_116)
      | ~ v1_relat_1(A_116) ) ),
    inference(resolution,[status(thm)],[c_42,c_486])).

tff(c_504,plain,(
    ! [A_117] :
      ( v2_wellord1(A_117)
      | ~ v8_relat_2(A_117)
      | ~ v6_relat_2(A_117)
      | ~ v4_relat_2(A_117)
      | ~ v1_wellord1(A_117)
      | ~ v1_relat_2(A_117)
      | ~ v1_relat_1(A_117) ) ),
    inference(resolution,[status(thm)],[c_28,c_495])).

tff(c_513,plain,
    ( v2_wellord1('#skF_2')
    | ~ v6_relat_2('#skF_2')
    | ~ v4_relat_2('#skF_2')
    | ~ v1_wellord1('#skF_2')
    | ~ v1_relat_2('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_298,c_504])).

tff(c_520,plain,(
    v2_wellord1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_394,c_321,c_411,c_343,c_513])).

tff(c_522,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_520])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n006.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 20:16:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.64/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.42  
% 2.87/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.43  %$ r3_wellord1 > r8_relat_2 > r6_relat_2 > r4_relat_2 > r2_wellord1 > r1_wellord1 > r1_relat_2 > v8_relat_2 > v6_relat_2 > v4_relat_2 > v2_wellord1 > v1_wellord1 > v1_relat_2 > v1_relat_1 > v1_funct_1 > #nlpp > k3_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.87/1.43  
% 2.87/1.43  %Foreground sorts:
% 2.87/1.43  
% 2.87/1.43  
% 2.87/1.43  %Background operators:
% 2.87/1.43  
% 2.87/1.43  
% 2.87/1.43  %Foreground operators:
% 2.87/1.43  tff(r4_relat_2, type, r4_relat_2: ($i * $i) > $o).
% 2.87/1.43  tff(r1_wellord1, type, r1_wellord1: ($i * $i) > $o).
% 2.87/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.87/1.43  tff(r3_wellord1, type, r3_wellord1: ($i * $i * $i) > $o).
% 2.87/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.43  tff(v1_relat_2, type, v1_relat_2: $i > $o).
% 2.87/1.43  tff(r6_relat_2, type, r6_relat_2: ($i * $i) > $o).
% 2.87/1.43  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 2.87/1.43  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.87/1.43  tff(v6_relat_2, type, v6_relat_2: $i > $o).
% 2.87/1.43  tff(r1_relat_2, type, r1_relat_2: ($i * $i) > $o).
% 2.87/1.43  tff(v4_relat_2, type, v4_relat_2: $i > $o).
% 2.87/1.43  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 2.87/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.87/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.87/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.87/1.43  tff(r2_wellord1, type, r2_wellord1: ($i * $i) > $o).
% 2.87/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.87/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.43  tff(r8_relat_2, type, r8_relat_2: ($i * $i) > $o).
% 2.87/1.43  tff(v1_wellord1, type, v1_wellord1: $i > $o).
% 2.87/1.43  
% 2.99/1.45  tff(f_125, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((v2_wellord1(A) & r3_wellord1(A, B, C)) => v2_wellord1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_wellord1)).
% 2.99/1.45  tff(f_96, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r3_wellord1(A, B, C) => (((((v1_relat_2(A) => v1_relat_2(B)) & (v8_relat_2(A) => v8_relat_2(B))) & (v6_relat_2(A) => v6_relat_2(B))) & (v4_relat_2(A) => v4_relat_2(B))) & (v1_wellord1(A) => v1_wellord1(B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_wellord1)).
% 2.99/1.45  tff(f_108, axiom, (![A]: (v1_relat_1(A) => (r2_wellord1(A, k3_relat_1(A)) <=> v2_wellord1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_wellord1)).
% 2.99/1.45  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (r2_wellord1(A, B) <=> ((((r1_relat_2(A, B) & r8_relat_2(A, B)) & r4_relat_2(A, B)) & r6_relat_2(A, B)) & r1_wellord1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_wellord1)).
% 2.99/1.45  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (v1_relat_2(A) <=> r1_relat_2(A, k3_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_relat_2)).
% 2.99/1.45  tff(f_102, axiom, (![A]: (v1_relat_1(A) => (v1_wellord1(A) <=> r1_wellord1(A, k3_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_wellord1)).
% 2.99/1.45  tff(f_31, axiom, (![A]: (v1_relat_1(A) => (v4_relat_2(A) <=> r4_relat_2(A, k3_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_relat_2)).
% 2.99/1.45  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (v6_relat_2(A) <=> r6_relat_2(A, k3_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_2)).
% 2.99/1.45  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (v8_relat_2(A) <=> r8_relat_2(A, k3_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_2)).
% 2.99/1.45  tff(c_48, plain, (~v2_wellord1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.99/1.45  tff(c_58, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.99/1.45  tff(c_60, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.99/1.45  tff(c_56, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.99/1.45  tff(c_54, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.99/1.45  tff(c_50, plain, (r3_wellord1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.99/1.45  tff(c_345, plain, (![B_91, A_92, C_93]: (v1_relat_2(B_91) | ~v1_relat_2(A_92) | ~r3_wellord1(A_92, B_91, C_93) | ~v1_funct_1(C_93) | ~v1_relat_1(C_93) | ~v1_relat_1(B_91) | ~v1_relat_1(A_92))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.99/1.45  tff(c_348, plain, (v1_relat_2('#skF_2') | ~v1_relat_2('#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_50, c_345])).
% 2.99/1.45  tff(c_351, plain, (v1_relat_2('#skF_2') | ~v1_relat_2('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_348])).
% 2.99/1.45  tff(c_352, plain, (~v1_relat_2('#skF_1')), inference(splitLeft, [status(thm)], [c_351])).
% 2.99/1.45  tff(c_52, plain, (v2_wellord1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.99/1.45  tff(c_44, plain, (![A_16]: (r2_wellord1(A_16, k3_relat_1(A_16)) | ~v2_wellord1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.99/1.45  tff(c_103, plain, (![A_36, B_37]: (r1_relat_2(A_36, B_37) | ~r2_wellord1(A_36, B_37) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.99/1.45  tff(c_371, plain, (![A_98]: (r1_relat_2(A_98, k3_relat_1(A_98)) | ~v2_wellord1(A_98) | ~v1_relat_1(A_98))), inference(resolution, [status(thm)], [c_44, c_103])).
% 2.99/1.45  tff(c_26, plain, (![A_7]: (v1_relat_2(A_7) | ~r1_relat_2(A_7, k3_relat_1(A_7)) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.99/1.45  tff(c_385, plain, (![A_101]: (v1_relat_2(A_101) | ~v2_wellord1(A_101) | ~v1_relat_1(A_101))), inference(resolution, [status(thm)], [c_371, c_26])).
% 2.99/1.45  tff(c_388, plain, (v1_relat_2('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_52, c_385])).
% 2.99/1.45  tff(c_391, plain, (v1_relat_2('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_388])).
% 2.99/1.45  tff(c_393, plain, $false, inference(negUnitSimplification, [status(thm)], [c_352, c_391])).
% 2.99/1.45  tff(c_394, plain, (v1_relat_2('#skF_2')), inference(splitRight, [status(thm)], [c_351])).
% 2.99/1.45  tff(c_77, plain, (![A_30]: (r2_wellord1(A_30, k3_relat_1(A_30)) | ~v2_wellord1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.99/1.45  tff(c_16, plain, (![A_4, B_6]: (r1_wellord1(A_4, B_6) | ~r2_wellord1(A_4, B_6) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.99/1.45  tff(c_301, plain, (![A_81]: (r1_wellord1(A_81, k3_relat_1(A_81)) | ~v2_wellord1(A_81) | ~v1_relat_1(A_81))), inference(resolution, [status(thm)], [c_77, c_16])).
% 2.99/1.45  tff(c_40, plain, (![A_15]: (v1_wellord1(A_15) | ~r1_wellord1(A_15, k3_relat_1(A_15)) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.99/1.45  tff(c_306, plain, (![A_82]: (v1_wellord1(A_82) | ~v2_wellord1(A_82) | ~v1_relat_1(A_82))), inference(resolution, [status(thm)], [c_301, c_40])).
% 2.99/1.45  tff(c_309, plain, (v1_wellord1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_52, c_306])).
% 2.99/1.45  tff(c_312, plain, (v1_wellord1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_309])).
% 2.99/1.45  tff(c_313, plain, (![B_83, A_84, C_85]: (v1_wellord1(B_83) | ~v1_wellord1(A_84) | ~r3_wellord1(A_84, B_83, C_85) | ~v1_funct_1(C_85) | ~v1_relat_1(C_85) | ~v1_relat_1(B_83) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.99/1.45  tff(c_316, plain, (v1_wellord1('#skF_2') | ~v1_wellord1('#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_50, c_313])).
% 2.99/1.45  tff(c_319, plain, (v1_wellord1('#skF_2') | ~v1_wellord1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_316])).
% 2.99/1.45  tff(c_321, plain, (v1_wellord1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_312, c_319])).
% 2.99/1.45  tff(c_92, plain, (![A_33, B_34]: (r4_relat_2(A_33, B_34) | ~r2_wellord1(A_33, B_34) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.99/1.45  tff(c_2, plain, (![A_1]: (v4_relat_2(A_1) | ~r4_relat_2(A_1, k3_relat_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.99/1.45  tff(c_125, plain, (![A_43]: (v4_relat_2(A_43) | ~r2_wellord1(A_43, k3_relat_1(A_43)) | ~v1_relat_1(A_43))), inference(resolution, [status(thm)], [c_92, c_2])).
% 2.99/1.45  tff(c_129, plain, (![A_16]: (v4_relat_2(A_16) | ~v2_wellord1(A_16) | ~v1_relat_1(A_16))), inference(resolution, [status(thm)], [c_44, c_125])).
% 2.99/1.45  tff(c_396, plain, (![B_102, A_103, C_104]: (v4_relat_2(B_102) | ~v4_relat_2(A_103) | ~r3_wellord1(A_103, B_102, C_104) | ~v1_funct_1(C_104) | ~v1_relat_1(C_104) | ~v1_relat_1(B_102) | ~v1_relat_1(A_103))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.99/1.45  tff(c_399, plain, (v4_relat_2('#skF_2') | ~v4_relat_2('#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_50, c_396])).
% 2.99/1.45  tff(c_402, plain, (v4_relat_2('#skF_2') | ~v4_relat_2('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_399])).
% 2.99/1.45  tff(c_403, plain, (~v4_relat_2('#skF_1')), inference(splitLeft, [status(thm)], [c_402])).
% 2.99/1.45  tff(c_406, plain, (~v2_wellord1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_129, c_403])).
% 2.99/1.45  tff(c_410, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_52, c_406])).
% 2.99/1.45  tff(c_411, plain, (v4_relat_2('#skF_2')), inference(splitRight, [status(thm)], [c_402])).
% 2.99/1.45  tff(c_119, plain, (![A_41, B_42]: (r6_relat_2(A_41, B_42) | ~r2_wellord1(A_41, B_42) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.99/1.45  tff(c_6, plain, (![A_2]: (v6_relat_2(A_2) | ~r6_relat_2(A_2, k3_relat_1(A_2)) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.99/1.45  tff(c_322, plain, (![A_86]: (v6_relat_2(A_86) | ~r2_wellord1(A_86, k3_relat_1(A_86)) | ~v1_relat_1(A_86))), inference(resolution, [status(thm)], [c_119, c_6])).
% 2.99/1.45  tff(c_335, plain, (![A_90]: (v6_relat_2(A_90) | ~v2_wellord1(A_90) | ~v1_relat_1(A_90))), inference(resolution, [status(thm)], [c_44, c_322])).
% 2.99/1.45  tff(c_327, plain, (![B_87, A_88, C_89]: (v6_relat_2(B_87) | ~v6_relat_2(A_88) | ~r3_wellord1(A_88, B_87, C_89) | ~v1_funct_1(C_89) | ~v1_relat_1(C_89) | ~v1_relat_1(B_87) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.99/1.45  tff(c_330, plain, (v6_relat_2('#skF_2') | ~v6_relat_2('#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_50, c_327])).
% 2.99/1.45  tff(c_333, plain, (v6_relat_2('#skF_2') | ~v6_relat_2('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_330])).
% 2.99/1.45  tff(c_334, plain, (~v6_relat_2('#skF_1')), inference(splitLeft, [status(thm)], [c_333])).
% 2.99/1.45  tff(c_338, plain, (~v2_wellord1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_335, c_334])).
% 2.99/1.45  tff(c_342, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_52, c_338])).
% 2.99/1.45  tff(c_343, plain, (v6_relat_2('#skF_2')), inference(splitRight, [status(thm)], [c_333])).
% 2.99/1.45  tff(c_108, plain, (![A_38, B_39]: (r8_relat_2(A_38, B_39) | ~r2_wellord1(A_38, B_39) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.99/1.45  tff(c_10, plain, (![A_3]: (v8_relat_2(A_3) | ~r8_relat_2(A_3, k3_relat_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.99/1.45  tff(c_285, plain, (![A_78]: (v8_relat_2(A_78) | ~r2_wellord1(A_78, k3_relat_1(A_78)) | ~v1_relat_1(A_78))), inference(resolution, [status(thm)], [c_108, c_10])).
% 2.99/1.45  tff(c_290, plain, (![A_79]: (v8_relat_2(A_79) | ~v2_wellord1(A_79) | ~v1_relat_1(A_79))), inference(resolution, [status(thm)], [c_44, c_285])).
% 2.99/1.45  tff(c_130, plain, (![B_44, A_45, C_46]: (v8_relat_2(B_44) | ~v8_relat_2(A_45) | ~r3_wellord1(A_45, B_44, C_46) | ~v1_funct_1(C_46) | ~v1_relat_1(C_46) | ~v1_relat_1(B_44) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.99/1.45  tff(c_133, plain, (v8_relat_2('#skF_2') | ~v8_relat_2('#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_50, c_130])).
% 2.99/1.45  tff(c_136, plain, (v8_relat_2('#skF_2') | ~v8_relat_2('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_133])).
% 2.99/1.45  tff(c_137, plain, (~v8_relat_2('#skF_1')), inference(splitLeft, [status(thm)], [c_136])).
% 2.99/1.45  tff(c_293, plain, (~v2_wellord1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_290, c_137])).
% 2.99/1.45  tff(c_297, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_52, c_293])).
% 2.99/1.45  tff(c_298, plain, (v8_relat_2('#skF_2')), inference(splitRight, [status(thm)], [c_136])).
% 2.99/1.45  tff(c_28, plain, (![A_7]: (r1_relat_2(A_7, k3_relat_1(A_7)) | ~v1_relat_2(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.99/1.45  tff(c_42, plain, (![A_15]: (r1_wellord1(A_15, k3_relat_1(A_15)) | ~v1_wellord1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.99/1.45  tff(c_4, plain, (![A_1]: (r4_relat_2(A_1, k3_relat_1(A_1)) | ~v4_relat_2(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.99/1.45  tff(c_8, plain, (![A_2]: (r6_relat_2(A_2, k3_relat_1(A_2)) | ~v6_relat_2(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.99/1.45  tff(c_12, plain, (![A_3]: (r8_relat_2(A_3, k3_relat_1(A_3)) | ~v8_relat_2(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.99/1.45  tff(c_414, plain, (![A_106, B_107]: (r2_wellord1(A_106, B_107) | ~r1_wellord1(A_106, B_107) | ~r6_relat_2(A_106, B_107) | ~r4_relat_2(A_106, B_107) | ~r8_relat_2(A_106, B_107) | ~r1_relat_2(A_106, B_107) | ~v1_relat_1(A_106))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.99/1.45  tff(c_441, plain, (![A_112]: (r2_wellord1(A_112, k3_relat_1(A_112)) | ~r1_wellord1(A_112, k3_relat_1(A_112)) | ~r6_relat_2(A_112, k3_relat_1(A_112)) | ~r4_relat_2(A_112, k3_relat_1(A_112)) | ~r1_relat_2(A_112, k3_relat_1(A_112)) | ~v8_relat_2(A_112) | ~v1_relat_1(A_112))), inference(resolution, [status(thm)], [c_12, c_414])).
% 2.99/1.45  tff(c_451, plain, (![A_113]: (r2_wellord1(A_113, k3_relat_1(A_113)) | ~r1_wellord1(A_113, k3_relat_1(A_113)) | ~r4_relat_2(A_113, k3_relat_1(A_113)) | ~r1_relat_2(A_113, k3_relat_1(A_113)) | ~v8_relat_2(A_113) | ~v6_relat_2(A_113) | ~v1_relat_1(A_113))), inference(resolution, [status(thm)], [c_8, c_441])).
% 2.99/1.45  tff(c_461, plain, (![A_114]: (r2_wellord1(A_114, k3_relat_1(A_114)) | ~r1_wellord1(A_114, k3_relat_1(A_114)) | ~r1_relat_2(A_114, k3_relat_1(A_114)) | ~v8_relat_2(A_114) | ~v6_relat_2(A_114) | ~v4_relat_2(A_114) | ~v1_relat_1(A_114))), inference(resolution, [status(thm)], [c_4, c_451])).
% 2.99/1.45  tff(c_46, plain, (![A_16]: (v2_wellord1(A_16) | ~r2_wellord1(A_16, k3_relat_1(A_16)) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.99/1.45  tff(c_486, plain, (![A_115]: (v2_wellord1(A_115) | ~r1_wellord1(A_115, k3_relat_1(A_115)) | ~r1_relat_2(A_115, k3_relat_1(A_115)) | ~v8_relat_2(A_115) | ~v6_relat_2(A_115) | ~v4_relat_2(A_115) | ~v1_relat_1(A_115))), inference(resolution, [status(thm)], [c_461, c_46])).
% 2.99/1.45  tff(c_495, plain, (![A_116]: (v2_wellord1(A_116) | ~r1_relat_2(A_116, k3_relat_1(A_116)) | ~v8_relat_2(A_116) | ~v6_relat_2(A_116) | ~v4_relat_2(A_116) | ~v1_wellord1(A_116) | ~v1_relat_1(A_116))), inference(resolution, [status(thm)], [c_42, c_486])).
% 2.99/1.45  tff(c_504, plain, (![A_117]: (v2_wellord1(A_117) | ~v8_relat_2(A_117) | ~v6_relat_2(A_117) | ~v4_relat_2(A_117) | ~v1_wellord1(A_117) | ~v1_relat_2(A_117) | ~v1_relat_1(A_117))), inference(resolution, [status(thm)], [c_28, c_495])).
% 2.99/1.45  tff(c_513, plain, (v2_wellord1('#skF_2') | ~v6_relat_2('#skF_2') | ~v4_relat_2('#skF_2') | ~v1_wellord1('#skF_2') | ~v1_relat_2('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_298, c_504])).
% 2.99/1.45  tff(c_520, plain, (v2_wellord1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_394, c_321, c_411, c_343, c_513])).
% 2.99/1.45  tff(c_522, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_520])).
% 2.99/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.45  
% 2.99/1.45  Inference rules
% 2.99/1.45  ----------------------
% 2.99/1.45  #Ref     : 0
% 2.99/1.45  #Sup     : 72
% 2.99/1.45  #Fact    : 0
% 2.99/1.45  #Define  : 0
% 2.99/1.45  #Split   : 11
% 2.99/1.45  #Chain   : 0
% 2.99/1.45  #Close   : 0
% 2.99/1.45  
% 2.99/1.45  Ordering : KBO
% 2.99/1.45  
% 2.99/1.45  Simplification rules
% 2.99/1.45  ----------------------
% 2.99/1.45  #Subsume      : 0
% 2.99/1.45  #Demod        : 84
% 2.99/1.45  #Tautology    : 23
% 2.99/1.45  #SimpNegUnit  : 4
% 2.99/1.45  #BackRed      : 0
% 2.99/1.45  
% 2.99/1.45  #Partial instantiations: 0
% 2.99/1.45  #Strategies tried      : 1
% 2.99/1.45  
% 2.99/1.45  Timing (in seconds)
% 2.99/1.45  ----------------------
% 2.99/1.45  Preprocessing        : 0.30
% 2.99/1.45  Parsing              : 0.17
% 2.99/1.45  CNF conversion       : 0.02
% 2.99/1.45  Main loop            : 0.31
% 2.99/1.45  Inferencing          : 0.14
% 2.99/1.45  Reduction            : 0.08
% 2.99/1.45  Demodulation         : 0.06
% 2.99/1.45  BG Simplification    : 0.02
% 2.99/1.45  Subsumption          : 0.04
% 2.99/1.45  Abstraction          : 0.01
% 2.99/1.45  MUC search           : 0.00
% 2.99/1.45  Cooper               : 0.00
% 2.99/1.45  Total                : 0.66
% 2.99/1.45  Index Insertion      : 0.00
% 2.99/1.45  Index Deletion       : 0.00
% 2.99/1.45  Index Matching       : 0.00
% 2.99/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
