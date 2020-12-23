%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:35 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 271 expanded)
%              Number of leaves         :   26 (  97 expanded)
%              Depth                    :   12
%              Number of atoms          :  222 ( 777 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r8_relat_2 > r6_relat_2 > r4_relat_2 > r2_wellord1 > r1_wellord1 > r1_relat_2 > v8_relat_2 > v6_relat_2 > v4_relat_2 > v2_wellord1 > v1_wellord1 > v1_relat_2 > v1_relat_1 > #nlpp > k3_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r4_relat_2,type,(
    r4_relat_2: ( $i * $i ) > $o )).

tff(r1_wellord1,type,(
    r1_wellord1: ( $i * $i ) > $o )).

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

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( r2_wellord1(A,k3_relat_1(A))
        <=> v2_wellord1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
      <=> ( v1_relat_2(A)
          & v8_relat_2(A)
          & v4_relat_2(A)
          & v6_relat_2(A)
          & v1_wellord1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v1_relat_2(A)
      <=> r1_relat_2(A,k3_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_relat_2)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v1_wellord1(A)
      <=> r1_wellord1(A,k3_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_wellord1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v4_relat_2(A)
      <=> r4_relat_2(A,k3_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_2)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v6_relat_2(A)
      <=> r6_relat_2(A,k3_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_2)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v8_relat_2(A)
      <=> r8_relat_2(A,k3_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_2)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r2_wellord1(A,B)
        <=> ( r1_relat_2(A,B)
            & r8_relat_2(A,B)
            & r4_relat_2(A,B)
            & r6_relat_2(A,B)
            & r1_wellord1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_wellord1)).

tff(c_46,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_48,plain,
    ( ~ v2_wellord1('#skF_1')
    | ~ r2_wellord1('#skF_1',k3_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_55,plain,(
    ~ r2_wellord1('#skF_1',k3_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_54,plain,
    ( r2_wellord1('#skF_1',k3_relat_1('#skF_1'))
    | v2_wellord1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_61,plain,(
    v2_wellord1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_54])).

tff(c_22,plain,(
    ! [A_4] :
      ( v8_relat_2(A_4)
      | ~ v2_wellord1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_24,plain,(
    ! [A_4] :
      ( v1_relat_2(A_4)
      | ~ v2_wellord1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_64,plain,
    ( v1_relat_2('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_61,c_24])).

tff(c_70,plain,(
    v1_relat_2('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_64])).

tff(c_40,plain,(
    ! [A_8] :
      ( r1_relat_2(A_8,k3_relat_1(A_8))
      | ~ v1_relat_2(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_18,plain,(
    ! [A_4] :
      ( v6_relat_2(A_4)
      | ~ v2_wellord1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    ! [A_4] :
      ( v1_wellord1(A_4)
      | ~ v2_wellord1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_67,plain,
    ( v1_wellord1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_61,c_16])).

tff(c_73,plain,(
    v1_wellord1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_67])).

tff(c_44,plain,(
    ! [A_9] :
      ( r1_wellord1(A_9,k3_relat_1(A_9))
      | ~ v1_wellord1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_20,plain,(
    ! [A_4] :
      ( v4_relat_2(A_4)
      | ~ v2_wellord1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

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

tff(c_132,plain,(
    ! [A_39,B_40] :
      ( r2_wellord1(A_39,B_40)
      | ~ r1_wellord1(A_39,B_40)
      | ~ r6_relat_2(A_39,B_40)
      | ~ r4_relat_2(A_39,B_40)
      | ~ r8_relat_2(A_39,B_40)
      | ~ r1_relat_2(A_39,B_40)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_141,plain,(
    ! [A_41] :
      ( r2_wellord1(A_41,k3_relat_1(A_41))
      | ~ r1_wellord1(A_41,k3_relat_1(A_41))
      | ~ r6_relat_2(A_41,k3_relat_1(A_41))
      | ~ r4_relat_2(A_41,k3_relat_1(A_41))
      | ~ r1_relat_2(A_41,k3_relat_1(A_41))
      | ~ v8_relat_2(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(resolution,[status(thm)],[c_12,c_132])).

tff(c_151,plain,(
    ! [A_42] :
      ( r2_wellord1(A_42,k3_relat_1(A_42))
      | ~ r1_wellord1(A_42,k3_relat_1(A_42))
      | ~ r4_relat_2(A_42,k3_relat_1(A_42))
      | ~ r1_relat_2(A_42,k3_relat_1(A_42))
      | ~ v8_relat_2(A_42)
      | ~ v6_relat_2(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(resolution,[status(thm)],[c_8,c_141])).

tff(c_161,plain,(
    ! [A_43] :
      ( r2_wellord1(A_43,k3_relat_1(A_43))
      | ~ r1_wellord1(A_43,k3_relat_1(A_43))
      | ~ r1_relat_2(A_43,k3_relat_1(A_43))
      | ~ v8_relat_2(A_43)
      | ~ v6_relat_2(A_43)
      | ~ v4_relat_2(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(resolution,[status(thm)],[c_4,c_151])).

tff(c_179,plain,
    ( ~ r1_wellord1('#skF_1',k3_relat_1('#skF_1'))
    | ~ r1_relat_2('#skF_1',k3_relat_1('#skF_1'))
    | ~ v8_relat_2('#skF_1')
    | ~ v6_relat_2('#skF_1')
    | ~ v4_relat_2('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_161,c_55])).

tff(c_187,plain,
    ( ~ r1_wellord1('#skF_1',k3_relat_1('#skF_1'))
    | ~ r1_relat_2('#skF_1',k3_relat_1('#skF_1'))
    | ~ v8_relat_2('#skF_1')
    | ~ v6_relat_2('#skF_1')
    | ~ v4_relat_2('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_179])).

tff(c_188,plain,(
    ~ v4_relat_2('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_187])).

tff(c_191,plain,
    ( ~ v2_wellord1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_188])).

tff(c_195,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_61,c_191])).

tff(c_196,plain,
    ( ~ v6_relat_2('#skF_1')
    | ~ v8_relat_2('#skF_1')
    | ~ r1_relat_2('#skF_1',k3_relat_1('#skF_1'))
    | ~ r1_wellord1('#skF_1',k3_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_198,plain,(
    ~ r1_wellord1('#skF_1',k3_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_201,plain,
    ( ~ v1_wellord1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_198])).

tff(c_205,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_73,c_201])).

tff(c_206,plain,
    ( ~ r1_relat_2('#skF_1',k3_relat_1('#skF_1'))
    | ~ v8_relat_2('#skF_1')
    | ~ v6_relat_2('#skF_1') ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_214,plain,(
    ~ v6_relat_2('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_206])).

tff(c_217,plain,
    ( ~ v2_wellord1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_214])).

tff(c_221,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_61,c_217])).

tff(c_222,plain,
    ( ~ v8_relat_2('#skF_1')
    | ~ r1_relat_2('#skF_1',k3_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_224,plain,(
    ~ r1_relat_2('#skF_1',k3_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_222])).

tff(c_227,plain,
    ( ~ v1_relat_2('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_224])).

tff(c_231,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_70,c_227])).

tff(c_232,plain,(
    ~ v8_relat_2('#skF_1') ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_236,plain,
    ( ~ v2_wellord1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_232])).

tff(c_240,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_61,c_236])).

tff(c_241,plain,(
    ~ v2_wellord1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_242,plain,(
    r2_wellord1('#skF_1',k3_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_259,plain,(
    ! [A_55,B_56] :
      ( r1_relat_2(A_55,B_56)
      | ~ r2_wellord1(A_55,B_56)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_262,plain,
    ( r1_relat_2('#skF_1',k3_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_242,c_259])).

tff(c_265,plain,(
    r1_relat_2('#skF_1',k3_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_262])).

tff(c_268,plain,(
    ! [A_60] :
      ( v1_relat_2(A_60)
      | ~ r1_relat_2(A_60,k3_relat_1(A_60))
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_271,plain,
    ( v1_relat_2('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_265,c_268])).

tff(c_274,plain,(
    v1_relat_2('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_271])).

tff(c_32,plain,(
    ! [A_5,B_7] :
      ( r4_relat_2(A_5,B_7)
      | ~ r2_wellord1(A_5,B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_253,plain,(
    ! [A_54] :
      ( v4_relat_2(A_54)
      | ~ r4_relat_2(A_54,k3_relat_1(A_54))
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_324,plain,(
    ! [A_69] :
      ( v4_relat_2(A_69)
      | ~ r2_wellord1(A_69,k3_relat_1(A_69))
      | ~ v1_relat_1(A_69) ) ),
    inference(resolution,[status(thm)],[c_32,c_253])).

tff(c_327,plain,
    ( v4_relat_2('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_242,c_324])).

tff(c_330,plain,(
    v4_relat_2('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_327])).

tff(c_301,plain,(
    ! [A_66,B_67] :
      ( r1_wellord1(A_66,B_67)
      | ~ r2_wellord1(A_66,B_67)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_304,plain,
    ( r1_wellord1('#skF_1',k3_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_242,c_301])).

tff(c_307,plain,(
    r1_wellord1('#skF_1',k3_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_304])).

tff(c_42,plain,(
    ! [A_9] :
      ( v1_wellord1(A_9)
      | ~ r1_wellord1(A_9,k3_relat_1(A_9))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_310,plain,
    ( v1_wellord1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_307,c_42])).

tff(c_313,plain,(
    v1_wellord1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_310])).

tff(c_34,plain,(
    ! [A_5,B_7] :
      ( r8_relat_2(A_5,B_7)
      | ~ r2_wellord1(A_5,B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_286,plain,(
    ! [A_64] :
      ( v8_relat_2(A_64)
      | ~ r8_relat_2(A_64,k3_relat_1(A_64))
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_336,plain,(
    ! [A_71] :
      ( v8_relat_2(A_71)
      | ~ r2_wellord1(A_71,k3_relat_1(A_71))
      | ~ v1_relat_1(A_71) ) ),
    inference(resolution,[status(thm)],[c_34,c_286])).

tff(c_339,plain,
    ( v8_relat_2('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_242,c_336])).

tff(c_342,plain,(
    v8_relat_2('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_339])).

tff(c_14,plain,(
    ! [A_4] :
      ( v2_wellord1(A_4)
      | ~ v1_wellord1(A_4)
      | ~ v6_relat_2(A_4)
      | ~ v4_relat_2(A_4)
      | ~ v8_relat_2(A_4)
      | ~ v1_relat_2(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_345,plain,
    ( v2_wellord1('#skF_1')
    | ~ v1_wellord1('#skF_1')
    | ~ v6_relat_2('#skF_1')
    | ~ v4_relat_2('#skF_1')
    | ~ v1_relat_2('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_342,c_14])).

tff(c_348,plain,
    ( v2_wellord1('#skF_1')
    | ~ v6_relat_2('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_274,c_330,c_313,c_345])).

tff(c_349,plain,(
    ~ v6_relat_2('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_241,c_348])).

tff(c_30,plain,(
    ! [A_5,B_7] :
      ( r6_relat_2(A_5,B_7)
      | ~ r2_wellord1(A_5,B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_314,plain,(
    ! [A_68] :
      ( v6_relat_2(A_68)
      | ~ r6_relat_2(A_68,k3_relat_1(A_68))
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_365,plain,(
    ! [A_74] :
      ( v6_relat_2(A_74)
      | ~ r2_wellord1(A_74,k3_relat_1(A_74))
      | ~ v1_relat_1(A_74) ) ),
    inference(resolution,[status(thm)],[c_30,c_314])).

tff(c_368,plain,
    ( v6_relat_2('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_242,c_365])).

tff(c_371,plain,(
    v6_relat_2('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_368])).

tff(c_373,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_349,c_371])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:50:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.21  
% 2.20/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.21  %$ r8_relat_2 > r6_relat_2 > r4_relat_2 > r2_wellord1 > r1_wellord1 > r1_relat_2 > v8_relat_2 > v6_relat_2 > v4_relat_2 > v2_wellord1 > v1_wellord1 > v1_relat_2 > v1_relat_1 > #nlpp > k3_relat_1 > #skF_1
% 2.20/1.21  
% 2.20/1.21  %Foreground sorts:
% 2.20/1.21  
% 2.20/1.21  
% 2.20/1.21  %Background operators:
% 2.20/1.21  
% 2.20/1.21  
% 2.20/1.21  %Foreground operators:
% 2.20/1.21  tff(r4_relat_2, type, r4_relat_2: ($i * $i) > $o).
% 2.20/1.21  tff(r1_wellord1, type, r1_wellord1: ($i * $i) > $o).
% 2.20/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.21  tff(v1_relat_2, type, v1_relat_2: $i > $o).
% 2.20/1.21  tff(r6_relat_2, type, r6_relat_2: ($i * $i) > $o).
% 2.20/1.21  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 2.20/1.21  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.20/1.21  tff(v6_relat_2, type, v6_relat_2: $i > $o).
% 2.20/1.21  tff(r1_relat_2, type, r1_relat_2: ($i * $i) > $o).
% 2.20/1.21  tff(v4_relat_2, type, v4_relat_2: $i > $o).
% 2.20/1.21  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 2.20/1.21  tff('#skF_1', type, '#skF_1': $i).
% 2.20/1.21  tff(r2_wellord1, type, r2_wellord1: ($i * $i) > $o).
% 2.20/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.20/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.21  tff(r8_relat_2, type, r8_relat_2: ($i * $i) > $o).
% 2.20/1.21  tff(v1_wellord1, type, v1_wellord1: $i > $o).
% 2.20/1.21  
% 2.20/1.23  tff(f_91, negated_conjecture, ~(![A]: (v1_relat_1(A) => (r2_wellord1(A, k3_relat_1(A)) <=> v2_wellord1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_wellord1)).
% 2.20/1.23  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) <=> ((((v1_relat_2(A) & v8_relat_2(A)) & v4_relat_2(A)) & v6_relat_2(A)) & v1_wellord1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_wellord1)).
% 2.20/1.23  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (v1_relat_2(A) <=> r1_relat_2(A, k3_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_relat_2)).
% 2.20/1.23  tff(f_84, axiom, (![A]: (v1_relat_1(A) => (v1_wellord1(A) <=> r1_wellord1(A, k3_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_wellord1)).
% 2.20/1.23  tff(f_31, axiom, (![A]: (v1_relat_1(A) => (v4_relat_2(A) <=> r4_relat_2(A, k3_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_relat_2)).
% 2.20/1.23  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (v6_relat_2(A) <=> r6_relat_2(A, k3_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_2)).
% 2.20/1.23  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (v8_relat_2(A) <=> r8_relat_2(A, k3_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_2)).
% 2.20/1.23  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (![B]: (r2_wellord1(A, B) <=> ((((r1_relat_2(A, B) & r8_relat_2(A, B)) & r4_relat_2(A, B)) & r6_relat_2(A, B)) & r1_wellord1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_wellord1)).
% 2.20/1.23  tff(c_46, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.20/1.23  tff(c_48, plain, (~v2_wellord1('#skF_1') | ~r2_wellord1('#skF_1', k3_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.20/1.23  tff(c_55, plain, (~r2_wellord1('#skF_1', k3_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_48])).
% 2.20/1.23  tff(c_54, plain, (r2_wellord1('#skF_1', k3_relat_1('#skF_1')) | v2_wellord1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.20/1.23  tff(c_61, plain, (v2_wellord1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_55, c_54])).
% 2.20/1.23  tff(c_22, plain, (![A_4]: (v8_relat_2(A_4) | ~v2_wellord1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.20/1.23  tff(c_24, plain, (![A_4]: (v1_relat_2(A_4) | ~v2_wellord1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.20/1.23  tff(c_64, plain, (v1_relat_2('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_61, c_24])).
% 2.20/1.23  tff(c_70, plain, (v1_relat_2('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_64])).
% 2.20/1.23  tff(c_40, plain, (![A_8]: (r1_relat_2(A_8, k3_relat_1(A_8)) | ~v1_relat_2(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.20/1.23  tff(c_18, plain, (![A_4]: (v6_relat_2(A_4) | ~v2_wellord1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.20/1.23  tff(c_16, plain, (![A_4]: (v1_wellord1(A_4) | ~v2_wellord1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.20/1.23  tff(c_67, plain, (v1_wellord1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_61, c_16])).
% 2.20/1.23  tff(c_73, plain, (v1_wellord1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_67])).
% 2.20/1.23  tff(c_44, plain, (![A_9]: (r1_wellord1(A_9, k3_relat_1(A_9)) | ~v1_wellord1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.20/1.23  tff(c_20, plain, (![A_4]: (v4_relat_2(A_4) | ~v2_wellord1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.20/1.23  tff(c_4, plain, (![A_1]: (r4_relat_2(A_1, k3_relat_1(A_1)) | ~v4_relat_2(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.20/1.23  tff(c_8, plain, (![A_2]: (r6_relat_2(A_2, k3_relat_1(A_2)) | ~v6_relat_2(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.20/1.23  tff(c_12, plain, (![A_3]: (r8_relat_2(A_3, k3_relat_1(A_3)) | ~v8_relat_2(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.20/1.23  tff(c_132, plain, (![A_39, B_40]: (r2_wellord1(A_39, B_40) | ~r1_wellord1(A_39, B_40) | ~r6_relat_2(A_39, B_40) | ~r4_relat_2(A_39, B_40) | ~r8_relat_2(A_39, B_40) | ~r1_relat_2(A_39, B_40) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.20/1.23  tff(c_141, plain, (![A_41]: (r2_wellord1(A_41, k3_relat_1(A_41)) | ~r1_wellord1(A_41, k3_relat_1(A_41)) | ~r6_relat_2(A_41, k3_relat_1(A_41)) | ~r4_relat_2(A_41, k3_relat_1(A_41)) | ~r1_relat_2(A_41, k3_relat_1(A_41)) | ~v8_relat_2(A_41) | ~v1_relat_1(A_41))), inference(resolution, [status(thm)], [c_12, c_132])).
% 2.20/1.23  tff(c_151, plain, (![A_42]: (r2_wellord1(A_42, k3_relat_1(A_42)) | ~r1_wellord1(A_42, k3_relat_1(A_42)) | ~r4_relat_2(A_42, k3_relat_1(A_42)) | ~r1_relat_2(A_42, k3_relat_1(A_42)) | ~v8_relat_2(A_42) | ~v6_relat_2(A_42) | ~v1_relat_1(A_42))), inference(resolution, [status(thm)], [c_8, c_141])).
% 2.20/1.23  tff(c_161, plain, (![A_43]: (r2_wellord1(A_43, k3_relat_1(A_43)) | ~r1_wellord1(A_43, k3_relat_1(A_43)) | ~r1_relat_2(A_43, k3_relat_1(A_43)) | ~v8_relat_2(A_43) | ~v6_relat_2(A_43) | ~v4_relat_2(A_43) | ~v1_relat_1(A_43))), inference(resolution, [status(thm)], [c_4, c_151])).
% 2.20/1.23  tff(c_179, plain, (~r1_wellord1('#skF_1', k3_relat_1('#skF_1')) | ~r1_relat_2('#skF_1', k3_relat_1('#skF_1')) | ~v8_relat_2('#skF_1') | ~v6_relat_2('#skF_1') | ~v4_relat_2('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_161, c_55])).
% 2.20/1.23  tff(c_187, plain, (~r1_wellord1('#skF_1', k3_relat_1('#skF_1')) | ~r1_relat_2('#skF_1', k3_relat_1('#skF_1')) | ~v8_relat_2('#skF_1') | ~v6_relat_2('#skF_1') | ~v4_relat_2('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_179])).
% 2.20/1.23  tff(c_188, plain, (~v4_relat_2('#skF_1')), inference(splitLeft, [status(thm)], [c_187])).
% 2.20/1.23  tff(c_191, plain, (~v2_wellord1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_20, c_188])).
% 2.20/1.23  tff(c_195, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_61, c_191])).
% 2.20/1.23  tff(c_196, plain, (~v6_relat_2('#skF_1') | ~v8_relat_2('#skF_1') | ~r1_relat_2('#skF_1', k3_relat_1('#skF_1')) | ~r1_wellord1('#skF_1', k3_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_187])).
% 2.20/1.23  tff(c_198, plain, (~r1_wellord1('#skF_1', k3_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_196])).
% 2.20/1.23  tff(c_201, plain, (~v1_wellord1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_44, c_198])).
% 2.20/1.23  tff(c_205, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_73, c_201])).
% 2.20/1.23  tff(c_206, plain, (~r1_relat_2('#skF_1', k3_relat_1('#skF_1')) | ~v8_relat_2('#skF_1') | ~v6_relat_2('#skF_1')), inference(splitRight, [status(thm)], [c_196])).
% 2.20/1.23  tff(c_214, plain, (~v6_relat_2('#skF_1')), inference(splitLeft, [status(thm)], [c_206])).
% 2.20/1.23  tff(c_217, plain, (~v2_wellord1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_18, c_214])).
% 2.20/1.23  tff(c_221, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_61, c_217])).
% 2.20/1.23  tff(c_222, plain, (~v8_relat_2('#skF_1') | ~r1_relat_2('#skF_1', k3_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_206])).
% 2.20/1.23  tff(c_224, plain, (~r1_relat_2('#skF_1', k3_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_222])).
% 2.20/1.23  tff(c_227, plain, (~v1_relat_2('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_40, c_224])).
% 2.20/1.23  tff(c_231, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_70, c_227])).
% 2.20/1.23  tff(c_232, plain, (~v8_relat_2('#skF_1')), inference(splitRight, [status(thm)], [c_222])).
% 2.20/1.23  tff(c_236, plain, (~v2_wellord1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_22, c_232])).
% 2.20/1.23  tff(c_240, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_61, c_236])).
% 2.20/1.23  tff(c_241, plain, (~v2_wellord1('#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 2.20/1.23  tff(c_242, plain, (r2_wellord1('#skF_1', k3_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_48])).
% 2.20/1.23  tff(c_259, plain, (![A_55, B_56]: (r1_relat_2(A_55, B_56) | ~r2_wellord1(A_55, B_56) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.20/1.23  tff(c_262, plain, (r1_relat_2('#skF_1', k3_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_242, c_259])).
% 2.20/1.23  tff(c_265, plain, (r1_relat_2('#skF_1', k3_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_262])).
% 2.20/1.23  tff(c_268, plain, (![A_60]: (v1_relat_2(A_60) | ~r1_relat_2(A_60, k3_relat_1(A_60)) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.20/1.23  tff(c_271, plain, (v1_relat_2('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_265, c_268])).
% 2.20/1.23  tff(c_274, plain, (v1_relat_2('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_271])).
% 2.20/1.23  tff(c_32, plain, (![A_5, B_7]: (r4_relat_2(A_5, B_7) | ~r2_wellord1(A_5, B_7) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.20/1.23  tff(c_253, plain, (![A_54]: (v4_relat_2(A_54) | ~r4_relat_2(A_54, k3_relat_1(A_54)) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.20/1.23  tff(c_324, plain, (![A_69]: (v4_relat_2(A_69) | ~r2_wellord1(A_69, k3_relat_1(A_69)) | ~v1_relat_1(A_69))), inference(resolution, [status(thm)], [c_32, c_253])).
% 2.20/1.23  tff(c_327, plain, (v4_relat_2('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_242, c_324])).
% 2.20/1.23  tff(c_330, plain, (v4_relat_2('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_327])).
% 2.20/1.23  tff(c_301, plain, (![A_66, B_67]: (r1_wellord1(A_66, B_67) | ~r2_wellord1(A_66, B_67) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.20/1.23  tff(c_304, plain, (r1_wellord1('#skF_1', k3_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_242, c_301])).
% 2.20/1.23  tff(c_307, plain, (r1_wellord1('#skF_1', k3_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_304])).
% 2.20/1.23  tff(c_42, plain, (![A_9]: (v1_wellord1(A_9) | ~r1_wellord1(A_9, k3_relat_1(A_9)) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.20/1.23  tff(c_310, plain, (v1_wellord1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_307, c_42])).
% 2.20/1.23  tff(c_313, plain, (v1_wellord1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_310])).
% 2.20/1.23  tff(c_34, plain, (![A_5, B_7]: (r8_relat_2(A_5, B_7) | ~r2_wellord1(A_5, B_7) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.20/1.23  tff(c_286, plain, (![A_64]: (v8_relat_2(A_64) | ~r8_relat_2(A_64, k3_relat_1(A_64)) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.20/1.23  tff(c_336, plain, (![A_71]: (v8_relat_2(A_71) | ~r2_wellord1(A_71, k3_relat_1(A_71)) | ~v1_relat_1(A_71))), inference(resolution, [status(thm)], [c_34, c_286])).
% 2.20/1.23  tff(c_339, plain, (v8_relat_2('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_242, c_336])).
% 2.20/1.23  tff(c_342, plain, (v8_relat_2('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_339])).
% 2.20/1.23  tff(c_14, plain, (![A_4]: (v2_wellord1(A_4) | ~v1_wellord1(A_4) | ~v6_relat_2(A_4) | ~v4_relat_2(A_4) | ~v8_relat_2(A_4) | ~v1_relat_2(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.20/1.23  tff(c_345, plain, (v2_wellord1('#skF_1') | ~v1_wellord1('#skF_1') | ~v6_relat_2('#skF_1') | ~v4_relat_2('#skF_1') | ~v1_relat_2('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_342, c_14])).
% 2.20/1.23  tff(c_348, plain, (v2_wellord1('#skF_1') | ~v6_relat_2('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_274, c_330, c_313, c_345])).
% 2.20/1.23  tff(c_349, plain, (~v6_relat_2('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_241, c_348])).
% 2.20/1.23  tff(c_30, plain, (![A_5, B_7]: (r6_relat_2(A_5, B_7) | ~r2_wellord1(A_5, B_7) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.20/1.23  tff(c_314, plain, (![A_68]: (v6_relat_2(A_68) | ~r6_relat_2(A_68, k3_relat_1(A_68)) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.20/1.23  tff(c_365, plain, (![A_74]: (v6_relat_2(A_74) | ~r2_wellord1(A_74, k3_relat_1(A_74)) | ~v1_relat_1(A_74))), inference(resolution, [status(thm)], [c_30, c_314])).
% 2.20/1.23  tff(c_368, plain, (v6_relat_2('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_242, c_365])).
% 2.20/1.23  tff(c_371, plain, (v6_relat_2('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_368])).
% 2.20/1.23  tff(c_373, plain, $false, inference(negUnitSimplification, [status(thm)], [c_349, c_371])).
% 2.20/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.23  
% 2.20/1.23  Inference rules
% 2.20/1.23  ----------------------
% 2.20/1.23  #Ref     : 0
% 2.20/1.23  #Sup     : 49
% 2.20/1.23  #Fact    : 0
% 2.20/1.23  #Define  : 0
% 2.20/1.23  #Split   : 5
% 2.20/1.23  #Chain   : 0
% 2.20/1.23  #Close   : 0
% 2.20/1.23  
% 2.20/1.23  Ordering : KBO
% 2.20/1.23  
% 2.20/1.23  Simplification rules
% 2.20/1.23  ----------------------
% 2.20/1.23  #Subsume      : 1
% 2.20/1.23  #Demod        : 28
% 2.20/1.23  #Tautology    : 25
% 2.20/1.23  #SimpNegUnit  : 4
% 2.20/1.23  #BackRed      : 0
% 2.20/1.23  
% 2.20/1.23  #Partial instantiations: 0
% 2.20/1.23  #Strategies tried      : 1
% 2.20/1.23  
% 2.20/1.23  Timing (in seconds)
% 2.20/1.23  ----------------------
% 2.20/1.23  Preprocessing        : 0.28
% 2.20/1.23  Parsing              : 0.16
% 2.20/1.23  CNF conversion       : 0.02
% 2.20/1.23  Main loop            : 0.24
% 2.20/1.23  Inferencing          : 0.11
% 2.20/1.23  Reduction            : 0.06
% 2.20/1.23  Demodulation         : 0.04
% 2.20/1.23  BG Simplification    : 0.02
% 2.20/1.23  Subsumption          : 0.04
% 2.20/1.23  Abstraction          : 0.01
% 2.46/1.23  MUC search           : 0.00
% 2.46/1.23  Cooper               : 0.00
% 2.46/1.23  Total                : 0.57
% 2.46/1.23  Index Insertion      : 0.00
% 2.46/1.23  Index Deletion       : 0.00
% 2.46/1.23  Index Matching       : 0.00
% 2.46/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
