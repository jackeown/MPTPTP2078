%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:29 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 148 expanded)
%              Number of leaves         :   29 (  60 expanded)
%              Depth                    :    8
%              Number of atoms          :  114 ( 240 expanded)
%              Number of equality atoms :   45 (  81 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_61,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B,C,D] :
            ( ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
              | r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(D,C)) )
           => r1_tarski(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_zfmisc_1)).

tff(f_63,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
     => ( k2_zfmisc_1(A,B) = k1_xboole_0
        | ( r1_tarski(A,C)
          & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_22,plain,(
    ! [A_19] : k3_xboole_0(A_19,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_xboole_0(A_5,B_6)
      | k3_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_24,plain,(
    ! [A_20] : k5_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_522,plain,(
    ! [A_101,B_102] : k5_xboole_0(A_101,k3_xboole_0(A_101,B_102)) = k4_xboole_0(A_101,B_102) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_531,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = k4_xboole_0(A_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_522])).

tff(c_534,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_531])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | k4_xboole_0(A_12,B_13) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_580,plain,(
    ! [A_112,B_113,C_114] :
      ( r1_tarski(A_112,B_113)
      | ~ r1_tarski(A_112,k3_xboole_0(B_113,C_114)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_589,plain,(
    ! [A_115,A_116] :
      ( r1_tarski(A_115,A_116)
      | ~ r1_tarski(A_115,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_580])).

tff(c_592,plain,(
    ! [A_12,A_116] :
      ( r1_tarski(A_12,A_116)
      | k4_xboole_0(A_12,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_589])).

tff(c_596,plain,(
    ! [A_117,A_118] :
      ( r1_tarski(A_117,A_118)
      | k1_xboole_0 != A_117 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_534,c_592])).

tff(c_36,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_617,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_596,c_36])).

tff(c_117,plain,(
    ! [A_47,B_48] : k5_xboole_0(A_47,k3_xboole_0(A_47,B_48)) = k4_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_126,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = k4_xboole_0(A_19,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_117])).

tff(c_129,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_126])).

tff(c_139,plain,(
    ! [A_50,B_51,C_52] :
      ( r1_tarski(A_50,B_51)
      | ~ r1_tarski(A_50,k3_xboole_0(B_51,C_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_152,plain,(
    ! [A_53,A_54] :
      ( r1_tarski(A_53,A_54)
      | ~ r1_tarski(A_53,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_139])).

tff(c_155,plain,(
    ! [A_12,A_54] :
      ( r1_tarski(A_12,A_54)
      | k4_xboole_0(A_12,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_152])).

tff(c_159,plain,(
    ! [A_55,A_56] :
      ( r1_tarski(A_55,A_56)
      | k1_xboole_0 != A_55 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_155])).

tff(c_176,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_159,c_36])).

tff(c_38,plain,
    ( r1_tarski(k2_zfmisc_1('#skF_4','#skF_3'),k2_zfmisc_1('#skF_6','#skF_5'))
    | r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_86,plain,(
    r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_234,plain,(
    ! [A_65,C_66,B_67,D_68] :
      ( r1_tarski(A_65,C_66)
      | k2_zfmisc_1(A_65,B_67) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_65,B_67),k2_zfmisc_1(C_66,D_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_257,plain,
    ( r1_tarski('#skF_3','#skF_5')
    | k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_86,c_234])).

tff(c_284,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_257])).

tff(c_26,plain,(
    ! [B_22,A_21] :
      ( k1_xboole_0 = B_22
      | k1_xboole_0 = A_21
      | k2_zfmisc_1(A_21,B_22) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_298,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_26])).

tff(c_305,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_298])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_206,plain,(
    ! [A_59,B_60,C_61] :
      ( ~ r1_xboole_0(A_59,B_60)
      | ~ r2_hidden(C_61,k3_xboole_0(A_59,B_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_213,plain,(
    ! [A_19,C_61] :
      ( ~ r1_xboole_0(A_19,k1_xboole_0)
      | ~ r2_hidden(C_61,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_206])).

tff(c_228,plain,(
    ! [C_64] : ~ r2_hidden(C_64,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_213])).

tff(c_233,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_228])).

tff(c_344,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_233])).

tff(c_362,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_344])).

tff(c_364,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_257])).

tff(c_431,plain,(
    ! [B_86,D_87,A_88,C_89] :
      ( r1_tarski(B_86,D_87)
      | k2_zfmisc_1(A_88,B_86) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_88,B_86),k2_zfmisc_1(C_89,D_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_437,plain,
    ( r1_tarski('#skF_4','#skF_6')
    | k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_86,c_431])).

tff(c_457,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_364,c_36,c_437])).

tff(c_488,plain,(
    ! [A_94] : ~ r1_xboole_0(A_94,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_213])).

tff(c_492,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_488])).

tff(c_496,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_492])).

tff(c_497,plain,(
    r1_tarski(k2_zfmisc_1('#skF_4','#skF_3'),k2_zfmisc_1('#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_690,plain,(
    ! [A_129,C_130,B_131,D_132] :
      ( r1_tarski(A_129,C_130)
      | k2_zfmisc_1(A_129,B_131) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_129,B_131),k2_zfmisc_1(C_130,D_132)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_696,plain,
    ( r1_tarski('#skF_4','#skF_6')
    | k2_zfmisc_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_497,c_690])).

tff(c_715,plain,(
    k2_zfmisc_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_696])).

tff(c_734,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_715,c_26])).

tff(c_741,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_617,c_734])).

tff(c_555,plain,(
    ! [A_106,B_107,C_108] :
      ( ~ r1_xboole_0(A_106,B_107)
      | ~ r2_hidden(C_108,k3_xboole_0(A_106,B_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_562,plain,(
    ! [A_19,C_108] :
      ( ~ r1_xboole_0(A_19,k1_xboole_0)
      | ~ r2_hidden(C_108,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_555])).

tff(c_565,plain,(
    ! [C_109] : ~ r2_hidden(C_109,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_562])).

tff(c_570,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_565])).

tff(c_787,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_741,c_570])).

tff(c_801,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_787])).

tff(c_803,plain,(
    ! [A_137] : ~ r1_xboole_0(A_137,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_562])).

tff(c_807,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_803])).

tff(c_811,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_807])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:06:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.42  
% 2.71/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.42  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 2.71/1.42  
% 2.71/1.42  %Foreground sorts:
% 2.71/1.42  
% 2.71/1.42  
% 2.71/1.42  %Background operators:
% 2.71/1.42  
% 2.71/1.42  
% 2.71/1.42  %Foreground operators:
% 2.71/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.71/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.71/1.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.71/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.71/1.42  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.71/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.71/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.71/1.42  tff('#skF_6', type, '#skF_6': $i).
% 2.71/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.71/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.71/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.71/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.71/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.71/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.71/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.71/1.42  
% 2.97/1.44  tff(f_61, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.97/1.44  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.97/1.44  tff(f_88, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B, C, D]: ((r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) | r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(D, C))) => r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_zfmisc_1)).
% 2.97/1.44  tff(f_63, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.97/1.44  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.97/1.44  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.97/1.44  tff(f_59, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 2.97/1.44  tff(f_77, axiom, (![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 2.97/1.44  tff(f_69, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.97/1.44  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.97/1.44  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.97/1.44  tff(c_22, plain, (![A_19]: (k3_xboole_0(A_19, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.97/1.44  tff(c_8, plain, (![A_5, B_6]: (r1_xboole_0(A_5, B_6) | k3_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.97/1.44  tff(c_40, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.97/1.44  tff(c_24, plain, (![A_20]: (k5_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.97/1.44  tff(c_522, plain, (![A_101, B_102]: (k5_xboole_0(A_101, k3_xboole_0(A_101, B_102))=k4_xboole_0(A_101, B_102))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.97/1.44  tff(c_531, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=k4_xboole_0(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_522])).
% 2.97/1.44  tff(c_534, plain, (![A_19]: (k4_xboole_0(A_19, k1_xboole_0)=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_531])).
% 2.97/1.44  tff(c_14, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | k4_xboole_0(A_12, B_13)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.97/1.44  tff(c_580, plain, (![A_112, B_113, C_114]: (r1_tarski(A_112, B_113) | ~r1_tarski(A_112, k3_xboole_0(B_113, C_114)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.97/1.44  tff(c_589, plain, (![A_115, A_116]: (r1_tarski(A_115, A_116) | ~r1_tarski(A_115, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_580])).
% 2.97/1.44  tff(c_592, plain, (![A_12, A_116]: (r1_tarski(A_12, A_116) | k4_xboole_0(A_12, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_589])).
% 2.97/1.44  tff(c_596, plain, (![A_117, A_118]: (r1_tarski(A_117, A_118) | k1_xboole_0!=A_117)), inference(demodulation, [status(thm), theory('equality')], [c_534, c_592])).
% 2.97/1.44  tff(c_36, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.97/1.44  tff(c_617, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_596, c_36])).
% 2.97/1.44  tff(c_117, plain, (![A_47, B_48]: (k5_xboole_0(A_47, k3_xboole_0(A_47, B_48))=k4_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.97/1.44  tff(c_126, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=k4_xboole_0(A_19, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_117])).
% 2.97/1.44  tff(c_129, plain, (![A_19]: (k4_xboole_0(A_19, k1_xboole_0)=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_126])).
% 2.97/1.44  tff(c_139, plain, (![A_50, B_51, C_52]: (r1_tarski(A_50, B_51) | ~r1_tarski(A_50, k3_xboole_0(B_51, C_52)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.97/1.44  tff(c_152, plain, (![A_53, A_54]: (r1_tarski(A_53, A_54) | ~r1_tarski(A_53, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_139])).
% 2.97/1.44  tff(c_155, plain, (![A_12, A_54]: (r1_tarski(A_12, A_54) | k4_xboole_0(A_12, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_152])).
% 2.97/1.44  tff(c_159, plain, (![A_55, A_56]: (r1_tarski(A_55, A_56) | k1_xboole_0!=A_55)), inference(demodulation, [status(thm), theory('equality')], [c_129, c_155])).
% 2.97/1.44  tff(c_176, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_159, c_36])).
% 2.97/1.44  tff(c_38, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_3'), k2_zfmisc_1('#skF_6', '#skF_5')) | r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.97/1.44  tff(c_86, plain, (r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_38])).
% 2.97/1.44  tff(c_234, plain, (![A_65, C_66, B_67, D_68]: (r1_tarski(A_65, C_66) | k2_zfmisc_1(A_65, B_67)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_65, B_67), k2_zfmisc_1(C_66, D_68)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.97/1.44  tff(c_257, plain, (r1_tarski('#skF_3', '#skF_5') | k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_86, c_234])).
% 2.97/1.44  tff(c_284, plain, (k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_257])).
% 2.97/1.44  tff(c_26, plain, (![B_22, A_21]: (k1_xboole_0=B_22 | k1_xboole_0=A_21 | k2_zfmisc_1(A_21, B_22)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.97/1.44  tff(c_298, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_284, c_26])).
% 2.97/1.44  tff(c_305, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_176, c_298])).
% 2.97/1.44  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.97/1.44  tff(c_206, plain, (![A_59, B_60, C_61]: (~r1_xboole_0(A_59, B_60) | ~r2_hidden(C_61, k3_xboole_0(A_59, B_60)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.97/1.44  tff(c_213, plain, (![A_19, C_61]: (~r1_xboole_0(A_19, k1_xboole_0) | ~r2_hidden(C_61, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_206])).
% 2.97/1.44  tff(c_228, plain, (![C_64]: (~r2_hidden(C_64, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_213])).
% 2.97/1.44  tff(c_233, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_228])).
% 2.97/1.44  tff(c_344, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_305, c_233])).
% 2.97/1.44  tff(c_362, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_344])).
% 2.97/1.44  tff(c_364, plain, (k2_zfmisc_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_257])).
% 2.97/1.44  tff(c_431, plain, (![B_86, D_87, A_88, C_89]: (r1_tarski(B_86, D_87) | k2_zfmisc_1(A_88, B_86)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_88, B_86), k2_zfmisc_1(C_89, D_87)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.97/1.44  tff(c_437, plain, (r1_tarski('#skF_4', '#skF_6') | k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_86, c_431])).
% 2.97/1.44  tff(c_457, plain, $false, inference(negUnitSimplification, [status(thm)], [c_364, c_36, c_437])).
% 2.97/1.44  tff(c_488, plain, (![A_94]: (~r1_xboole_0(A_94, k1_xboole_0))), inference(splitRight, [status(thm)], [c_213])).
% 2.97/1.44  tff(c_492, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_488])).
% 2.97/1.44  tff(c_496, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_492])).
% 2.97/1.44  tff(c_497, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_3'), k2_zfmisc_1('#skF_6', '#skF_5'))), inference(splitRight, [status(thm)], [c_38])).
% 2.97/1.44  tff(c_690, plain, (![A_129, C_130, B_131, D_132]: (r1_tarski(A_129, C_130) | k2_zfmisc_1(A_129, B_131)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_129, B_131), k2_zfmisc_1(C_130, D_132)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.97/1.44  tff(c_696, plain, (r1_tarski('#skF_4', '#skF_6') | k2_zfmisc_1('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_497, c_690])).
% 2.97/1.44  tff(c_715, plain, (k2_zfmisc_1('#skF_4', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_36, c_696])).
% 2.97/1.44  tff(c_734, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_715, c_26])).
% 2.97/1.44  tff(c_741, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_617, c_734])).
% 2.97/1.44  tff(c_555, plain, (![A_106, B_107, C_108]: (~r1_xboole_0(A_106, B_107) | ~r2_hidden(C_108, k3_xboole_0(A_106, B_107)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.97/1.44  tff(c_562, plain, (![A_19, C_108]: (~r1_xboole_0(A_19, k1_xboole_0) | ~r2_hidden(C_108, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_555])).
% 2.97/1.44  tff(c_565, plain, (![C_109]: (~r2_hidden(C_109, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_562])).
% 2.97/1.44  tff(c_570, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_565])).
% 2.97/1.44  tff(c_787, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_741, c_570])).
% 2.97/1.44  tff(c_801, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_787])).
% 2.97/1.44  tff(c_803, plain, (![A_137]: (~r1_xboole_0(A_137, k1_xboole_0))), inference(splitRight, [status(thm)], [c_562])).
% 2.97/1.44  tff(c_807, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_803])).
% 2.97/1.44  tff(c_811, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_807])).
% 2.97/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.44  
% 2.97/1.44  Inference rules
% 2.97/1.44  ----------------------
% 2.97/1.44  #Ref     : 0
% 2.97/1.44  #Sup     : 161
% 2.97/1.44  #Fact    : 0
% 2.97/1.44  #Define  : 0
% 2.97/1.44  #Split   : 4
% 2.97/1.44  #Chain   : 0
% 2.97/1.44  #Close   : 0
% 2.97/1.44  
% 2.97/1.44  Ordering : KBO
% 2.97/1.44  
% 2.97/1.44  Simplification rules
% 2.97/1.44  ----------------------
% 2.97/1.44  #Subsume      : 12
% 2.97/1.44  #Demod        : 126
% 2.97/1.44  #Tautology    : 93
% 2.97/1.44  #SimpNegUnit  : 8
% 2.97/1.44  #BackRed      : 49
% 2.97/1.44  
% 2.97/1.44  #Partial instantiations: 0
% 2.97/1.44  #Strategies tried      : 1
% 2.97/1.44  
% 2.97/1.44  Timing (in seconds)
% 2.97/1.44  ----------------------
% 2.97/1.44  Preprocessing        : 0.31
% 2.97/1.45  Parsing              : 0.17
% 2.97/1.45  CNF conversion       : 0.02
% 2.97/1.45  Main loop            : 0.38
% 2.97/1.45  Inferencing          : 0.14
% 2.97/1.45  Reduction            : 0.11
% 2.97/1.45  Demodulation         : 0.08
% 2.97/1.45  BG Simplification    : 0.02
% 2.97/1.45  Subsumption          : 0.07
% 2.97/1.45  Abstraction          : 0.02
% 2.97/1.45  MUC search           : 0.00
% 2.97/1.45  Cooper               : 0.00
% 2.97/1.45  Total                : 0.72
% 2.97/1.45  Index Insertion      : 0.00
% 2.97/1.45  Index Deletion       : 0.00
% 2.97/1.45  Index Matching       : 0.00
% 2.97/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
