%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:58 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 194 expanded)
%              Number of leaves         :   28 (  74 expanded)
%              Depth                    :    8
%              Number of atoms          :  110 ( 321 expanded)
%              Number of equality atoms :   44 ( 148 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_40,axiom,(
    ! [A,B,C,D] : k4_enumset1(A,A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C] : k4_enumset1(A,A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_enumset1)).

tff(f_38,axiom,(
    ! [A,B] : k2_enumset1(A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

tff(f_36,axiom,(
    ! [A] : k1_enumset1(A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_55,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
      <=> ( A = C
          & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_522,plain,(
    ! [A_145,B_146,C_147,D_148] : k4_enumset1(A_145,A_145,A_145,B_146,C_147,D_148) = k2_enumset1(A_145,B_146,C_147,D_148) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_26,plain,(
    ! [A_14,B_15,C_16] : k4_enumset1(A_14,A_14,A_14,A_14,B_15,C_16) = k1_enumset1(A_14,B_15,C_16) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_538,plain,(
    ! [B_149,C_150,D_151] : k2_enumset1(B_149,B_149,C_150,D_151) = k1_enumset1(B_149,C_150,D_151) ),
    inference(superposition,[status(thm),theory(equality)],[c_522,c_26])).

tff(c_22,plain,(
    ! [A_8,B_9] : k2_enumset1(A_8,A_8,A_8,B_9) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_554,plain,(
    ! [C_152,D_153] : k1_enumset1(C_152,C_152,D_153) = k2_tarski(C_152,D_153) ),
    inference(superposition,[status(thm),theory(equality)],[c_538,c_22])).

tff(c_20,plain,(
    ! [A_7] : k1_enumset1(A_7,A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_570,plain,(
    ! [D_154] : k2_tarski(D_154,D_154) = k1_tarski(D_154) ),
    inference(superposition,[status(thm),theory(equality)],[c_554,c_20])).

tff(c_4,plain,(
    ! [D_6,A_1] : r2_hidden(D_6,k2_tarski(A_1,D_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_579,plain,(
    ! [D_154] : r2_hidden(D_154,k1_tarski(D_154)) ),
    inference(superposition,[status(thm),theory(equality)],[c_570,c_4])).

tff(c_209,plain,(
    ! [A_66,B_67,C_68,D_69] : k4_enumset1(A_66,A_66,A_66,B_67,C_68,D_69) = k2_enumset1(A_66,B_67,C_68,D_69) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_225,plain,(
    ! [B_70,C_71,D_72] : k2_enumset1(B_70,B_70,C_71,D_72) = k1_enumset1(B_70,C_71,D_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_26])).

tff(c_241,plain,(
    ! [C_73,D_74] : k1_enumset1(C_73,C_73,D_74) = k2_tarski(C_73,D_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_22])).

tff(c_270,plain,(
    ! [D_79] : k2_tarski(D_79,D_79) = k1_tarski(D_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_20])).

tff(c_279,plain,(
    ! [D_79] : r2_hidden(D_79,k1_tarski(D_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_4])).

tff(c_38,plain,
    ( '#skF_5' = '#skF_3'
    | ~ r2_hidden('#skF_8','#skF_10')
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_56,plain,(
    '#skF_7' != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_44,plain,
    ( '#skF_5' = '#skF_3'
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_78,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_32,plain,(
    ! [A_17,C_19,B_18,D_20] :
      ( r2_hidden(A_17,C_19)
      | ~ r2_hidden(k4_tarski(A_17,B_18),k2_zfmisc_1(C_19,D_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_82,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_78,c_32])).

tff(c_98,plain,(
    ! [A_42,B_43,C_44,D_45] : k4_enumset1(A_42,A_42,A_42,B_43,C_44,D_45) = k2_enumset1(A_42,B_43,C_44,D_45) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_114,plain,(
    ! [B_46,C_47,D_48] : k2_enumset1(B_46,B_46,C_47,D_48) = k1_enumset1(B_46,C_47,D_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_26])).

tff(c_130,plain,(
    ! [C_49,D_50] : k1_enumset1(C_49,C_49,D_50) = k2_tarski(C_49,D_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_22])).

tff(c_148,plain,(
    ! [D_51] : k2_tarski(D_51,D_51) = k1_tarski(D_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_20])).

tff(c_2,plain,(
    ! [D_6,B_2,A_1] :
      ( D_6 = B_2
      | D_6 = A_1
      | ~ r2_hidden(D_6,k2_tarski(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_179,plain,(
    ! [D_58,D_57] :
      ( D_58 = D_57
      | D_58 = D_57
      | ~ r2_hidden(D_57,k1_tarski(D_58)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_2])).

tff(c_185,plain,(
    '#skF_7' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_82,c_179])).

tff(c_191,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_56,c_185])).

tff(c_193,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_42,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_198,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_193,c_42])).

tff(c_28,plain,(
    ! [A_17,B_18,C_19,D_20] :
      ( r2_hidden(k4_tarski(A_17,B_18),k2_zfmisc_1(C_19,D_20))
      | ~ r2_hidden(B_18,D_20)
      | ~ r2_hidden(A_17,C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_192,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_40,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6'))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_304,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6'))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_40])).

tff(c_305,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_193,c_304])).

tff(c_308,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_305])).

tff(c_312,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_198,c_308])).

tff(c_314,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_376,plain,(
    ! [A_112,B_113,C_114,D_115] : k4_enumset1(A_112,A_112,A_112,B_113,C_114,D_115) = k2_enumset1(A_112,B_113,C_114,D_115) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_392,plain,(
    ! [B_116,C_117,D_118] : k2_enumset1(B_116,B_116,C_117,D_118) = k1_enumset1(B_116,C_117,D_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_376,c_26])).

tff(c_410,plain,(
    ! [C_119,D_120] : k1_enumset1(C_119,C_119,D_120) = k2_tarski(C_119,D_120) ),
    inference(superposition,[status(thm),theory(equality)],[c_392,c_22])).

tff(c_426,plain,(
    ! [D_121] : k2_tarski(D_121,D_121) = k1_tarski(D_121) ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_20])).

tff(c_435,plain,(
    ! [D_121] : r2_hidden(D_121,k1_tarski(D_121)) ),
    inference(superposition,[status(thm),theory(equality)],[c_426,c_4])).

tff(c_313,plain,
    ( ~ r2_hidden('#skF_8','#skF_10')
    | '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_319,plain,(
    ~ r2_hidden('#skF_8','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_313])).

tff(c_343,plain,
    ( '#skF_5' = '#skF_3'
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_44])).

tff(c_344,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_343])).

tff(c_350,plain,(
    ! [B_101,D_102,A_103,C_104] :
      ( r2_hidden(B_101,D_102)
      | ~ r2_hidden(k4_tarski(A_103,B_101),k2_zfmisc_1(C_104,D_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_353,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_344,c_350])).

tff(c_357,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_319,c_353])).

tff(c_359,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(splitRight,[status(thm)],[c_343])).

tff(c_374,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_42])).

tff(c_375,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_359,c_374])).

tff(c_358,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_343])).

tff(c_470,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6'))
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),'#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_358,c_40])).

tff(c_471,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_359,c_470])).

tff(c_474,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_471])).

tff(c_478,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_375,c_474])).

tff(c_480,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(splitRight,[status(thm)],[c_313])).

tff(c_36,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_8','#skF_10')
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_486,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_480,c_36])).

tff(c_588,plain,(
    ! [A_155,B_156,C_157,D_158] :
      ( r2_hidden(k4_tarski(A_155,B_156),k2_zfmisc_1(C_157,D_158))
      | ~ r2_hidden(B_156,D_158)
      | ~ r2_hidden(A_155,C_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_479,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_313])).

tff(c_34,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6'))
    | ~ r2_hidden('#skF_8','#skF_10')
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_512,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_480,c_479,c_34])).

tff(c_591,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_588,c_512])).

tff(c_600,plain,(
    ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_486,c_591])).

tff(c_605,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_600])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:48:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.30  
% 2.25/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.30  %$ r2_hidden > k4_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_4
% 2.25/1.30  
% 2.25/1.30  %Foreground sorts:
% 2.25/1.30  
% 2.25/1.30  
% 2.25/1.30  %Background operators:
% 2.25/1.30  
% 2.25/1.30  
% 2.25/1.30  %Foreground operators:
% 2.25/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.25/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.25/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.25/1.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.25/1.30  tff('#skF_7', type, '#skF_7': $i).
% 2.25/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.25/1.30  tff('#skF_10', type, '#skF_10': $i).
% 2.25/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.25/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.25/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.25/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.25/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.25/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.25/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.25/1.30  tff('#skF_9', type, '#skF_9': $i).
% 2.25/1.30  tff('#skF_8', type, '#skF_8': $i).
% 2.25/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.25/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.25/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.30  
% 2.25/1.31  tff(f_40, axiom, (![A, B, C, D]: (k4_enumset1(A, A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_enumset1)).
% 2.25/1.31  tff(f_42, axiom, (![A, B, C]: (k4_enumset1(A, A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_enumset1)).
% 2.25/1.31  tff(f_38, axiom, (![A, B]: (k2_enumset1(A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_enumset1)).
% 2.25/1.31  tff(f_36, axiom, (![A]: (k1_enumset1(A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_enumset1)).
% 2.25/1.31  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.25/1.31  tff(f_55, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 2.25/1.31  tff(f_48, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.25/1.31  tff(c_522, plain, (![A_145, B_146, C_147, D_148]: (k4_enumset1(A_145, A_145, A_145, B_146, C_147, D_148)=k2_enumset1(A_145, B_146, C_147, D_148))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.25/1.31  tff(c_26, plain, (![A_14, B_15, C_16]: (k4_enumset1(A_14, A_14, A_14, A_14, B_15, C_16)=k1_enumset1(A_14, B_15, C_16))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.25/1.31  tff(c_538, plain, (![B_149, C_150, D_151]: (k2_enumset1(B_149, B_149, C_150, D_151)=k1_enumset1(B_149, C_150, D_151))), inference(superposition, [status(thm), theory('equality')], [c_522, c_26])).
% 2.25/1.31  tff(c_22, plain, (![A_8, B_9]: (k2_enumset1(A_8, A_8, A_8, B_9)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.25/1.31  tff(c_554, plain, (![C_152, D_153]: (k1_enumset1(C_152, C_152, D_153)=k2_tarski(C_152, D_153))), inference(superposition, [status(thm), theory('equality')], [c_538, c_22])).
% 2.25/1.31  tff(c_20, plain, (![A_7]: (k1_enumset1(A_7, A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.25/1.31  tff(c_570, plain, (![D_154]: (k2_tarski(D_154, D_154)=k1_tarski(D_154))), inference(superposition, [status(thm), theory('equality')], [c_554, c_20])).
% 2.25/1.31  tff(c_4, plain, (![D_6, A_1]: (r2_hidden(D_6, k2_tarski(A_1, D_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.25/1.31  tff(c_579, plain, (![D_154]: (r2_hidden(D_154, k1_tarski(D_154)))), inference(superposition, [status(thm), theory('equality')], [c_570, c_4])).
% 2.25/1.31  tff(c_209, plain, (![A_66, B_67, C_68, D_69]: (k4_enumset1(A_66, A_66, A_66, B_67, C_68, D_69)=k2_enumset1(A_66, B_67, C_68, D_69))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.25/1.31  tff(c_225, plain, (![B_70, C_71, D_72]: (k2_enumset1(B_70, B_70, C_71, D_72)=k1_enumset1(B_70, C_71, D_72))), inference(superposition, [status(thm), theory('equality')], [c_209, c_26])).
% 2.25/1.31  tff(c_241, plain, (![C_73, D_74]: (k1_enumset1(C_73, C_73, D_74)=k2_tarski(C_73, D_74))), inference(superposition, [status(thm), theory('equality')], [c_225, c_22])).
% 2.25/1.31  tff(c_270, plain, (![D_79]: (k2_tarski(D_79, D_79)=k1_tarski(D_79))), inference(superposition, [status(thm), theory('equality')], [c_241, c_20])).
% 2.25/1.31  tff(c_279, plain, (![D_79]: (r2_hidden(D_79, k1_tarski(D_79)))), inference(superposition, [status(thm), theory('equality')], [c_270, c_4])).
% 2.25/1.31  tff(c_38, plain, ('#skF_5'='#skF_3' | ~r2_hidden('#skF_8', '#skF_10') | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.25/1.31  tff(c_56, plain, ('#skF_7'!='#skF_9'), inference(splitLeft, [status(thm)], [c_38])).
% 2.25/1.31  tff(c_44, plain, ('#skF_5'='#skF_3' | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.25/1.31  tff(c_78, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(splitLeft, [status(thm)], [c_44])).
% 2.25/1.31  tff(c_32, plain, (![A_17, C_19, B_18, D_20]: (r2_hidden(A_17, C_19) | ~r2_hidden(k4_tarski(A_17, B_18), k2_zfmisc_1(C_19, D_20)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.25/1.31  tff(c_82, plain, (r2_hidden('#skF_7', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_78, c_32])).
% 2.25/1.31  tff(c_98, plain, (![A_42, B_43, C_44, D_45]: (k4_enumset1(A_42, A_42, A_42, B_43, C_44, D_45)=k2_enumset1(A_42, B_43, C_44, D_45))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.25/1.31  tff(c_114, plain, (![B_46, C_47, D_48]: (k2_enumset1(B_46, B_46, C_47, D_48)=k1_enumset1(B_46, C_47, D_48))), inference(superposition, [status(thm), theory('equality')], [c_98, c_26])).
% 2.25/1.31  tff(c_130, plain, (![C_49, D_50]: (k1_enumset1(C_49, C_49, D_50)=k2_tarski(C_49, D_50))), inference(superposition, [status(thm), theory('equality')], [c_114, c_22])).
% 2.25/1.31  tff(c_148, plain, (![D_51]: (k2_tarski(D_51, D_51)=k1_tarski(D_51))), inference(superposition, [status(thm), theory('equality')], [c_130, c_20])).
% 2.25/1.31  tff(c_2, plain, (![D_6, B_2, A_1]: (D_6=B_2 | D_6=A_1 | ~r2_hidden(D_6, k2_tarski(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.25/1.31  tff(c_179, plain, (![D_58, D_57]: (D_58=D_57 | D_58=D_57 | ~r2_hidden(D_57, k1_tarski(D_58)))), inference(superposition, [status(thm), theory('equality')], [c_148, c_2])).
% 2.25/1.31  tff(c_185, plain, ('#skF_7'='#skF_9'), inference(resolution, [status(thm)], [c_82, c_179])).
% 2.25/1.31  tff(c_191, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_56, c_185])).
% 2.25/1.31  tff(c_193, plain, (~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(splitRight, [status(thm)], [c_44])).
% 2.25/1.31  tff(c_42, plain, (r2_hidden('#skF_4', '#skF_6') | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.25/1.31  tff(c_198, plain, (r2_hidden('#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_193, c_42])).
% 2.25/1.31  tff(c_28, plain, (![A_17, B_18, C_19, D_20]: (r2_hidden(k4_tarski(A_17, B_18), k2_zfmisc_1(C_19, D_20)) | ~r2_hidden(B_18, D_20) | ~r2_hidden(A_17, C_19))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.25/1.31  tff(c_192, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_44])).
% 2.25/1.31  tff(c_40, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6')) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.25/1.31  tff(c_304, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_6')) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_192, c_40])).
% 2.25/1.31  tff(c_305, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_193, c_304])).
% 2.25/1.31  tff(c_308, plain, (~r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_305])).
% 2.25/1.31  tff(c_312, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_279, c_198, c_308])).
% 2.25/1.31  tff(c_314, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_38])).
% 2.25/1.31  tff(c_376, plain, (![A_112, B_113, C_114, D_115]: (k4_enumset1(A_112, A_112, A_112, B_113, C_114, D_115)=k2_enumset1(A_112, B_113, C_114, D_115))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.25/1.31  tff(c_392, plain, (![B_116, C_117, D_118]: (k2_enumset1(B_116, B_116, C_117, D_118)=k1_enumset1(B_116, C_117, D_118))), inference(superposition, [status(thm), theory('equality')], [c_376, c_26])).
% 2.25/1.31  tff(c_410, plain, (![C_119, D_120]: (k1_enumset1(C_119, C_119, D_120)=k2_tarski(C_119, D_120))), inference(superposition, [status(thm), theory('equality')], [c_392, c_22])).
% 2.25/1.31  tff(c_426, plain, (![D_121]: (k2_tarski(D_121, D_121)=k1_tarski(D_121))), inference(superposition, [status(thm), theory('equality')], [c_410, c_20])).
% 2.25/1.31  tff(c_435, plain, (![D_121]: (r2_hidden(D_121, k1_tarski(D_121)))), inference(superposition, [status(thm), theory('equality')], [c_426, c_4])).
% 2.25/1.31  tff(c_313, plain, (~r2_hidden('#skF_8', '#skF_10') | '#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_38])).
% 2.25/1.31  tff(c_319, plain, (~r2_hidden('#skF_8', '#skF_10')), inference(splitLeft, [status(thm)], [c_313])).
% 2.25/1.31  tff(c_343, plain, ('#skF_5'='#skF_3' | r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_314, c_44])).
% 2.25/1.31  tff(c_344, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(splitLeft, [status(thm)], [c_343])).
% 2.25/1.31  tff(c_350, plain, (![B_101, D_102, A_103, C_104]: (r2_hidden(B_101, D_102) | ~r2_hidden(k4_tarski(A_103, B_101), k2_zfmisc_1(C_104, D_102)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.25/1.31  tff(c_353, plain, (r2_hidden('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_344, c_350])).
% 2.25/1.31  tff(c_357, plain, $false, inference(negUnitSimplification, [status(thm)], [c_319, c_353])).
% 2.25/1.31  tff(c_359, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(splitRight, [status(thm)], [c_343])).
% 2.25/1.32  tff(c_374, plain, (r2_hidden('#skF_4', '#skF_6') | r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_314, c_42])).
% 2.25/1.32  tff(c_375, plain, (r2_hidden('#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_359, c_374])).
% 2.25/1.32  tff(c_358, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_343])).
% 2.25/1.32  tff(c_470, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_6')) | r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_314, c_358, c_40])).
% 2.25/1.32  tff(c_471, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_359, c_470])).
% 2.25/1.32  tff(c_474, plain, (~r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_471])).
% 2.25/1.32  tff(c_478, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_435, c_375, c_474])).
% 2.25/1.32  tff(c_480, plain, (r2_hidden('#skF_8', '#skF_10')), inference(splitRight, [status(thm)], [c_313])).
% 2.25/1.32  tff(c_36, plain, (r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_8', '#skF_10') | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.25/1.32  tff(c_486, plain, (r2_hidden('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_314, c_480, c_36])).
% 2.25/1.32  tff(c_588, plain, (![A_155, B_156, C_157, D_158]: (r2_hidden(k4_tarski(A_155, B_156), k2_zfmisc_1(C_157, D_158)) | ~r2_hidden(B_156, D_158) | ~r2_hidden(A_155, C_157))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.25/1.32  tff(c_479, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_313])).
% 2.25/1.32  tff(c_34, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6')) | ~r2_hidden('#skF_8', '#skF_10') | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.25/1.32  tff(c_512, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_314, c_480, c_479, c_34])).
% 2.25/1.32  tff(c_591, plain, (~r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_588, c_512])).
% 2.25/1.32  tff(c_600, plain, (~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_486, c_591])).
% 2.25/1.32  tff(c_605, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_579, c_600])).
% 2.25/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.32  
% 2.25/1.32  Inference rules
% 2.25/1.32  ----------------------
% 2.25/1.32  #Ref     : 0
% 2.25/1.32  #Sup     : 119
% 2.25/1.32  #Fact    : 0
% 2.25/1.32  #Define  : 0
% 2.25/1.32  #Split   : 5
% 2.25/1.32  #Chain   : 0
% 2.25/1.32  #Close   : 0
% 2.25/1.32  
% 2.25/1.32  Ordering : KBO
% 2.25/1.32  
% 2.25/1.32  Simplification rules
% 2.25/1.32  ----------------------
% 2.25/1.32  #Subsume      : 6
% 2.25/1.32  #Demod        : 40
% 2.25/1.32  #Tautology    : 88
% 2.25/1.32  #SimpNegUnit  : 6
% 2.25/1.32  #BackRed      : 1
% 2.25/1.32  
% 2.25/1.32  #Partial instantiations: 0
% 2.25/1.32  #Strategies tried      : 1
% 2.25/1.32  
% 2.25/1.32  Timing (in seconds)
% 2.25/1.32  ----------------------
% 2.25/1.32  Preprocessing        : 0.29
% 2.25/1.32  Parsing              : 0.15
% 2.25/1.32  CNF conversion       : 0.02
% 2.25/1.32  Main loop            : 0.26
% 2.25/1.32  Inferencing          : 0.10
% 2.25/1.32  Reduction            : 0.08
% 2.25/1.32  Demodulation         : 0.06
% 2.25/1.32  BG Simplification    : 0.02
% 2.25/1.32  Subsumption          : 0.04
% 2.25/1.32  Abstraction          : 0.01
% 2.25/1.32  MUC search           : 0.00
% 2.25/1.32  Cooper               : 0.00
% 2.25/1.32  Total                : 0.59
% 2.25/1.32  Index Insertion      : 0.00
% 2.25/1.32  Index Deletion       : 0.00
% 2.25/1.32  Index Matching       : 0.00
% 2.25/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
