%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:09 EST 2020

% Result     : Theorem 12.29s
% Output     : CNFRefutation 12.55s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 198 expanded)
%              Number of leaves         :   34 (  81 expanded)
%              Depth                    :   15
%              Number of atoms          :   69 ( 218 expanded)
%              Number of equality atoms :   28 ( 112 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_69,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_67,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_71,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_73,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_58,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_24,plain,(
    ! [A_16,B_17] : r1_tarski(A_16,k2_xboole_0(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_40,plain,(
    ! [A_44,B_45,C_46] : k2_enumset1(A_44,A_44,B_45,C_46) = k1_enumset1(A_44,B_45,C_46) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_649,plain,(
    ! [D_139,C_140,B_141,A_142] : k2_enumset1(D_139,C_140,B_141,A_142) = k2_enumset1(A_142,B_141,C_140,D_139) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1204,plain,(
    ! [C_165,B_166,A_167] : k2_enumset1(C_165,B_166,A_167,A_167) = k1_enumset1(A_167,B_166,C_165) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_649])).

tff(c_1217,plain,(
    ! [B_166,A_167] : k1_enumset1(B_166,A_167,A_167) = k1_enumset1(A_167,B_166,B_166) ),
    inference(superposition,[status(thm),theory(equality)],[c_1204,c_40])).

tff(c_38,plain,(
    ! [A_42,B_43] : k1_enumset1(A_42,A_42,B_43) = k2_tarski(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_42,plain,(
    ! [A_47,B_48,C_49,D_50] : k3_enumset1(A_47,A_47,B_48,C_49,D_50) = k2_enumset1(A_47,B_48,C_49,D_50) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_44,plain,(
    ! [B_52,E_55,C_53,D_54,A_51] : k4_enumset1(A_51,A_51,B_52,C_53,D_54,E_55) = k3_enumset1(A_51,B_52,C_53,D_54,E_55) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1282,plain,(
    ! [B_180,A_181,C_177,D_178,F_176,E_179] : k2_xboole_0(k3_enumset1(A_181,B_180,C_177,D_178,E_179),k1_tarski(F_176)) = k4_enumset1(A_181,B_180,C_177,D_178,E_179,F_176) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_5475,plain,(
    ! [D_244,F_245,E_248,C_243,A_247,B_246] : r1_tarski(k3_enumset1(A_247,B_246,C_243,D_244,E_248),k4_enumset1(A_247,B_246,C_243,D_244,E_248,F_245)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1282,c_24])).

tff(c_5483,plain,(
    ! [A_47,D_50,F_245,C_49,B_48] : r1_tarski(k2_enumset1(A_47,B_48,C_49,D_50),k4_enumset1(A_47,A_47,B_48,C_49,D_50,F_245)) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_5475])).

tff(c_19477,plain,(
    ! [C_356,B_355,F_354,A_352,D_353] : r1_tarski(k2_enumset1(A_352,B_355,C_356,D_353),k3_enumset1(A_352,B_355,C_356,D_353,F_354)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_5483])).

tff(c_19485,plain,(
    ! [A_47,B_48,C_49,D_50] : r1_tarski(k2_enumset1(A_47,A_47,B_48,C_49),k2_enumset1(A_47,B_48,C_49,D_50)) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_19477])).

tff(c_19498,plain,(
    ! [A_357,B_358,C_359,D_360] : r1_tarski(k1_enumset1(A_357,B_358,C_359),k2_enumset1(A_357,B_358,C_359,D_360)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_19485])).

tff(c_19518,plain,(
    ! [A_44,B_45,C_46] : r1_tarski(k1_enumset1(A_44,A_44,B_45),k1_enumset1(A_44,B_45,C_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_19498])).

tff(c_19525,plain,(
    ! [A_361,B_362,C_363] : r1_tarski(k2_tarski(A_361,B_362),k1_enumset1(A_361,B_362,C_363)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_19518])).

tff(c_19539,plain,(
    ! [B_166,A_167] : r1_tarski(k2_tarski(B_166,A_167),k1_enumset1(A_167,B_166,B_166)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1217,c_19525])).

tff(c_684,plain,(
    ! [C_46,B_45,A_44] : k2_enumset1(C_46,B_45,A_44,A_44) = k1_enumset1(A_44,B_45,C_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_649])).

tff(c_20088,plain,(
    ! [C_376,B_377,A_378] : r1_tarski(k1_enumset1(C_376,B_377,A_378),k1_enumset1(A_378,B_377,C_376)) ),
    inference(superposition,[status(thm),theory(equality)],[c_684,c_19498])).

tff(c_20117,plain,(
    ! [B_379,A_380] : r1_tarski(k1_enumset1(B_379,A_380,A_380),k2_tarski(A_380,B_379)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_20088])).

tff(c_290,plain,(
    ! [A_104,B_105] :
      ( r2_xboole_0(A_104,B_105)
      | B_105 = A_104
      | ~ r1_tarski(A_104,B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_22,plain,(
    ! [B_15,A_14] :
      ( ~ r2_xboole_0(B_15,A_14)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_302,plain,(
    ! [B_105,A_104] :
      ( ~ r1_tarski(B_105,A_104)
      | B_105 = A_104
      | ~ r1_tarski(A_104,B_105) ) ),
    inference(resolution,[status(thm)],[c_290,c_22])).

tff(c_20119,plain,(
    ! [B_379,A_380] :
      ( k1_enumset1(B_379,A_380,A_380) = k2_tarski(A_380,B_379)
      | ~ r1_tarski(k2_tarski(A_380,B_379),k1_enumset1(B_379,A_380,A_380)) ) ),
    inference(resolution,[status(thm)],[c_20117,c_302])).

tff(c_20135,plain,(
    ! [B_379,A_380] : k1_enumset1(B_379,A_380,A_380) = k2_tarski(A_380,B_379) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19539,c_20119])).

tff(c_20184,plain,(
    ! [B_383,A_384] : k2_tarski(B_383,A_384) = k2_tarski(A_384,B_383) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20135,c_20135,c_1217])).

tff(c_50,plain,(
    ! [A_69,B_70] : k3_tarski(k2_tarski(A_69,B_70)) = k2_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_20366,plain,(
    ! [B_389,A_390] : k3_tarski(k2_tarski(B_389,A_390)) = k2_xboole_0(A_390,B_389) ),
    inference(superposition,[status(thm),theory(equality)],[c_20184,c_50])).

tff(c_20372,plain,(
    ! [B_389,A_390] : k2_xboole_0(B_389,A_390) = k2_xboole_0(A_390,B_389) ),
    inference(superposition,[status(thm),theory(equality)],[c_20366,c_50])).

tff(c_60,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_380,plain,(
    ! [B_122,A_123] :
      ( ~ r1_tarski(B_122,A_123)
      | B_122 = A_123
      | ~ r1_tarski(A_123,B_122) ) ),
    inference(resolution,[status(thm)],[c_290,c_22])).

tff(c_393,plain,
    ( k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_60,c_380])).

tff(c_487,plain,(
    ~ r1_tarski('#skF_3',k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_393])).

tff(c_20395,plain,(
    ~ r1_tarski('#skF_3',k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20372,c_487])).

tff(c_20399,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20395])).

tff(c_20400,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_393])).

tff(c_331,plain,(
    ! [A_111,C_112,B_113] :
      ( r2_hidden(A_111,C_112)
      | ~ r1_tarski(k2_tarski(A_111,B_113),C_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_343,plain,(
    ! [A_111,B_113,B_17] : r2_hidden(A_111,k2_xboole_0(k2_tarski(A_111,B_113),B_17)) ),
    inference(resolution,[status(thm)],[c_24,c_331])).

tff(c_20410,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20400,c_343])).

tff(c_20421,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_20410])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % DateTime   : Tue Dec  1 18:37:07 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.29/5.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.29/5.88  
% 12.29/5.88  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.29/5.88  %$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 12.29/5.88  
% 12.29/5.88  %Foreground sorts:
% 12.29/5.88  
% 12.29/5.88  
% 12.29/5.88  %Background operators:
% 12.29/5.88  
% 12.29/5.88  
% 12.29/5.88  %Foreground operators:
% 12.29/5.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.29/5.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.29/5.88  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.29/5.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.29/5.88  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 12.29/5.88  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.29/5.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.29/5.88  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 12.29/5.88  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.29/5.88  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.29/5.88  tff('#skF_2', type, '#skF_2': $i).
% 12.29/5.88  tff('#skF_3', type, '#skF_3': $i).
% 12.29/5.88  tff('#skF_1', type, '#skF_1': $i).
% 12.29/5.88  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 12.29/5.88  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 12.29/5.88  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 12.29/5.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.29/5.88  tff(k3_tarski, type, k3_tarski: $i > $i).
% 12.29/5.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.29/5.88  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.29/5.88  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.29/5.88  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 12.29/5.88  
% 12.55/5.90  tff(f_90, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 12.55/5.90  tff(f_53, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 12.55/5.90  tff(f_69, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 12.55/5.90  tff(f_59, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 12.55/5.90  tff(f_67, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 12.55/5.90  tff(f_71, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 12.55/5.90  tff(f_73, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 12.55/5.90  tff(f_61, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 12.55/5.90  tff(f_34, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 12.55/5.90  tff(f_51, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_xboole_1)).
% 12.55/5.90  tff(f_79, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 12.55/5.90  tff(f_85, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 12.55/5.90  tff(c_58, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 12.55/5.90  tff(c_24, plain, (![A_16, B_17]: (r1_tarski(A_16, k2_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.55/5.90  tff(c_40, plain, (![A_44, B_45, C_46]: (k2_enumset1(A_44, A_44, B_45, C_46)=k1_enumset1(A_44, B_45, C_46))), inference(cnfTransformation, [status(thm)], [f_69])).
% 12.55/5.90  tff(c_649, plain, (![D_139, C_140, B_141, A_142]: (k2_enumset1(D_139, C_140, B_141, A_142)=k2_enumset1(A_142, B_141, C_140, D_139))), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.55/5.90  tff(c_1204, plain, (![C_165, B_166, A_167]: (k2_enumset1(C_165, B_166, A_167, A_167)=k1_enumset1(A_167, B_166, C_165))), inference(superposition, [status(thm), theory('equality')], [c_40, c_649])).
% 12.55/5.90  tff(c_1217, plain, (![B_166, A_167]: (k1_enumset1(B_166, A_167, A_167)=k1_enumset1(A_167, B_166, B_166))), inference(superposition, [status(thm), theory('equality')], [c_1204, c_40])).
% 12.55/5.90  tff(c_38, plain, (![A_42, B_43]: (k1_enumset1(A_42, A_42, B_43)=k2_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_67])).
% 12.55/5.90  tff(c_42, plain, (![A_47, B_48, C_49, D_50]: (k3_enumset1(A_47, A_47, B_48, C_49, D_50)=k2_enumset1(A_47, B_48, C_49, D_50))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.55/5.90  tff(c_44, plain, (![B_52, E_55, C_53, D_54, A_51]: (k4_enumset1(A_51, A_51, B_52, C_53, D_54, E_55)=k3_enumset1(A_51, B_52, C_53, D_54, E_55))), inference(cnfTransformation, [status(thm)], [f_73])).
% 12.55/5.90  tff(c_1282, plain, (![B_180, A_181, C_177, D_178, F_176, E_179]: (k2_xboole_0(k3_enumset1(A_181, B_180, C_177, D_178, E_179), k1_tarski(F_176))=k4_enumset1(A_181, B_180, C_177, D_178, E_179, F_176))), inference(cnfTransformation, [status(thm)], [f_61])).
% 12.55/5.90  tff(c_5475, plain, (![D_244, F_245, E_248, C_243, A_247, B_246]: (r1_tarski(k3_enumset1(A_247, B_246, C_243, D_244, E_248), k4_enumset1(A_247, B_246, C_243, D_244, E_248, F_245)))), inference(superposition, [status(thm), theory('equality')], [c_1282, c_24])).
% 12.55/5.90  tff(c_5483, plain, (![A_47, D_50, F_245, C_49, B_48]: (r1_tarski(k2_enumset1(A_47, B_48, C_49, D_50), k4_enumset1(A_47, A_47, B_48, C_49, D_50, F_245)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_5475])).
% 12.55/5.90  tff(c_19477, plain, (![C_356, B_355, F_354, A_352, D_353]: (r1_tarski(k2_enumset1(A_352, B_355, C_356, D_353), k3_enumset1(A_352, B_355, C_356, D_353, F_354)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_5483])).
% 12.55/5.90  tff(c_19485, plain, (![A_47, B_48, C_49, D_50]: (r1_tarski(k2_enumset1(A_47, A_47, B_48, C_49), k2_enumset1(A_47, B_48, C_49, D_50)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_19477])).
% 12.55/5.90  tff(c_19498, plain, (![A_357, B_358, C_359, D_360]: (r1_tarski(k1_enumset1(A_357, B_358, C_359), k2_enumset1(A_357, B_358, C_359, D_360)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_19485])).
% 12.55/5.90  tff(c_19518, plain, (![A_44, B_45, C_46]: (r1_tarski(k1_enumset1(A_44, A_44, B_45), k1_enumset1(A_44, B_45, C_46)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_19498])).
% 12.55/5.90  tff(c_19525, plain, (![A_361, B_362, C_363]: (r1_tarski(k2_tarski(A_361, B_362), k1_enumset1(A_361, B_362, C_363)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_19518])).
% 12.55/5.90  tff(c_19539, plain, (![B_166, A_167]: (r1_tarski(k2_tarski(B_166, A_167), k1_enumset1(A_167, B_166, B_166)))), inference(superposition, [status(thm), theory('equality')], [c_1217, c_19525])).
% 12.55/5.90  tff(c_684, plain, (![C_46, B_45, A_44]: (k2_enumset1(C_46, B_45, A_44, A_44)=k1_enumset1(A_44, B_45, C_46))), inference(superposition, [status(thm), theory('equality')], [c_40, c_649])).
% 12.55/5.90  tff(c_20088, plain, (![C_376, B_377, A_378]: (r1_tarski(k1_enumset1(C_376, B_377, A_378), k1_enumset1(A_378, B_377, C_376)))), inference(superposition, [status(thm), theory('equality')], [c_684, c_19498])).
% 12.55/5.90  tff(c_20117, plain, (![B_379, A_380]: (r1_tarski(k1_enumset1(B_379, A_380, A_380), k2_tarski(A_380, B_379)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_20088])).
% 12.55/5.90  tff(c_290, plain, (![A_104, B_105]: (r2_xboole_0(A_104, B_105) | B_105=A_104 | ~r1_tarski(A_104, B_105))), inference(cnfTransformation, [status(thm)], [f_34])).
% 12.55/5.90  tff(c_22, plain, (![B_15, A_14]: (~r2_xboole_0(B_15, A_14) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.55/5.90  tff(c_302, plain, (![B_105, A_104]: (~r1_tarski(B_105, A_104) | B_105=A_104 | ~r1_tarski(A_104, B_105))), inference(resolution, [status(thm)], [c_290, c_22])).
% 12.55/5.90  tff(c_20119, plain, (![B_379, A_380]: (k1_enumset1(B_379, A_380, A_380)=k2_tarski(A_380, B_379) | ~r1_tarski(k2_tarski(A_380, B_379), k1_enumset1(B_379, A_380, A_380)))), inference(resolution, [status(thm)], [c_20117, c_302])).
% 12.55/5.90  tff(c_20135, plain, (![B_379, A_380]: (k1_enumset1(B_379, A_380, A_380)=k2_tarski(A_380, B_379))), inference(demodulation, [status(thm), theory('equality')], [c_19539, c_20119])).
% 12.55/5.90  tff(c_20184, plain, (![B_383, A_384]: (k2_tarski(B_383, A_384)=k2_tarski(A_384, B_383))), inference(demodulation, [status(thm), theory('equality')], [c_20135, c_20135, c_1217])).
% 12.55/5.90  tff(c_50, plain, (![A_69, B_70]: (k3_tarski(k2_tarski(A_69, B_70))=k2_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.55/5.90  tff(c_20366, plain, (![B_389, A_390]: (k3_tarski(k2_tarski(B_389, A_390))=k2_xboole_0(A_390, B_389))), inference(superposition, [status(thm), theory('equality')], [c_20184, c_50])).
% 12.55/5.90  tff(c_20372, plain, (![B_389, A_390]: (k2_xboole_0(B_389, A_390)=k2_xboole_0(A_390, B_389))), inference(superposition, [status(thm), theory('equality')], [c_20366, c_50])).
% 12.55/5.90  tff(c_60, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 12.55/5.90  tff(c_380, plain, (![B_122, A_123]: (~r1_tarski(B_122, A_123) | B_122=A_123 | ~r1_tarski(A_123, B_122))), inference(resolution, [status(thm)], [c_290, c_22])).
% 12.55/5.90  tff(c_393, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'))), inference(resolution, [status(thm)], [c_60, c_380])).
% 12.55/5.90  tff(c_487, plain, (~r1_tarski('#skF_3', k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_393])).
% 12.55/5.90  tff(c_20395, plain, (~r1_tarski('#skF_3', k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_20372, c_487])).
% 12.55/5.90  tff(c_20399, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_20395])).
% 12.55/5.90  tff(c_20400, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_393])).
% 12.55/5.90  tff(c_331, plain, (![A_111, C_112, B_113]: (r2_hidden(A_111, C_112) | ~r1_tarski(k2_tarski(A_111, B_113), C_112))), inference(cnfTransformation, [status(thm)], [f_85])).
% 12.55/5.90  tff(c_343, plain, (![A_111, B_113, B_17]: (r2_hidden(A_111, k2_xboole_0(k2_tarski(A_111, B_113), B_17)))), inference(resolution, [status(thm)], [c_24, c_331])).
% 12.55/5.90  tff(c_20410, plain, (r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20400, c_343])).
% 12.55/5.90  tff(c_20421, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_20410])).
% 12.55/5.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.55/5.90  
% 12.55/5.90  Inference rules
% 12.55/5.90  ----------------------
% 12.55/5.90  #Ref     : 0
% 12.55/5.90  #Sup     : 5368
% 12.55/5.90  #Fact    : 0
% 12.55/5.90  #Define  : 0
% 12.55/5.90  #Split   : 1
% 12.55/5.90  #Chain   : 0
% 12.55/5.90  #Close   : 0
% 12.55/5.90  
% 12.55/5.90  Ordering : KBO
% 12.55/5.90  
% 12.55/5.90  Simplification rules
% 12.55/5.90  ----------------------
% 12.55/5.90  #Subsume      : 435
% 12.55/5.90  #Demod        : 6766
% 12.55/5.90  #Tautology    : 1746
% 12.55/5.90  #SimpNegUnit  : 1
% 12.55/5.90  #BackRed      : 9
% 12.55/5.90  
% 12.55/5.90  #Partial instantiations: 0
% 12.55/5.90  #Strategies tried      : 1
% 12.55/5.90  
% 12.55/5.90  Timing (in seconds)
% 12.55/5.90  ----------------------
% 12.55/5.90  Preprocessing        : 0.36
% 12.55/5.90  Parsing              : 0.19
% 12.55/5.90  CNF conversion       : 0.02
% 12.55/5.90  Main loop            : 4.80
% 12.55/5.90  Inferencing          : 0.72
% 12.55/5.90  Reduction            : 3.35
% 12.55/5.90  Demodulation         : 3.16
% 12.55/5.90  BG Simplification    : 0.13
% 12.55/5.90  Subsumption          : 0.47
% 12.55/5.90  Abstraction          : 0.19
% 12.55/5.90  MUC search           : 0.00
% 12.55/5.90  Cooper               : 0.00
% 12.55/5.90  Total                : 5.19
% 12.55/5.90  Index Insertion      : 0.00
% 12.55/5.90  Index Deletion       : 0.00
% 12.55/5.90  Index Matching       : 0.00
% 12.55/5.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
