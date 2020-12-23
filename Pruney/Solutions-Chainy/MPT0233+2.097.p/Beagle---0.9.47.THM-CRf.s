%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:33 EST 2020

% Result     : Theorem 8.88s
% Output     : CNFRefutation 9.05s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 134 expanded)
%              Number of leaves         :   43 (  63 expanded)
%              Depth                    :   14
%              Number of atoms          :   89 ( 142 expanded)
%              Number of equality atoms :   61 (  97 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_6 > #skF_7 > #skF_10 > #skF_5 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_123,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_59,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_67,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_71,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_65,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_113,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_109,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_107,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_103,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_88,plain,(
    '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_86,plain,(
    '#skF_7' != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_16,plain,(
    ! [A_17] : k2_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_22,plain,(
    ! [A_21,B_22] : r1_tarski(k4_xboole_0(A_21,B_22),A_21) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_121,plain,(
    ! [A_65] :
      ( k1_xboole_0 = A_65
      | ~ r1_tarski(A_65,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_130,plain,(
    ! [B_22] : k4_xboole_0(k1_xboole_0,B_22) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_121])).

tff(c_725,plain,(
    ! [A_115,B_116] : k5_xboole_0(A_115,k4_xboole_0(B_116,A_115)) = k2_xboole_0(A_115,B_116) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_737,plain,(
    ! [B_22] : k5_xboole_0(B_22,k1_xboole_0) = k2_xboole_0(B_22,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_725])).

tff(c_740,plain,(
    ! [B_22] : k5_xboole_0(B_22,k1_xboole_0) = B_22 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_737])).

tff(c_20,plain,(
    ! [A_20] : r1_tarski(k1_xboole_0,A_20) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_217,plain,(
    ! [A_89,B_90] :
      ( k3_xboole_0(A_89,B_90) = A_89
      | ~ r1_tarski(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_239,plain,(
    ! [A_91] : k3_xboole_0(k1_xboole_0,A_91) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_217])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_244,plain,(
    ! [A_91] : k3_xboole_0(A_91,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_2])).

tff(c_445,plain,(
    ! [A_100,B_101] : k5_xboole_0(A_100,k3_xboole_0(A_100,B_101)) = k4_xboole_0(A_100,B_101) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_457,plain,(
    ! [A_91] : k5_xboole_0(A_91,k1_xboole_0) = k4_xboole_0(A_91,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_445])).

tff(c_762,plain,(
    ! [A_118] : k4_xboole_0(A_118,k1_xboole_0) = A_118 ),
    inference(demodulation,[status(thm),theory(equality)],[c_740,c_457])).

tff(c_26,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k4_xboole_0(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_775,plain,(
    ! [A_118] : k4_xboole_0(A_118,A_118) = k3_xboole_0(A_118,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_762,c_26])).

tff(c_792,plain,(
    ! [A_118] : k4_xboole_0(A_118,A_118) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_775])).

tff(c_84,plain,(
    ! [A_56,B_57] : r1_tarski(k1_tarski(A_56),k2_tarski(A_56,B_57)) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_90,plain,(
    r1_tarski(k2_tarski('#skF_7','#skF_8'),k2_tarski('#skF_9','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_236,plain,(
    k3_xboole_0(k2_tarski('#skF_7','#skF_8'),k2_tarski('#skF_9','#skF_10')) = k2_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_90,c_217])).

tff(c_536,plain,(
    ! [A_104,B_105,C_106] :
      ( r1_tarski(A_104,B_105)
      | ~ r1_tarski(A_104,k3_xboole_0(B_105,C_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2087,plain,(
    ! [A_182,B_183,A_184] :
      ( r1_tarski(A_182,B_183)
      | ~ r1_tarski(A_182,k3_xboole_0(A_184,B_183)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_536])).

tff(c_2264,plain,(
    ! [A_188] :
      ( r1_tarski(A_188,k2_tarski('#skF_9','#skF_10'))
      | ~ r1_tarski(A_188,k2_tarski('#skF_7','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_2087])).

tff(c_2340,plain,(
    r1_tarski(k1_tarski('#skF_7'),k2_tarski('#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_84,c_2264])).

tff(c_18,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2348,plain,(
    k3_xboole_0(k1_tarski('#skF_7'),k2_tarski('#skF_9','#skF_10')) = k1_tarski('#skF_7') ),
    inference(resolution,[status(thm)],[c_2340,c_18])).

tff(c_12,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1300,plain,(
    ! [A_148,B_149] : k3_xboole_0(k4_xboole_0(A_148,B_149),A_148) = k4_xboole_0(A_148,B_149) ),
    inference(resolution,[status(thm)],[c_22,c_217])).

tff(c_1366,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k4_xboole_0(A_24,B_25)) = k3_xboole_0(k3_xboole_0(A_24,B_25),A_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1300])).

tff(c_2768,plain,(
    ! [A_213,B_214] : k3_xboole_0(A_213,k3_xboole_0(A_213,B_214)) = k3_xboole_0(A_213,B_214) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2,c_1366])).

tff(c_2847,plain,(
    ! [A_213,B_214] : k5_xboole_0(A_213,k3_xboole_0(A_213,B_214)) = k4_xboole_0(A_213,k3_xboole_0(A_213,B_214)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2768,c_12])).

tff(c_2917,plain,(
    ! [A_213,B_214] : k4_xboole_0(A_213,k3_xboole_0(A_213,B_214)) = k4_xboole_0(A_213,B_214) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2847])).

tff(c_4280,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),k2_tarski('#skF_9','#skF_10')) = k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2348,c_2917])).

tff(c_4357,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),k2_tarski('#skF_9','#skF_10')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_792,c_4280])).

tff(c_30,plain,(
    ! [A_27,B_28] : k5_xboole_0(A_27,k4_xboole_0(B_28,A_27)) = k2_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4408,plain,(
    k2_xboole_0(k2_tarski('#skF_9','#skF_10'),k1_tarski('#skF_7')) = k5_xboole_0(k2_tarski('#skF_9','#skF_10'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4357,c_30])).

tff(c_4427,plain,(
    k2_xboole_0(k2_tarski('#skF_9','#skF_10'),k1_tarski('#skF_7')) = k2_tarski('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_740,c_4408])).

tff(c_80,plain,(
    ! [A_49,B_50,C_51] : k2_enumset1(A_49,A_49,B_50,C_51) = k1_enumset1(A_49,B_50,C_51) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_78,plain,(
    ! [A_47,B_48] : k1_enumset1(A_47,A_47,B_48) = k2_tarski(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2754,plain,(
    ! [A_209,B_210,C_211,D_212] : k2_xboole_0(k1_enumset1(A_209,B_210,C_211),k1_tarski(D_212)) = k2_enumset1(A_209,B_210,C_211,D_212) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2763,plain,(
    ! [A_47,B_48,D_212] : k2_xboole_0(k2_tarski(A_47,B_48),k1_tarski(D_212)) = k2_enumset1(A_47,A_47,B_48,D_212) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_2754])).

tff(c_2766,plain,(
    ! [A_47,B_48,D_212] : k2_xboole_0(k2_tarski(A_47,B_48),k1_tarski(D_212)) = k1_enumset1(A_47,B_48,D_212) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2763])).

tff(c_15120,plain,(
    k1_enumset1('#skF_9','#skF_10','#skF_7') = k2_tarski('#skF_9','#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_4427,c_2766])).

tff(c_34,plain,(
    ! [E_35,A_29,B_30] : r2_hidden(E_35,k1_enumset1(A_29,B_30,E_35)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_15158,plain,(
    r2_hidden('#skF_7',k2_tarski('#skF_9','#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_15120,c_34])).

tff(c_56,plain,(
    ! [D_41,B_37,A_36] :
      ( D_41 = B_37
      | D_41 = A_36
      | ~ r2_hidden(D_41,k2_tarski(A_36,B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_15172,plain,
    ( '#skF_7' = '#skF_10'
    | '#skF_7' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_15158,c_56])).

tff(c_15176,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_86,c_15172])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:21:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.88/3.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.88/3.18  
% 8.88/3.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.88/3.19  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_6 > #skF_7 > #skF_10 > #skF_5 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_1
% 8.88/3.19  
% 8.88/3.19  %Foreground sorts:
% 8.88/3.19  
% 8.88/3.19  
% 8.88/3.19  %Background operators:
% 8.88/3.19  
% 8.88/3.19  
% 8.88/3.19  %Foreground operators:
% 8.88/3.19  tff('#skF_2', type, '#skF_2': $i > $i).
% 8.88/3.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.88/3.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.88/3.19  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 8.88/3.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.88/3.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.88/3.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.88/3.19  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.88/3.19  tff('#skF_7', type, '#skF_7': $i).
% 8.88/3.19  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.88/3.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.88/3.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.88/3.19  tff('#skF_10', type, '#skF_10': $i).
% 8.88/3.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.88/3.19  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 8.88/3.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.88/3.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.88/3.19  tff('#skF_9', type, '#skF_9': $i).
% 8.88/3.19  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 8.88/3.19  tff('#skF_8', type, '#skF_8': $i).
% 8.88/3.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.88/3.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.88/3.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.88/3.19  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 8.88/3.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.88/3.19  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.88/3.19  
% 9.05/3.20  tff(f_123, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 9.05/3.20  tff(f_59, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 9.05/3.20  tff(f_67, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 9.05/3.20  tff(f_71, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 9.05/3.20  tff(f_77, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 9.05/3.20  tff(f_65, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.05/3.20  tff(f_63, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.05/3.20  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.05/3.20  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.05/3.20  tff(f_73, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.05/3.20  tff(f_113, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 9.05/3.20  tff(f_57, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 9.05/3.20  tff(f_109, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 9.05/3.20  tff(f_107, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 9.05/3.20  tff(f_103, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 9.05/3.20  tff(f_92, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 9.05/3.20  tff(f_101, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 9.05/3.20  tff(c_88, plain, ('#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_123])).
% 9.05/3.20  tff(c_86, plain, ('#skF_7'!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_123])).
% 9.05/3.20  tff(c_16, plain, (![A_17]: (k2_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.05/3.20  tff(c_22, plain, (![A_21, B_22]: (r1_tarski(k4_xboole_0(A_21, B_22), A_21))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.05/3.20  tff(c_121, plain, (![A_65]: (k1_xboole_0=A_65 | ~r1_tarski(A_65, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.05/3.20  tff(c_130, plain, (![B_22]: (k4_xboole_0(k1_xboole_0, B_22)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_121])).
% 9.05/3.20  tff(c_725, plain, (![A_115, B_116]: (k5_xboole_0(A_115, k4_xboole_0(B_116, A_115))=k2_xboole_0(A_115, B_116))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.05/3.20  tff(c_737, plain, (![B_22]: (k5_xboole_0(B_22, k1_xboole_0)=k2_xboole_0(B_22, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_130, c_725])).
% 9.05/3.20  tff(c_740, plain, (![B_22]: (k5_xboole_0(B_22, k1_xboole_0)=B_22)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_737])).
% 9.05/3.20  tff(c_20, plain, (![A_20]: (r1_tarski(k1_xboole_0, A_20))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.05/3.20  tff(c_217, plain, (![A_89, B_90]: (k3_xboole_0(A_89, B_90)=A_89 | ~r1_tarski(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.05/3.20  tff(c_239, plain, (![A_91]: (k3_xboole_0(k1_xboole_0, A_91)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_217])).
% 9.05/3.20  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.05/3.20  tff(c_244, plain, (![A_91]: (k3_xboole_0(A_91, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_239, c_2])).
% 9.05/3.20  tff(c_445, plain, (![A_100, B_101]: (k5_xboole_0(A_100, k3_xboole_0(A_100, B_101))=k4_xboole_0(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.05/3.20  tff(c_457, plain, (![A_91]: (k5_xboole_0(A_91, k1_xboole_0)=k4_xboole_0(A_91, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_244, c_445])).
% 9.05/3.20  tff(c_762, plain, (![A_118]: (k4_xboole_0(A_118, k1_xboole_0)=A_118)), inference(demodulation, [status(thm), theory('equality')], [c_740, c_457])).
% 9.05/3.20  tff(c_26, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k4_xboole_0(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.05/3.20  tff(c_775, plain, (![A_118]: (k4_xboole_0(A_118, A_118)=k3_xboole_0(A_118, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_762, c_26])).
% 9.05/3.20  tff(c_792, plain, (![A_118]: (k4_xboole_0(A_118, A_118)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_244, c_775])).
% 9.05/3.20  tff(c_84, plain, (![A_56, B_57]: (r1_tarski(k1_tarski(A_56), k2_tarski(A_56, B_57)))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.05/3.20  tff(c_90, plain, (r1_tarski(k2_tarski('#skF_7', '#skF_8'), k2_tarski('#skF_9', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 9.05/3.20  tff(c_236, plain, (k3_xboole_0(k2_tarski('#skF_7', '#skF_8'), k2_tarski('#skF_9', '#skF_10'))=k2_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_90, c_217])).
% 9.05/3.20  tff(c_536, plain, (![A_104, B_105, C_106]: (r1_tarski(A_104, B_105) | ~r1_tarski(A_104, k3_xboole_0(B_105, C_106)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.05/3.20  tff(c_2087, plain, (![A_182, B_183, A_184]: (r1_tarski(A_182, B_183) | ~r1_tarski(A_182, k3_xboole_0(A_184, B_183)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_536])).
% 9.05/3.20  tff(c_2264, plain, (![A_188]: (r1_tarski(A_188, k2_tarski('#skF_9', '#skF_10')) | ~r1_tarski(A_188, k2_tarski('#skF_7', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_236, c_2087])).
% 9.05/3.20  tff(c_2340, plain, (r1_tarski(k1_tarski('#skF_7'), k2_tarski('#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_84, c_2264])).
% 9.05/3.20  tff(c_18, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=A_18 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.05/3.20  tff(c_2348, plain, (k3_xboole_0(k1_tarski('#skF_7'), k2_tarski('#skF_9', '#skF_10'))=k1_tarski('#skF_7')), inference(resolution, [status(thm)], [c_2340, c_18])).
% 9.05/3.20  tff(c_12, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.05/3.20  tff(c_1300, plain, (![A_148, B_149]: (k3_xboole_0(k4_xboole_0(A_148, B_149), A_148)=k4_xboole_0(A_148, B_149))), inference(resolution, [status(thm)], [c_22, c_217])).
% 9.05/3.20  tff(c_1366, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k4_xboole_0(A_24, B_25))=k3_xboole_0(k3_xboole_0(A_24, B_25), A_24))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1300])).
% 9.05/3.20  tff(c_2768, plain, (![A_213, B_214]: (k3_xboole_0(A_213, k3_xboole_0(A_213, B_214))=k3_xboole_0(A_213, B_214))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2, c_1366])).
% 9.05/3.20  tff(c_2847, plain, (![A_213, B_214]: (k5_xboole_0(A_213, k3_xboole_0(A_213, B_214))=k4_xboole_0(A_213, k3_xboole_0(A_213, B_214)))), inference(superposition, [status(thm), theory('equality')], [c_2768, c_12])).
% 9.05/3.20  tff(c_2917, plain, (![A_213, B_214]: (k4_xboole_0(A_213, k3_xboole_0(A_213, B_214))=k4_xboole_0(A_213, B_214))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2847])).
% 9.05/3.20  tff(c_4280, plain, (k4_xboole_0(k1_tarski('#skF_7'), k2_tarski('#skF_9', '#skF_10'))=k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2348, c_2917])).
% 9.05/3.20  tff(c_4357, plain, (k4_xboole_0(k1_tarski('#skF_7'), k2_tarski('#skF_9', '#skF_10'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_792, c_4280])).
% 9.05/3.20  tff(c_30, plain, (![A_27, B_28]: (k5_xboole_0(A_27, k4_xboole_0(B_28, A_27))=k2_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.05/3.20  tff(c_4408, plain, (k2_xboole_0(k2_tarski('#skF_9', '#skF_10'), k1_tarski('#skF_7'))=k5_xboole_0(k2_tarski('#skF_9', '#skF_10'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4357, c_30])).
% 9.05/3.20  tff(c_4427, plain, (k2_xboole_0(k2_tarski('#skF_9', '#skF_10'), k1_tarski('#skF_7'))=k2_tarski('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_740, c_4408])).
% 9.05/3.20  tff(c_80, plain, (![A_49, B_50, C_51]: (k2_enumset1(A_49, A_49, B_50, C_51)=k1_enumset1(A_49, B_50, C_51))), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.05/3.20  tff(c_78, plain, (![A_47, B_48]: (k1_enumset1(A_47, A_47, B_48)=k2_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_107])).
% 9.05/3.20  tff(c_2754, plain, (![A_209, B_210, C_211, D_212]: (k2_xboole_0(k1_enumset1(A_209, B_210, C_211), k1_tarski(D_212))=k2_enumset1(A_209, B_210, C_211, D_212))), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.05/3.20  tff(c_2763, plain, (![A_47, B_48, D_212]: (k2_xboole_0(k2_tarski(A_47, B_48), k1_tarski(D_212))=k2_enumset1(A_47, A_47, B_48, D_212))), inference(superposition, [status(thm), theory('equality')], [c_78, c_2754])).
% 9.05/3.20  tff(c_2766, plain, (![A_47, B_48, D_212]: (k2_xboole_0(k2_tarski(A_47, B_48), k1_tarski(D_212))=k1_enumset1(A_47, B_48, D_212))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2763])).
% 9.05/3.20  tff(c_15120, plain, (k1_enumset1('#skF_9', '#skF_10', '#skF_7')=k2_tarski('#skF_9', '#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_4427, c_2766])).
% 9.05/3.20  tff(c_34, plain, (![E_35, A_29, B_30]: (r2_hidden(E_35, k1_enumset1(A_29, B_30, E_35)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.05/3.20  tff(c_15158, plain, (r2_hidden('#skF_7', k2_tarski('#skF_9', '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_15120, c_34])).
% 9.05/3.20  tff(c_56, plain, (![D_41, B_37, A_36]: (D_41=B_37 | D_41=A_36 | ~r2_hidden(D_41, k2_tarski(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.05/3.20  tff(c_15172, plain, ('#skF_7'='#skF_10' | '#skF_7'='#skF_9'), inference(resolution, [status(thm)], [c_15158, c_56])).
% 9.05/3.20  tff(c_15176, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_86, c_15172])).
% 9.05/3.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.05/3.20  
% 9.05/3.20  Inference rules
% 9.05/3.20  ----------------------
% 9.05/3.20  #Ref     : 0
% 9.05/3.20  #Sup     : 3504
% 9.05/3.20  #Fact    : 26
% 9.05/3.20  #Define  : 0
% 9.05/3.20  #Split   : 2
% 9.05/3.20  #Chain   : 0
% 9.05/3.20  #Close   : 0
% 9.05/3.20  
% 9.05/3.20  Ordering : KBO
% 9.05/3.20  
% 9.05/3.20  Simplification rules
% 9.05/3.20  ----------------------
% 9.05/3.20  #Subsume      : 177
% 9.05/3.20  #Demod        : 4117
% 9.05/3.20  #Tautology    : 2615
% 9.05/3.20  #SimpNegUnit  : 8
% 9.05/3.20  #BackRed      : 2
% 9.05/3.20  
% 9.05/3.20  #Partial instantiations: 0
% 9.05/3.20  #Strategies tried      : 1
% 9.05/3.20  
% 9.05/3.20  Timing (in seconds)
% 9.05/3.20  ----------------------
% 9.05/3.21  Preprocessing        : 0.36
% 9.05/3.21  Parsing              : 0.19
% 9.05/3.21  CNF conversion       : 0.03
% 9.05/3.21  Main loop            : 2.04
% 9.05/3.21  Inferencing          : 0.49
% 9.05/3.21  Reduction            : 1.04
% 9.05/3.21  Demodulation         : 0.89
% 9.05/3.21  BG Simplification    : 0.06
% 9.05/3.21  Subsumption          : 0.35
% 9.05/3.21  Abstraction          : 0.09
% 9.05/3.21  MUC search           : 0.00
% 9.05/3.21  Cooper               : 0.00
% 9.05/3.21  Total                : 2.44
% 9.05/3.21  Index Insertion      : 0.00
% 9.05/3.21  Index Deletion       : 0.00
% 9.05/3.21  Index Matching       : 0.00
% 9.05/3.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
