%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:05 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :   62 (  86 expanded)
%              Number of leaves         :   32 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :   57 (  90 expanded)
%              Number of equality atoms :   23 (  37 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_74,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).

tff(f_80,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_76,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_92,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_82,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_30,plain,(
    ! [A_15,B_16] : r1_tarski(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_208,plain,(
    ! [C_101,B_102,A_103] : k1_enumset1(C_101,B_102,A_103) = k1_enumset1(A_103,B_102,C_101) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_68,plain,(
    ! [A_40,B_41] : k1_enumset1(A_40,A_40,B_41) = k2_tarski(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_224,plain,(
    ! [C_101,B_102] : k1_enumset1(C_101,B_102,B_102) = k2_tarski(B_102,C_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_68])).

tff(c_608,plain,(
    ! [A_150,B_151,C_152] : k2_xboole_0(k2_tarski(A_150,B_151),k1_tarski(C_152)) = k1_enumset1(A_150,B_151,C_152) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_639,plain,(
    ! [A_153,B_154,C_155] : r1_tarski(k2_tarski(A_153,B_154),k1_enumset1(A_153,B_154,C_155)) ),
    inference(superposition,[status(thm),theory(equality)],[c_608,c_30])).

tff(c_650,plain,(
    ! [C_101,B_102] : r1_tarski(k2_tarski(C_101,B_102),k2_tarski(B_102,C_101)) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_639])).

tff(c_734,plain,(
    ! [C_161,B_162] : r1_tarski(k2_tarski(C_161,B_162),k2_tarski(B_162,C_161)) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_639])).

tff(c_22,plain,(
    ! [B_12,A_11] :
      ( B_12 = A_11
      | ~ r1_tarski(B_12,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_742,plain,(
    ! [C_161,B_162] :
      ( k2_tarski(C_161,B_162) = k2_tarski(B_162,C_161)
      | ~ r1_tarski(k2_tarski(B_162,C_161),k2_tarski(C_161,B_162)) ) ),
    inference(resolution,[status(thm)],[c_734,c_22])).

tff(c_758,plain,(
    ! [C_163,B_164] : k2_tarski(C_163,B_164) = k2_tarski(B_164,C_163) ),
    inference(demodulation,[status(thm),theory(equality)],[c_650,c_742])).

tff(c_80,plain,(
    ! [A_67,B_68] : k3_tarski(k2_tarski(A_67,B_68)) = k2_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_913,plain,(
    ! [C_167,B_168] : k3_tarski(k2_tarski(C_167,B_168)) = k2_xboole_0(B_168,C_167) ),
    inference(superposition,[status(thm),theory(equality)],[c_758,c_80])).

tff(c_919,plain,(
    ! [C_167,B_168] : k2_xboole_0(C_167,B_168) = k2_xboole_0(B_168,C_167) ),
    inference(superposition,[status(thm),theory(equality)],[c_913,c_80])).

tff(c_84,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_331,plain,(
    ! [B_106,A_107] :
      ( B_106 = A_107
      | ~ r1_tarski(B_106,A_107)
      | ~ r1_tarski(A_107,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_343,plain,
    ( k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_6'
    | ~ r1_tarski('#skF_6',k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(resolution,[status(thm)],[c_84,c_331])).

tff(c_393,plain,(
    ~ r1_tarski('#skF_6',k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_343])).

tff(c_960,plain,(
    ~ r1_tarski('#skF_6',k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_919,c_393])).

tff(c_964,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_960])).

tff(c_965,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_343])).

tff(c_972,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_965,c_30])).

tff(c_134,plain,(
    ! [A_86,B_87] : k1_enumset1(A_86,A_86,B_87) = k2_tarski(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_42,plain,(
    ! [E_28,B_23,C_24] : r2_hidden(E_28,k1_enumset1(E_28,B_23,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_140,plain,(
    ! [A_86,B_87] : r2_hidden(A_86,k2_tarski(A_86,B_87)) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_42])).

tff(c_350,plain,(
    ! [C_108,B_109,A_110] :
      ( r2_hidden(C_108,B_109)
      | ~ r2_hidden(C_108,A_110)
      | ~ r1_tarski(A_110,B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1054,plain,(
    ! [A_186,B_187,B_188] :
      ( r2_hidden(A_186,B_187)
      | ~ r1_tarski(k2_tarski(A_186,B_188),B_187) ) ),
    inference(resolution,[status(thm)],[c_140,c_350])).

tff(c_1057,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_972,c_1054])).

tff(c_1076,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1057])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:41:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.19/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.56  
% 3.19/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.56  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 3.19/1.56  
% 3.19/1.56  %Foreground sorts:
% 3.19/1.56  
% 3.19/1.56  
% 3.19/1.56  %Background operators:
% 3.19/1.56  
% 3.19/1.56  
% 3.19/1.56  %Foreground operators:
% 3.19/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.19/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.19/1.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.19/1.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.19/1.56  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.19/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.19/1.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.19/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.19/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.19/1.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.19/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.19/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.19/1.56  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.19/1.56  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.19/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.19/1.56  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.19/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.19/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.19/1.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.19/1.56  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.19/1.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.19/1.56  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.19/1.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.19/1.56  
% 3.19/1.58  tff(f_97, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 3.19/1.58  tff(f_51, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.19/1.58  tff(f_74, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_enumset1)).
% 3.19/1.58  tff(f_80, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.19/1.58  tff(f_76, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 3.19/1.58  tff(f_47, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.19/1.58  tff(f_92, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.19/1.58  tff(f_70, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.19/1.58  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.19/1.58  tff(c_82, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.19/1.58  tff(c_30, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.19/1.58  tff(c_208, plain, (![C_101, B_102, A_103]: (k1_enumset1(C_101, B_102, A_103)=k1_enumset1(A_103, B_102, C_101))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.19/1.58  tff(c_68, plain, (![A_40, B_41]: (k1_enumset1(A_40, A_40, B_41)=k2_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.19/1.58  tff(c_224, plain, (![C_101, B_102]: (k1_enumset1(C_101, B_102, B_102)=k2_tarski(B_102, C_101))), inference(superposition, [status(thm), theory('equality')], [c_208, c_68])).
% 3.19/1.58  tff(c_608, plain, (![A_150, B_151, C_152]: (k2_xboole_0(k2_tarski(A_150, B_151), k1_tarski(C_152))=k1_enumset1(A_150, B_151, C_152))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.19/1.58  tff(c_639, plain, (![A_153, B_154, C_155]: (r1_tarski(k2_tarski(A_153, B_154), k1_enumset1(A_153, B_154, C_155)))), inference(superposition, [status(thm), theory('equality')], [c_608, c_30])).
% 3.19/1.58  tff(c_650, plain, (![C_101, B_102]: (r1_tarski(k2_tarski(C_101, B_102), k2_tarski(B_102, C_101)))), inference(superposition, [status(thm), theory('equality')], [c_224, c_639])).
% 3.19/1.58  tff(c_734, plain, (![C_161, B_162]: (r1_tarski(k2_tarski(C_161, B_162), k2_tarski(B_162, C_161)))), inference(superposition, [status(thm), theory('equality')], [c_224, c_639])).
% 3.19/1.58  tff(c_22, plain, (![B_12, A_11]: (B_12=A_11 | ~r1_tarski(B_12, A_11) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.19/1.58  tff(c_742, plain, (![C_161, B_162]: (k2_tarski(C_161, B_162)=k2_tarski(B_162, C_161) | ~r1_tarski(k2_tarski(B_162, C_161), k2_tarski(C_161, B_162)))), inference(resolution, [status(thm)], [c_734, c_22])).
% 3.19/1.58  tff(c_758, plain, (![C_163, B_164]: (k2_tarski(C_163, B_164)=k2_tarski(B_164, C_163))), inference(demodulation, [status(thm), theory('equality')], [c_650, c_742])).
% 3.19/1.58  tff(c_80, plain, (![A_67, B_68]: (k3_tarski(k2_tarski(A_67, B_68))=k2_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.19/1.58  tff(c_913, plain, (![C_167, B_168]: (k3_tarski(k2_tarski(C_167, B_168))=k2_xboole_0(B_168, C_167))), inference(superposition, [status(thm), theory('equality')], [c_758, c_80])).
% 3.19/1.58  tff(c_919, plain, (![C_167, B_168]: (k2_xboole_0(C_167, B_168)=k2_xboole_0(B_168, C_167))), inference(superposition, [status(thm), theory('equality')], [c_913, c_80])).
% 3.19/1.58  tff(c_84, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.19/1.58  tff(c_331, plain, (![B_106, A_107]: (B_106=A_107 | ~r1_tarski(B_106, A_107) | ~r1_tarski(A_107, B_106))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.19/1.58  tff(c_343, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_6' | ~r1_tarski('#skF_6', k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_84, c_331])).
% 3.19/1.58  tff(c_393, plain, (~r1_tarski('#skF_6', k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(splitLeft, [status(thm)], [c_343])).
% 3.19/1.58  tff(c_960, plain, (~r1_tarski('#skF_6', k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_919, c_393])).
% 3.19/1.58  tff(c_964, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_960])).
% 3.19/1.58  tff(c_965, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_343])).
% 3.19/1.58  tff(c_972, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_965, c_30])).
% 3.19/1.58  tff(c_134, plain, (![A_86, B_87]: (k1_enumset1(A_86, A_86, B_87)=k2_tarski(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.19/1.58  tff(c_42, plain, (![E_28, B_23, C_24]: (r2_hidden(E_28, k1_enumset1(E_28, B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.19/1.58  tff(c_140, plain, (![A_86, B_87]: (r2_hidden(A_86, k2_tarski(A_86, B_87)))), inference(superposition, [status(thm), theory('equality')], [c_134, c_42])).
% 3.19/1.58  tff(c_350, plain, (![C_108, B_109, A_110]: (r2_hidden(C_108, B_109) | ~r2_hidden(C_108, A_110) | ~r1_tarski(A_110, B_109))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.19/1.58  tff(c_1054, plain, (![A_186, B_187, B_188]: (r2_hidden(A_186, B_187) | ~r1_tarski(k2_tarski(A_186, B_188), B_187))), inference(resolution, [status(thm)], [c_140, c_350])).
% 3.19/1.58  tff(c_1057, plain, (r2_hidden('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_972, c_1054])).
% 3.19/1.58  tff(c_1076, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_1057])).
% 3.19/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.58  
% 3.19/1.58  Inference rules
% 3.19/1.58  ----------------------
% 3.19/1.58  #Ref     : 0
% 3.19/1.58  #Sup     : 242
% 3.19/1.58  #Fact    : 0
% 3.19/1.58  #Define  : 0
% 3.19/1.58  #Split   : 1
% 3.19/1.58  #Chain   : 0
% 3.19/1.58  #Close   : 0
% 3.19/1.58  
% 3.19/1.58  Ordering : KBO
% 3.19/1.58  
% 3.19/1.58  Simplification rules
% 3.19/1.58  ----------------------
% 3.19/1.58  #Subsume      : 12
% 3.19/1.58  #Demod        : 106
% 3.19/1.58  #Tautology    : 140
% 3.19/1.58  #SimpNegUnit  : 1
% 3.19/1.58  #BackRed      : 3
% 3.19/1.58  
% 3.19/1.58  #Partial instantiations: 0
% 3.19/1.58  #Strategies tried      : 1
% 3.19/1.58  
% 3.19/1.58  Timing (in seconds)
% 3.19/1.58  ----------------------
% 3.19/1.58  Preprocessing        : 0.38
% 3.19/1.58  Parsing              : 0.19
% 3.19/1.58  CNF conversion       : 0.03
% 3.19/1.58  Main loop            : 0.37
% 3.19/1.58  Inferencing          : 0.12
% 3.19/1.58  Reduction            : 0.14
% 3.19/1.58  Demodulation         : 0.11
% 3.19/1.58  BG Simplification    : 0.03
% 3.19/1.58  Subsumption          : 0.07
% 3.19/1.58  Abstraction          : 0.02
% 3.19/1.58  MUC search           : 0.00
% 3.19/1.58  Cooper               : 0.00
% 3.19/1.58  Total                : 0.78
% 3.19/1.58  Index Insertion      : 0.00
% 3.19/1.58  Index Deletion       : 0.00
% 3.19/1.58  Index Matching       : 0.00
% 3.19/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
