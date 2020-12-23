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

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   64 (  88 expanded)
%              Number of leaves         :   34 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :   57 (  90 expanded)
%              Number of equality atoms :   23 (  37 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_100,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_77,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).

tff(f_83,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_79,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_95,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_73,axiom,(
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

tff(c_80,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_28,plain,(
    ! [A_22,B_23] : r1_tarski(A_22,k2_xboole_0(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_243,plain,(
    ! [C_110,B_111,A_112] : k1_enumset1(C_110,B_111,A_112) = k1_enumset1(A_112,B_111,C_110) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_66,plain,(
    ! [A_47,B_48] : k1_enumset1(A_47,A_47,B_48) = k2_tarski(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_259,plain,(
    ! [C_110,B_111] : k1_enumset1(C_110,B_111,B_111) = k2_tarski(B_111,C_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_66])).

tff(c_769,plain,(
    ! [A_157,B_158,C_159] : k2_xboole_0(k2_tarski(A_157,B_158),k1_tarski(C_159)) = k1_enumset1(A_157,B_158,C_159) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_804,plain,(
    ! [A_160,B_161,C_162] : r1_tarski(k2_tarski(A_160,B_161),k1_enumset1(A_160,B_161,C_162)) ),
    inference(superposition,[status(thm),theory(equality)],[c_769,c_28])).

tff(c_815,plain,(
    ! [C_110,B_111] : r1_tarski(k2_tarski(C_110,B_111),k2_tarski(B_111,C_110)) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_804])).

tff(c_849,plain,(
    ! [C_165,B_166] : r1_tarski(k2_tarski(C_165,B_166),k2_tarski(B_166,C_165)) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_804])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( B_13 = A_12
      | ~ r1_tarski(B_13,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_857,plain,(
    ! [C_165,B_166] :
      ( k2_tarski(C_165,B_166) = k2_tarski(B_166,C_165)
      | ~ r1_tarski(k2_tarski(B_166,C_165),k2_tarski(C_165,B_166)) ) ),
    inference(resolution,[status(thm)],[c_849,c_14])).

tff(c_1189,plain,(
    ! [C_180,B_181] : k2_tarski(C_180,B_181) = k2_tarski(B_181,C_180) ),
    inference(demodulation,[status(thm),theory(equality)],[c_815,c_857])).

tff(c_78,plain,(
    ! [A_74,B_75] : k3_tarski(k2_tarski(A_74,B_75)) = k2_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1381,plain,(
    ! [B_192,C_193] : k3_tarski(k2_tarski(B_192,C_193)) = k2_xboole_0(C_193,B_192) ),
    inference(superposition,[status(thm),theory(equality)],[c_1189,c_78])).

tff(c_1387,plain,(
    ! [C_193,B_192] : k2_xboole_0(C_193,B_192) = k2_xboole_0(B_192,C_193) ),
    inference(superposition,[status(thm),theory(equality)],[c_1381,c_78])).

tff(c_82,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_367,plain,(
    ! [B_117,A_118] :
      ( B_117 = A_118
      | ~ r1_tarski(B_117,A_118)
      | ~ r1_tarski(A_118,B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_376,plain,
    ( k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_6'
    | ~ r1_tarski('#skF_6',k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(resolution,[status(thm)],[c_82,c_367])).

tff(c_383,plain,(
    ~ r1_tarski('#skF_6',k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_376])).

tff(c_1408,plain,(
    ~ r1_tarski('#skF_6',k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1387,c_383])).

tff(c_1412,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1408])).

tff(c_1413,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_376])).

tff(c_1426,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1413,c_28])).

tff(c_192,plain,(
    ! [A_100,B_101] : k1_enumset1(A_100,A_100,B_101) = k2_tarski(A_100,B_101) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_38,plain,(
    ! [E_35,A_29,C_31] : r2_hidden(E_35,k1_enumset1(A_29,E_35,C_31)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_201,plain,(
    ! [A_100,B_101] : r2_hidden(A_100,k2_tarski(A_100,B_101)) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_38])).

tff(c_1483,plain,(
    ! [C_199,B_200,A_201] :
      ( r2_hidden(C_199,B_200)
      | ~ r2_hidden(C_199,A_201)
      | ~ r1_tarski(A_201,B_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1535,plain,(
    ! [A_209,B_210,B_211] :
      ( r2_hidden(A_209,B_210)
      | ~ r1_tarski(k2_tarski(A_209,B_211),B_210) ) ),
    inference(resolution,[status(thm)],[c_201,c_1483])).

tff(c_1538,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_1426,c_1535])).

tff(c_1553,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1538])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:27:57 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.44/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.64  
% 3.44/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.64  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 3.44/1.64  
% 3.44/1.64  %Foreground sorts:
% 3.44/1.64  
% 3.44/1.64  
% 3.44/1.64  %Background operators:
% 3.44/1.64  
% 3.44/1.64  
% 3.44/1.64  %Foreground operators:
% 3.44/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.44/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.44/1.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.44/1.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.44/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.44/1.64  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.44/1.64  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.44/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.44/1.64  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.44/1.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.44/1.64  tff('#skF_5', type, '#skF_5': $i).
% 3.44/1.64  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.44/1.64  tff('#skF_6', type, '#skF_6': $i).
% 3.44/1.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.44/1.64  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.44/1.64  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.44/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.44/1.64  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.44/1.64  tff('#skF_4', type, '#skF_4': $i).
% 3.44/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.44/1.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.44/1.64  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.44/1.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.44/1.64  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.44/1.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.44/1.64  
% 3.44/1.66  tff(f_100, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 3.44/1.66  tff(f_54, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.44/1.66  tff(f_77, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_enumset1)).
% 3.44/1.66  tff(f_83, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.44/1.66  tff(f_79, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 3.44/1.66  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.44/1.66  tff(f_95, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.44/1.66  tff(f_73, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.44/1.66  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.44/1.66  tff(c_80, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.44/1.66  tff(c_28, plain, (![A_22, B_23]: (r1_tarski(A_22, k2_xboole_0(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.44/1.66  tff(c_243, plain, (![C_110, B_111, A_112]: (k1_enumset1(C_110, B_111, A_112)=k1_enumset1(A_112, B_111, C_110))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.44/1.66  tff(c_66, plain, (![A_47, B_48]: (k1_enumset1(A_47, A_47, B_48)=k2_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.44/1.66  tff(c_259, plain, (![C_110, B_111]: (k1_enumset1(C_110, B_111, B_111)=k2_tarski(B_111, C_110))), inference(superposition, [status(thm), theory('equality')], [c_243, c_66])).
% 3.44/1.66  tff(c_769, plain, (![A_157, B_158, C_159]: (k2_xboole_0(k2_tarski(A_157, B_158), k1_tarski(C_159))=k1_enumset1(A_157, B_158, C_159))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.44/1.66  tff(c_804, plain, (![A_160, B_161, C_162]: (r1_tarski(k2_tarski(A_160, B_161), k1_enumset1(A_160, B_161, C_162)))), inference(superposition, [status(thm), theory('equality')], [c_769, c_28])).
% 3.44/1.66  tff(c_815, plain, (![C_110, B_111]: (r1_tarski(k2_tarski(C_110, B_111), k2_tarski(B_111, C_110)))), inference(superposition, [status(thm), theory('equality')], [c_259, c_804])).
% 3.44/1.66  tff(c_849, plain, (![C_165, B_166]: (r1_tarski(k2_tarski(C_165, B_166), k2_tarski(B_166, C_165)))), inference(superposition, [status(thm), theory('equality')], [c_259, c_804])).
% 3.44/1.66  tff(c_14, plain, (![B_13, A_12]: (B_13=A_12 | ~r1_tarski(B_13, A_12) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.44/1.66  tff(c_857, plain, (![C_165, B_166]: (k2_tarski(C_165, B_166)=k2_tarski(B_166, C_165) | ~r1_tarski(k2_tarski(B_166, C_165), k2_tarski(C_165, B_166)))), inference(resolution, [status(thm)], [c_849, c_14])).
% 3.44/1.66  tff(c_1189, plain, (![C_180, B_181]: (k2_tarski(C_180, B_181)=k2_tarski(B_181, C_180))), inference(demodulation, [status(thm), theory('equality')], [c_815, c_857])).
% 3.44/1.66  tff(c_78, plain, (![A_74, B_75]: (k3_tarski(k2_tarski(A_74, B_75))=k2_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.44/1.66  tff(c_1381, plain, (![B_192, C_193]: (k3_tarski(k2_tarski(B_192, C_193))=k2_xboole_0(C_193, B_192))), inference(superposition, [status(thm), theory('equality')], [c_1189, c_78])).
% 3.44/1.66  tff(c_1387, plain, (![C_193, B_192]: (k2_xboole_0(C_193, B_192)=k2_xboole_0(B_192, C_193))), inference(superposition, [status(thm), theory('equality')], [c_1381, c_78])).
% 3.44/1.66  tff(c_82, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.44/1.66  tff(c_367, plain, (![B_117, A_118]: (B_117=A_118 | ~r1_tarski(B_117, A_118) | ~r1_tarski(A_118, B_117))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.44/1.66  tff(c_376, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_6' | ~r1_tarski('#skF_6', k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_82, c_367])).
% 3.44/1.66  tff(c_383, plain, (~r1_tarski('#skF_6', k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(splitLeft, [status(thm)], [c_376])).
% 3.44/1.66  tff(c_1408, plain, (~r1_tarski('#skF_6', k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_1387, c_383])).
% 3.44/1.66  tff(c_1412, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_1408])).
% 3.44/1.66  tff(c_1413, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_376])).
% 3.44/1.66  tff(c_1426, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1413, c_28])).
% 3.44/1.66  tff(c_192, plain, (![A_100, B_101]: (k1_enumset1(A_100, A_100, B_101)=k2_tarski(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.44/1.66  tff(c_38, plain, (![E_35, A_29, C_31]: (r2_hidden(E_35, k1_enumset1(A_29, E_35, C_31)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.44/1.66  tff(c_201, plain, (![A_100, B_101]: (r2_hidden(A_100, k2_tarski(A_100, B_101)))), inference(superposition, [status(thm), theory('equality')], [c_192, c_38])).
% 3.44/1.66  tff(c_1483, plain, (![C_199, B_200, A_201]: (r2_hidden(C_199, B_200) | ~r2_hidden(C_199, A_201) | ~r1_tarski(A_201, B_200))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.44/1.66  tff(c_1535, plain, (![A_209, B_210, B_211]: (r2_hidden(A_209, B_210) | ~r1_tarski(k2_tarski(A_209, B_211), B_210))), inference(resolution, [status(thm)], [c_201, c_1483])).
% 3.44/1.66  tff(c_1538, plain, (r2_hidden('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_1426, c_1535])).
% 3.44/1.66  tff(c_1553, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_1538])).
% 3.44/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.66  
% 3.44/1.66  Inference rules
% 3.44/1.66  ----------------------
% 3.44/1.66  #Ref     : 0
% 3.44/1.66  #Sup     : 358
% 3.44/1.66  #Fact    : 0
% 3.44/1.66  #Define  : 0
% 3.44/1.66  #Split   : 1
% 3.44/1.66  #Chain   : 0
% 3.44/1.66  #Close   : 0
% 3.44/1.66  
% 3.44/1.66  Ordering : KBO
% 3.44/1.66  
% 3.44/1.66  Simplification rules
% 3.44/1.66  ----------------------
% 3.44/1.66  #Subsume      : 6
% 3.44/1.66  #Demod        : 177
% 3.44/1.66  #Tautology    : 217
% 3.44/1.66  #SimpNegUnit  : 1
% 3.44/1.66  #BackRed      : 5
% 3.44/1.66  
% 3.44/1.66  #Partial instantiations: 0
% 3.44/1.66  #Strategies tried      : 1
% 3.44/1.66  
% 3.44/1.66  Timing (in seconds)
% 3.44/1.66  ----------------------
% 3.44/1.66  Preprocessing        : 0.40
% 3.44/1.66  Parsing              : 0.22
% 3.44/1.66  CNF conversion       : 0.03
% 3.44/1.66  Main loop            : 0.43
% 3.44/1.66  Inferencing          : 0.14
% 3.44/1.66  Reduction            : 0.17
% 3.44/1.66  Demodulation         : 0.13
% 3.44/1.66  BG Simplification    : 0.03
% 3.44/1.66  Subsumption          : 0.07
% 3.44/1.66  Abstraction          : 0.03
% 3.44/1.66  MUC search           : 0.00
% 3.44/1.66  Cooper               : 0.00
% 3.44/1.66  Total                : 0.86
% 3.44/1.66  Index Insertion      : 0.00
% 3.44/1.66  Index Deletion       : 0.00
% 3.44/1.66  Index Matching       : 0.00
% 3.44/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
