%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:49 EST 2020

% Result     : Theorem 4.43s
% Output     : CNFRefutation 4.51s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 219 expanded)
%              Number of leaves         :   22 (  83 expanded)
%              Depth                    :   19
%              Number of atoms          :  105 ( 430 expanded)
%              Number of equality atoms :   44 ( 149 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( r2_xboole_0(A,B)
        & r1_tarski(B,C) )
     => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_xboole_1)).

tff(c_40,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_36,plain,(
    k1_tarski('#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_xboole_0(A_1,B_2)
      | B_2 = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_32,plain,(
    ! [B_20,C_21] : r1_tarski(k1_tarski(B_20),k2_tarski(B_20,C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_392,plain,(
    ! [C_91,B_92,A_93] :
      ( r1_tarski(k4_xboole_0(C_91,B_92),k4_xboole_0(C_91,A_93))
      | ~ r1_tarski(A_93,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1534,plain,(
    ! [C_165,B_166,A_167] :
      ( k4_xboole_0(k4_xboole_0(C_165,B_166),k4_xboole_0(C_165,A_167)) = k1_xboole_0
      | ~ r1_tarski(A_167,B_166) ) ),
    inference(resolution,[status(thm)],[c_392,c_10])).

tff(c_1731,plain,(
    ! [B_171] :
      ( k4_xboole_0(k4_xboole_0('#skF_1',B_171),k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(k1_tarski('#skF_2'),B_171) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1534])).

tff(c_1755,plain,(
    ! [C_21] : k4_xboole_0(k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_21)),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_1731])).

tff(c_16,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_184,plain,(
    ! [A_62,B_63,C_64] :
      ( r1_tarski(A_62,B_63)
      | ~ r1_tarski(A_62,k4_xboole_0(B_63,C_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_209,plain,(
    ! [B_63,C_64,B_9] : r1_tarski(k3_xboole_0(k4_xboole_0(B_63,C_64),B_9),B_63) ),
    inference(resolution,[status(thm)],[c_16,c_184])).

tff(c_14,plain,(
    ! [A_5,B_6,C_7] :
      ( r1_tarski(A_5,B_6)
      | ~ r1_tarski(A_5,k4_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_660,plain,(
    ! [C_117,B_118,A_119] :
      ( r1_tarski(k4_xboole_0(C_117,B_118),C_117)
      | ~ r1_tarski(A_119,B_118) ) ),
    inference(resolution,[status(thm)],[c_392,c_14])).

tff(c_710,plain,(
    ! [C_120,B_121] : r1_tarski(k4_xboole_0(C_120,B_121),C_120) ),
    inference(resolution,[status(thm)],[c_209,c_660])).

tff(c_1081,plain,(
    ! [C_136,B_137] : k4_xboole_0(k4_xboole_0(C_136,B_137),C_136) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_710,c_10])).

tff(c_2924,plain,(
    ! [A_223,C_224,B_225] :
      ( r1_tarski(A_223,k4_xboole_0(C_224,B_225))
      | ~ r1_tarski(A_223,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1081,c_14])).

tff(c_2974,plain,(
    ! [A_226,C_227] :
      ( r1_tarski(A_226,C_227)
      | ~ r1_tarski(A_226,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2924,c_14])).

tff(c_3004,plain,(
    ! [A_3,C_227] :
      ( r1_tarski(A_3,C_227)
      | k4_xboole_0(A_3,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_2974])).

tff(c_700,plain,(
    ! [C_117,B_63] : r1_tarski(k4_xboole_0(C_117,B_63),C_117) ),
    inference(resolution,[status(thm)],[c_209,c_660])).

tff(c_1209,plain,(
    ! [C_139,B_140] : r1_tarski(k1_xboole_0,k4_xboole_0(C_139,B_140)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1081,c_700])).

tff(c_1271,plain,(
    ! [C_141] : r1_tarski(k1_xboole_0,C_141) ),
    inference(resolution,[status(thm)],[c_1209,c_14])).

tff(c_20,plain,(
    ! [A_13,C_15,B_14] :
      ( r2_xboole_0(A_13,C_15)
      | ~ r1_tarski(B_14,C_15)
      | ~ r2_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1436,plain,(
    ! [A_155,C_156] :
      ( r2_xboole_0(A_155,C_156)
      | ~ r2_xboole_0(A_155,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1271,c_20])).

tff(c_3236,plain,(
    ! [A_241,C_242] :
      ( r2_xboole_0(A_241,C_242)
      | k1_xboole_0 = A_241
      | ~ r1_tarski(A_241,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2,c_1436])).

tff(c_4,plain,(
    ! [B_2] : ~ r2_xboole_0(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3288,plain,(
    ! [C_243] :
      ( k1_xboole_0 = C_243
      | ~ r1_tarski(C_243,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_3236,c_4])).

tff(c_3334,plain,(
    ! [A_244] :
      ( k1_xboole_0 = A_244
      | k4_xboole_0(A_244,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_3004,c_3288])).

tff(c_3375,plain,(
    ! [C_245] : k4_xboole_0('#skF_1',k2_tarski('#skF_2',C_245)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1755,c_3334])).

tff(c_593,plain,(
    ! [B_109,C_110,A_111] :
      ( k2_tarski(B_109,C_110) = A_111
      | k1_tarski(C_110) = A_111
      | k1_tarski(B_109) = A_111
      | k1_xboole_0 = A_111
      | ~ r1_tarski(A_111,k2_tarski(B_109,C_110)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_625,plain,(
    ! [B_109,C_110,A_3] :
      ( k2_tarski(B_109,C_110) = A_3
      | k1_tarski(C_110) = A_3
      | k1_tarski(B_109) = A_3
      | k1_xboole_0 = A_3
      | k4_xboole_0(A_3,k2_tarski(B_109,C_110)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_593])).

tff(c_3395,plain,(
    ! [C_245] :
      ( k2_tarski('#skF_2',C_245) = '#skF_1'
      | k1_tarski(C_245) = '#skF_1'
      | k1_tarski('#skF_2') = '#skF_1'
      | k1_xboole_0 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3375,c_625])).

tff(c_3568,plain,(
    ! [C_247] :
      ( k2_tarski('#skF_2',C_247) = '#skF_1'
      | k1_tarski(C_247) = '#skF_1' ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_3395])).

tff(c_296,plain,(
    ! [A_74,C_75,B_76] :
      ( r2_xboole_0(A_74,C_75)
      | ~ r1_tarski(B_76,C_75)
      | ~ r2_xboole_0(A_74,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1387,plain,(
    ! [A_144,B_145,C_146] :
      ( r2_xboole_0(A_144,k2_tarski(B_145,C_146))
      | ~ r2_xboole_0(A_144,k1_tarski(B_145)) ) ),
    inference(resolution,[status(thm)],[c_32,c_296])).

tff(c_1396,plain,(
    ! [B_145,C_146] : ~ r2_xboole_0(k2_tarski(B_145,C_146),k1_tarski(B_145)) ),
    inference(resolution,[status(thm)],[c_1387,c_4])).

tff(c_3594,plain,(
    ! [C_247] :
      ( ~ r2_xboole_0('#skF_1',k1_tarski('#skF_2'))
      | k1_tarski(C_247) = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3568,c_1396])).

tff(c_3914,plain,(
    ~ r2_xboole_0('#skF_1',k1_tarski('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_3594])).

tff(c_3917,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2,c_3914])).

tff(c_3920,plain,(
    ~ r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_3917])).

tff(c_3926,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_3920])).

tff(c_3931,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3926])).

tff(c_3932,plain,(
    ! [C_247] : k1_tarski(C_247) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3594])).

tff(c_3962,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3932,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:31:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.43/1.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.43/1.78  
% 4.43/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.43/1.78  %$ r2_xboole_0 > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 4.43/1.78  
% 4.43/1.78  %Foreground sorts:
% 4.43/1.78  
% 4.43/1.78  
% 4.43/1.78  %Background operators:
% 4.43/1.78  
% 4.43/1.78  
% 4.43/1.78  %Foreground operators:
% 4.43/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.43/1.78  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.43/1.78  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.43/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.43/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.43/1.78  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.43/1.78  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.43/1.78  tff('#skF_2', type, '#skF_2': $i).
% 4.43/1.78  tff('#skF_1', type, '#skF_1': $i).
% 4.43/1.78  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 4.43/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.43/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.43/1.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.43/1.78  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.43/1.78  
% 4.51/1.80  tff(f_91, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 4.51/1.80  tff(f_36, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.51/1.80  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 4.51/1.80  tff(f_81, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_zfmisc_1)).
% 4.51/1.80  tff(f_48, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_xboole_1)).
% 4.51/1.80  tff(f_44, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.51/1.80  tff(f_42, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 4.51/1.80  tff(f_54, axiom, (![A, B, C]: ((r2_xboole_0(A, B) & r1_tarski(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_xboole_1)).
% 4.51/1.80  tff(c_40, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.51/1.80  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.51/1.80  tff(c_36, plain, (k1_tarski('#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.51/1.80  tff(c_2, plain, (![A_1, B_2]: (r2_xboole_0(A_1, B_2) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.51/1.80  tff(c_38, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.51/1.80  tff(c_32, plain, (![B_20, C_21]: (r1_tarski(k1_tarski(B_20), k2_tarski(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.51/1.80  tff(c_392, plain, (![C_91, B_92, A_93]: (r1_tarski(k4_xboole_0(C_91, B_92), k4_xboole_0(C_91, A_93)) | ~r1_tarski(A_93, B_92))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.51/1.80  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.51/1.80  tff(c_1534, plain, (![C_165, B_166, A_167]: (k4_xboole_0(k4_xboole_0(C_165, B_166), k4_xboole_0(C_165, A_167))=k1_xboole_0 | ~r1_tarski(A_167, B_166))), inference(resolution, [status(thm)], [c_392, c_10])).
% 4.51/1.80  tff(c_1731, plain, (![B_171]: (k4_xboole_0(k4_xboole_0('#skF_1', B_171), k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_tarski('#skF_2'), B_171))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1534])).
% 4.51/1.80  tff(c_1755, plain, (![C_21]: (k4_xboole_0(k4_xboole_0('#skF_1', k2_tarski('#skF_2', C_21)), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_1731])).
% 4.51/1.80  tff(c_16, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.51/1.80  tff(c_184, plain, (![A_62, B_63, C_64]: (r1_tarski(A_62, B_63) | ~r1_tarski(A_62, k4_xboole_0(B_63, C_64)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.51/1.80  tff(c_209, plain, (![B_63, C_64, B_9]: (r1_tarski(k3_xboole_0(k4_xboole_0(B_63, C_64), B_9), B_63))), inference(resolution, [status(thm)], [c_16, c_184])).
% 4.51/1.80  tff(c_14, plain, (![A_5, B_6, C_7]: (r1_tarski(A_5, B_6) | ~r1_tarski(A_5, k4_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.51/1.80  tff(c_660, plain, (![C_117, B_118, A_119]: (r1_tarski(k4_xboole_0(C_117, B_118), C_117) | ~r1_tarski(A_119, B_118))), inference(resolution, [status(thm)], [c_392, c_14])).
% 4.51/1.80  tff(c_710, plain, (![C_120, B_121]: (r1_tarski(k4_xboole_0(C_120, B_121), C_120))), inference(resolution, [status(thm)], [c_209, c_660])).
% 4.51/1.80  tff(c_1081, plain, (![C_136, B_137]: (k4_xboole_0(k4_xboole_0(C_136, B_137), C_136)=k1_xboole_0)), inference(resolution, [status(thm)], [c_710, c_10])).
% 4.51/1.80  tff(c_2924, plain, (![A_223, C_224, B_225]: (r1_tarski(A_223, k4_xboole_0(C_224, B_225)) | ~r1_tarski(A_223, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1081, c_14])).
% 4.51/1.80  tff(c_2974, plain, (![A_226, C_227]: (r1_tarski(A_226, C_227) | ~r1_tarski(A_226, k1_xboole_0))), inference(resolution, [status(thm)], [c_2924, c_14])).
% 4.51/1.80  tff(c_3004, plain, (![A_3, C_227]: (r1_tarski(A_3, C_227) | k4_xboole_0(A_3, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_2974])).
% 4.51/1.80  tff(c_700, plain, (![C_117, B_63]: (r1_tarski(k4_xboole_0(C_117, B_63), C_117))), inference(resolution, [status(thm)], [c_209, c_660])).
% 4.51/1.80  tff(c_1209, plain, (![C_139, B_140]: (r1_tarski(k1_xboole_0, k4_xboole_0(C_139, B_140)))), inference(superposition, [status(thm), theory('equality')], [c_1081, c_700])).
% 4.51/1.80  tff(c_1271, plain, (![C_141]: (r1_tarski(k1_xboole_0, C_141))), inference(resolution, [status(thm)], [c_1209, c_14])).
% 4.51/1.80  tff(c_20, plain, (![A_13, C_15, B_14]: (r2_xboole_0(A_13, C_15) | ~r1_tarski(B_14, C_15) | ~r2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.51/1.80  tff(c_1436, plain, (![A_155, C_156]: (r2_xboole_0(A_155, C_156) | ~r2_xboole_0(A_155, k1_xboole_0))), inference(resolution, [status(thm)], [c_1271, c_20])).
% 4.51/1.80  tff(c_3236, plain, (![A_241, C_242]: (r2_xboole_0(A_241, C_242) | k1_xboole_0=A_241 | ~r1_tarski(A_241, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_1436])).
% 4.51/1.80  tff(c_4, plain, (![B_2]: (~r2_xboole_0(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.51/1.80  tff(c_3288, plain, (![C_243]: (k1_xboole_0=C_243 | ~r1_tarski(C_243, k1_xboole_0))), inference(resolution, [status(thm)], [c_3236, c_4])).
% 4.51/1.80  tff(c_3334, plain, (![A_244]: (k1_xboole_0=A_244 | k4_xboole_0(A_244, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_3004, c_3288])).
% 4.51/1.80  tff(c_3375, plain, (![C_245]: (k4_xboole_0('#skF_1', k2_tarski('#skF_2', C_245))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1755, c_3334])).
% 4.51/1.80  tff(c_593, plain, (![B_109, C_110, A_111]: (k2_tarski(B_109, C_110)=A_111 | k1_tarski(C_110)=A_111 | k1_tarski(B_109)=A_111 | k1_xboole_0=A_111 | ~r1_tarski(A_111, k2_tarski(B_109, C_110)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.51/1.80  tff(c_625, plain, (![B_109, C_110, A_3]: (k2_tarski(B_109, C_110)=A_3 | k1_tarski(C_110)=A_3 | k1_tarski(B_109)=A_3 | k1_xboole_0=A_3 | k4_xboole_0(A_3, k2_tarski(B_109, C_110))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_593])).
% 4.51/1.80  tff(c_3395, plain, (![C_245]: (k2_tarski('#skF_2', C_245)='#skF_1' | k1_tarski(C_245)='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3375, c_625])).
% 4.51/1.80  tff(c_3568, plain, (![C_247]: (k2_tarski('#skF_2', C_247)='#skF_1' | k1_tarski(C_247)='#skF_1')), inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_3395])).
% 4.51/1.80  tff(c_296, plain, (![A_74, C_75, B_76]: (r2_xboole_0(A_74, C_75) | ~r1_tarski(B_76, C_75) | ~r2_xboole_0(A_74, B_76))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.51/1.80  tff(c_1387, plain, (![A_144, B_145, C_146]: (r2_xboole_0(A_144, k2_tarski(B_145, C_146)) | ~r2_xboole_0(A_144, k1_tarski(B_145)))), inference(resolution, [status(thm)], [c_32, c_296])).
% 4.51/1.80  tff(c_1396, plain, (![B_145, C_146]: (~r2_xboole_0(k2_tarski(B_145, C_146), k1_tarski(B_145)))), inference(resolution, [status(thm)], [c_1387, c_4])).
% 4.51/1.80  tff(c_3594, plain, (![C_247]: (~r2_xboole_0('#skF_1', k1_tarski('#skF_2')) | k1_tarski(C_247)='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3568, c_1396])).
% 4.51/1.80  tff(c_3914, plain, (~r2_xboole_0('#skF_1', k1_tarski('#skF_2'))), inference(splitLeft, [status(thm)], [c_3594])).
% 4.51/1.80  tff(c_3917, plain, (k1_tarski('#skF_2')='#skF_1' | ~r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_2, c_3914])).
% 4.51/1.80  tff(c_3920, plain, (~r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_36, c_3917])).
% 4.51/1.80  tff(c_3926, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_3920])).
% 4.51/1.80  tff(c_3931, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_3926])).
% 4.51/1.80  tff(c_3932, plain, (![C_247]: (k1_tarski(C_247)='#skF_1')), inference(splitRight, [status(thm)], [c_3594])).
% 4.51/1.80  tff(c_3962, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3932, c_36])).
% 4.51/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.51/1.80  
% 4.51/1.80  Inference rules
% 4.51/1.80  ----------------------
% 4.51/1.80  #Ref     : 0
% 4.51/1.80  #Sup     : 984
% 4.51/1.80  #Fact    : 3
% 4.51/1.80  #Define  : 0
% 4.51/1.80  #Split   : 3
% 4.51/1.80  #Chain   : 0
% 4.51/1.80  #Close   : 0
% 4.51/1.80  
% 4.51/1.80  Ordering : KBO
% 4.51/1.80  
% 4.51/1.80  Simplification rules
% 4.51/1.80  ----------------------
% 4.51/1.80  #Subsume      : 161
% 4.51/1.80  #Demod        : 670
% 4.51/1.80  #Tautology    : 576
% 4.51/1.80  #SimpNegUnit  : 10
% 4.51/1.80  #BackRed      : 29
% 4.51/1.80  
% 4.51/1.80  #Partial instantiations: 0
% 4.51/1.80  #Strategies tried      : 1
% 4.51/1.80  
% 4.51/1.80  Timing (in seconds)
% 4.51/1.80  ----------------------
% 4.51/1.80  Preprocessing        : 0.29
% 4.51/1.80  Parsing              : 0.16
% 4.51/1.80  CNF conversion       : 0.02
% 4.51/1.80  Main loop            : 0.74
% 4.51/1.80  Inferencing          : 0.24
% 4.51/1.80  Reduction            : 0.27
% 4.51/1.80  Demodulation         : 0.20
% 4.51/1.80  BG Simplification    : 0.03
% 4.51/1.80  Subsumption          : 0.14
% 4.51/1.80  Abstraction          : 0.03
% 4.51/1.80  MUC search           : 0.00
% 4.51/1.80  Cooper               : 0.00
% 4.51/1.80  Total                : 1.06
% 4.51/1.80  Index Insertion      : 0.00
% 4.51/1.80  Index Deletion       : 0.00
% 4.51/1.80  Index Matching       : 0.00
% 4.51/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
