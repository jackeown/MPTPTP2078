%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:35 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :   52 (  57 expanded)
%              Number of leaves         :   33 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   49 (  59 expanded)
%              Number of equality atoms :   26 (  33 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_128,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_118,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_78,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_76,plain,(
    '#skF_5' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_72,plain,(
    ! [B_63,C_64] : r1_tarski(k1_tarski(B_63),k2_tarski(B_63,C_64)) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_80,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_168,plain,(
    ! [A_85,B_86] :
      ( k3_xboole_0(A_85,B_86) = A_85
      | ~ r1_tarski(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_192,plain,(
    k3_xboole_0(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) = k2_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_168])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_557,plain,(
    ! [A_115,B_116,C_117] :
      ( r1_tarski(A_115,B_116)
      | ~ r1_tarski(A_115,k3_xboole_0(B_116,C_117)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_602,plain,(
    ! [A_121,A_122,B_123] :
      ( r1_tarski(A_121,A_122)
      | ~ r1_tarski(A_121,k3_xboole_0(B_123,A_122)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_557])).

tff(c_739,plain,(
    ! [A_133] :
      ( r1_tarski(A_133,k2_tarski('#skF_7','#skF_8'))
      | ~ r1_tarski(A_133,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_602])).

tff(c_16,plain,(
    ! [A_17,B_18] :
      ( k3_xboole_0(A_17,B_18) = A_17
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2289,plain,(
    ! [A_226] :
      ( k3_xboole_0(A_226,k2_tarski('#skF_7','#skF_8')) = A_226
      | ~ r1_tarski(A_226,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_739,c_16])).

tff(c_2318,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_7','#skF_8')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_2289])).

tff(c_874,plain,(
    ! [B_142,A_143] :
      ( r2_hidden(B_142,A_143)
      | k3_xboole_0(A_143,k1_tarski(B_142)) != k1_tarski(B_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_886,plain,(
    ! [B_142,B_2] :
      ( r2_hidden(B_142,B_2)
      | k3_xboole_0(k1_tarski(B_142),B_2) != k1_tarski(B_142) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_874])).

tff(c_2397,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2318,c_886])).

tff(c_24,plain,(
    ! [D_28,B_24,A_23] :
      ( D_28 = B_24
      | D_28 = A_23
      | ~ r2_hidden(D_28,k2_tarski(A_23,B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2404,plain,
    ( '#skF_5' = '#skF_8'
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_2397,c_24])).

tff(c_2408,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_76,c_2404])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:58:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.77/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.65  
% 3.77/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.65  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_1
% 3.77/1.65  
% 3.77/1.65  %Foreground sorts:
% 3.77/1.65  
% 3.77/1.65  
% 3.77/1.65  %Background operators:
% 3.77/1.65  
% 3.77/1.65  
% 3.77/1.65  %Foreground operators:
% 3.77/1.65  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.77/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.77/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.77/1.65  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.77/1.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.77/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.77/1.65  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.77/1.65  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.77/1.65  tff('#skF_7', type, '#skF_7': $i).
% 3.77/1.65  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.77/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.77/1.65  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.77/1.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.77/1.65  tff('#skF_5', type, '#skF_5': $i).
% 3.77/1.65  tff('#skF_6', type, '#skF_6': $i).
% 3.77/1.65  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.77/1.65  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.77/1.65  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.77/1.65  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.77/1.65  tff('#skF_8', type, '#skF_8': $i).
% 3.77/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.77/1.65  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.77/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.77/1.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.77/1.65  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.77/1.65  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.77/1.65  
% 3.77/1.66  tff(f_128, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 3.77/1.66  tff(f_118, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 3.77/1.66  tff(f_61, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.77/1.66  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.77/1.66  tff(f_57, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 3.77/1.66  tff(f_94, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 3.77/1.66  tff(f_76, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 3.77/1.66  tff(c_78, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.77/1.66  tff(c_76, plain, ('#skF_5'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.77/1.66  tff(c_72, plain, (![B_63, C_64]: (r1_tarski(k1_tarski(B_63), k2_tarski(B_63, C_64)))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.77/1.66  tff(c_80, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.77/1.66  tff(c_168, plain, (![A_85, B_86]: (k3_xboole_0(A_85, B_86)=A_85 | ~r1_tarski(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.77/1.66  tff(c_192, plain, (k3_xboole_0(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))=k2_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_80, c_168])).
% 3.77/1.66  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.77/1.66  tff(c_557, plain, (![A_115, B_116, C_117]: (r1_tarski(A_115, B_116) | ~r1_tarski(A_115, k3_xboole_0(B_116, C_117)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.77/1.66  tff(c_602, plain, (![A_121, A_122, B_123]: (r1_tarski(A_121, A_122) | ~r1_tarski(A_121, k3_xboole_0(B_123, A_122)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_557])).
% 3.77/1.66  tff(c_739, plain, (![A_133]: (r1_tarski(A_133, k2_tarski('#skF_7', '#skF_8')) | ~r1_tarski(A_133, k2_tarski('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_192, c_602])).
% 3.77/1.66  tff(c_16, plain, (![A_17, B_18]: (k3_xboole_0(A_17, B_18)=A_17 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.77/1.66  tff(c_2289, plain, (![A_226]: (k3_xboole_0(A_226, k2_tarski('#skF_7', '#skF_8'))=A_226 | ~r1_tarski(A_226, k2_tarski('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_739, c_16])).
% 3.77/1.66  tff(c_2318, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_7', '#skF_8'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_72, c_2289])).
% 3.77/1.66  tff(c_874, plain, (![B_142, A_143]: (r2_hidden(B_142, A_143) | k3_xboole_0(A_143, k1_tarski(B_142))!=k1_tarski(B_142))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.77/1.66  tff(c_886, plain, (![B_142, B_2]: (r2_hidden(B_142, B_2) | k3_xboole_0(k1_tarski(B_142), B_2)!=k1_tarski(B_142))), inference(superposition, [status(thm), theory('equality')], [c_2, c_874])).
% 3.77/1.66  tff(c_2397, plain, (r2_hidden('#skF_5', k2_tarski('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2318, c_886])).
% 3.77/1.66  tff(c_24, plain, (![D_28, B_24, A_23]: (D_28=B_24 | D_28=A_23 | ~r2_hidden(D_28, k2_tarski(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.77/1.66  tff(c_2404, plain, ('#skF_5'='#skF_8' | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_2397, c_24])).
% 3.77/1.66  tff(c_2408, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_76, c_2404])).
% 3.77/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.66  
% 3.77/1.66  Inference rules
% 3.77/1.66  ----------------------
% 3.77/1.66  #Ref     : 0
% 3.77/1.66  #Sup     : 562
% 3.77/1.66  #Fact    : 0
% 3.77/1.66  #Define  : 0
% 3.77/1.66  #Split   : 2
% 3.77/1.66  #Chain   : 0
% 3.77/1.66  #Close   : 0
% 3.77/1.66  
% 3.77/1.66  Ordering : KBO
% 3.77/1.66  
% 3.77/1.66  Simplification rules
% 3.77/1.66  ----------------------
% 3.77/1.66  #Subsume      : 110
% 3.77/1.66  #Demod        : 327
% 3.77/1.66  #Tautology    : 277
% 3.77/1.66  #SimpNegUnit  : 43
% 3.77/1.66  #BackRed      : 2
% 3.77/1.66  
% 3.77/1.66  #Partial instantiations: 0
% 3.77/1.66  #Strategies tried      : 1
% 3.77/1.66  
% 3.77/1.66  Timing (in seconds)
% 3.77/1.66  ----------------------
% 3.77/1.66  Preprocessing        : 0.33
% 3.77/1.66  Parsing              : 0.17
% 3.77/1.66  CNF conversion       : 0.02
% 3.77/1.66  Main loop            : 0.56
% 3.77/1.66  Inferencing          : 0.18
% 3.77/1.66  Reduction            : 0.22
% 3.77/1.66  Demodulation         : 0.17
% 3.77/1.66  BG Simplification    : 0.03
% 3.77/1.66  Subsumption          : 0.10
% 3.77/1.66  Abstraction          : 0.03
% 3.77/1.66  MUC search           : 0.00
% 3.77/1.67  Cooper               : 0.00
% 3.77/1.67  Total                : 0.92
% 3.77/1.67  Index Insertion      : 0.00
% 3.77/1.67  Index Deletion       : 0.00
% 3.77/1.67  Index Matching       : 0.00
% 3.77/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
