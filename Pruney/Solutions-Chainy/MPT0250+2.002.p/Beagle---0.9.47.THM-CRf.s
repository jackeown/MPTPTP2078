%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:32 EST 2020

% Result     : Theorem 4.09s
% Output     : CNFRefutation 4.39s
% Verified   : 
% Statistics : Number of formulae       :   51 (  63 expanded)
%              Number of leaves         :   30 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   43 (  56 expanded)
%              Number of equality atoms :   14 (  23 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_111,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_100,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_71,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_72,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_32,plain,(
    ! [A_28,B_29] : r1_tarski(A_28,k2_xboole_0(A_28,B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_38,plain,(
    ! [B_36,A_35] : k2_tarski(B_36,A_35) = k2_tarski(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_429,plain,(
    ! [A_111,B_112] : k3_tarski(k2_tarski(A_111,B_112)) = k2_xboole_0(A_111,B_112) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_458,plain,(
    ! [B_114,A_115] : k3_tarski(k2_tarski(B_114,A_115)) = k2_xboole_0(A_115,B_114) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_429])).

tff(c_64,plain,(
    ! [A_68,B_69] : k3_tarski(k2_tarski(A_68,B_69)) = k2_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_464,plain,(
    ! [B_114,A_115] : k2_xboole_0(B_114,A_115) = k2_xboole_0(A_115,B_114) ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_64])).

tff(c_74,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_1'),'#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_510,plain,(
    r1_tarski(k2_xboole_0('#skF_2',k1_tarski('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_74])).

tff(c_742,plain,(
    ! [A_131,B_132] :
      ( r2_xboole_0(A_131,B_132)
      | B_132 = A_131
      | ~ r1_tarski(A_131,B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_30,plain,(
    ! [B_27,A_26] :
      ( ~ r2_xboole_0(B_27,A_26)
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2331,plain,(
    ! [B_244,A_245] :
      ( ~ r1_tarski(B_244,A_245)
      | B_244 = A_245
      | ~ r1_tarski(A_245,B_244) ) ),
    inference(resolution,[status(thm)],[c_742,c_30])).

tff(c_2351,plain,
    ( k2_xboole_0('#skF_2',k1_tarski('#skF_1')) = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_xboole_0('#skF_2',k1_tarski('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_510,c_2331])).

tff(c_2381,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2351])).

tff(c_40,plain,(
    ! [A_37] : k2_tarski(A_37,A_37) = k1_tarski(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_969,plain,(
    ! [A_144,C_145,B_146] :
      ( r2_hidden(A_144,C_145)
      | ~ r1_tarski(k2_tarski(A_144,B_146),C_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1057,plain,(
    ! [A_155,C_156] :
      ( r2_hidden(A_155,C_156)
      | ~ r1_tarski(k1_tarski(A_155),C_156) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_969])).

tff(c_1089,plain,(
    ! [A_157,B_158] : r2_hidden(A_157,k2_xboole_0(k1_tarski(A_157),B_158)) ),
    inference(resolution,[status(thm)],[c_32,c_1057])).

tff(c_1093,plain,(
    ! [A_157,B_114] : r2_hidden(A_157,k2_xboole_0(B_114,k1_tarski(A_157))) ),
    inference(superposition,[status(thm),theory(equality)],[c_464,c_1089])).

tff(c_2408,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2381,c_1093])).

tff(c_2438,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2408])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:01:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.09/1.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.09/1.76  
% 4.09/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.09/1.76  %$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 4.09/1.76  
% 4.09/1.76  %Foreground sorts:
% 4.09/1.76  
% 4.09/1.76  
% 4.09/1.76  %Background operators:
% 4.09/1.76  
% 4.09/1.76  
% 4.09/1.76  %Foreground operators:
% 4.09/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.09/1.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.09/1.76  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.09/1.76  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.09/1.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.09/1.76  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.09/1.76  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.09/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.09/1.76  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.09/1.76  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.09/1.76  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.09/1.76  tff('#skF_2', type, '#skF_2': $i).
% 4.09/1.76  tff('#skF_1', type, '#skF_1': $i).
% 4.09/1.76  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.09/1.76  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 4.09/1.76  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.09/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.09/1.76  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.09/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.09/1.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.09/1.76  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.09/1.76  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.09/1.76  
% 4.39/1.77  tff(f_111, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 4.39/1.77  tff(f_63, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.39/1.77  tff(f_69, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.39/1.77  tff(f_100, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.39/1.77  tff(f_36, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 4.39/1.77  tff(f_61, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_xboole_1)).
% 4.39/1.77  tff(f_71, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.39/1.77  tff(f_106, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 4.39/1.77  tff(c_72, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.39/1.77  tff(c_32, plain, (![A_28, B_29]: (r1_tarski(A_28, k2_xboole_0(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.39/1.77  tff(c_38, plain, (![B_36, A_35]: (k2_tarski(B_36, A_35)=k2_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.39/1.77  tff(c_429, plain, (![A_111, B_112]: (k3_tarski(k2_tarski(A_111, B_112))=k2_xboole_0(A_111, B_112))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.39/1.77  tff(c_458, plain, (![B_114, A_115]: (k3_tarski(k2_tarski(B_114, A_115))=k2_xboole_0(A_115, B_114))), inference(superposition, [status(thm), theory('equality')], [c_38, c_429])).
% 4.39/1.77  tff(c_64, plain, (![A_68, B_69]: (k3_tarski(k2_tarski(A_68, B_69))=k2_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.39/1.77  tff(c_464, plain, (![B_114, A_115]: (k2_xboole_0(B_114, A_115)=k2_xboole_0(A_115, B_114))), inference(superposition, [status(thm), theory('equality')], [c_458, c_64])).
% 4.39/1.77  tff(c_74, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.39/1.77  tff(c_510, plain, (r1_tarski(k2_xboole_0('#skF_2', k1_tarski('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_464, c_74])).
% 4.39/1.77  tff(c_742, plain, (![A_131, B_132]: (r2_xboole_0(A_131, B_132) | B_132=A_131 | ~r1_tarski(A_131, B_132))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.39/1.77  tff(c_30, plain, (![B_27, A_26]: (~r2_xboole_0(B_27, A_26) | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.39/1.77  tff(c_2331, plain, (![B_244, A_245]: (~r1_tarski(B_244, A_245) | B_244=A_245 | ~r1_tarski(A_245, B_244))), inference(resolution, [status(thm)], [c_742, c_30])).
% 4.39/1.77  tff(c_2351, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))='#skF_2' | ~r1_tarski('#skF_2', k2_xboole_0('#skF_2', k1_tarski('#skF_1')))), inference(resolution, [status(thm)], [c_510, c_2331])).
% 4.39/1.77  tff(c_2381, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2351])).
% 4.39/1.77  tff(c_40, plain, (![A_37]: (k2_tarski(A_37, A_37)=k1_tarski(A_37))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.39/1.77  tff(c_969, plain, (![A_144, C_145, B_146]: (r2_hidden(A_144, C_145) | ~r1_tarski(k2_tarski(A_144, B_146), C_145))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.39/1.77  tff(c_1057, plain, (![A_155, C_156]: (r2_hidden(A_155, C_156) | ~r1_tarski(k1_tarski(A_155), C_156))), inference(superposition, [status(thm), theory('equality')], [c_40, c_969])).
% 4.39/1.77  tff(c_1089, plain, (![A_157, B_158]: (r2_hidden(A_157, k2_xboole_0(k1_tarski(A_157), B_158)))), inference(resolution, [status(thm)], [c_32, c_1057])).
% 4.39/1.77  tff(c_1093, plain, (![A_157, B_114]: (r2_hidden(A_157, k2_xboole_0(B_114, k1_tarski(A_157))))), inference(superposition, [status(thm), theory('equality')], [c_464, c_1089])).
% 4.39/1.77  tff(c_2408, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2381, c_1093])).
% 4.39/1.77  tff(c_2438, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_2408])).
% 4.39/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.39/1.77  
% 4.39/1.77  Inference rules
% 4.39/1.77  ----------------------
% 4.39/1.77  #Ref     : 0
% 4.39/1.77  #Sup     : 574
% 4.39/1.77  #Fact    : 0
% 4.39/1.77  #Define  : 0
% 4.39/1.77  #Split   : 0
% 4.39/1.77  #Chain   : 0
% 4.39/1.77  #Close   : 0
% 4.39/1.77  
% 4.39/1.77  Ordering : KBO
% 4.39/1.77  
% 4.39/1.77  Simplification rules
% 4.39/1.77  ----------------------
% 4.39/1.77  #Subsume      : 10
% 4.39/1.77  #Demod        : 286
% 4.39/1.77  #Tautology    : 386
% 4.39/1.77  #SimpNegUnit  : 1
% 4.39/1.77  #BackRed      : 2
% 4.39/1.77  
% 4.39/1.77  #Partial instantiations: 0
% 4.42/1.77  #Strategies tried      : 1
% 4.42/1.77  
% 4.42/1.77  Timing (in seconds)
% 4.42/1.77  ----------------------
% 4.42/1.77  Preprocessing        : 0.38
% 4.42/1.77  Parsing              : 0.20
% 4.42/1.77  CNF conversion       : 0.03
% 4.42/1.77  Main loop            : 0.61
% 4.42/1.77  Inferencing          : 0.20
% 4.42/1.77  Reduction            : 0.25
% 4.42/1.77  Demodulation         : 0.20
% 4.42/1.77  BG Simplification    : 0.03
% 4.42/1.77  Subsumption          : 0.09
% 4.42/1.77  Abstraction          : 0.03
% 4.42/1.77  MUC search           : 0.00
% 4.42/1.77  Cooper               : 0.00
% 4.42/1.77  Total                : 1.02
% 4.42/1.77  Index Insertion      : 0.00
% 4.42/1.77  Index Deletion       : 0.00
% 4.42/1.77  Index Matching       : 0.00
% 4.42/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
