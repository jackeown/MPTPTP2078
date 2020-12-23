%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:22 EST 2020

% Result     : Theorem 6.08s
% Output     : CNFRefutation 6.08s
% Verified   : 
% Statistics : Number of formulae       :   45 (  68 expanded)
%              Number of leaves         :   26 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   47 (  81 expanded)
%              Number of equality atoms :   31 (  50 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_40,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_86,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_68,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_84,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_24,plain,(
    ! [A_9] : k3_xboole_0(A_9,A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_145,plain,(
    ! [B_60,A_61] :
      ( r2_hidden(B_60,A_61)
      | k3_xboole_0(A_61,k1_tarski(B_60)) != k1_tarski(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_150,plain,(
    ! [B_60] : r2_hidden(B_60,k1_tarski(B_60)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_145])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r1_xboole_0(A_7,B_8)
      | k3_xboole_0(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_135,plain,(
    ! [A_55,B_56,C_57] :
      ( ~ r1_xboole_0(A_55,B_56)
      | ~ r2_hidden(C_57,k3_xboole_0(A_55,B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_139,plain,(
    ! [A_58,C_59] :
      ( ~ r1_xboole_0(A_58,A_58)
      | ~ r2_hidden(C_59,A_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_135])).

tff(c_142,plain,(
    ! [C_59,B_8] :
      ( ~ r2_hidden(C_59,B_8)
      | k3_xboole_0(B_8,B_8) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_139])).

tff(c_153,plain,(
    ! [C_63,B_64] :
      ( ~ r2_hidden(C_63,B_64)
      | k1_xboole_0 != B_64 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_142])).

tff(c_157,plain,(
    ! [B_60] : k1_tarski(B_60) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_150,c_153])).

tff(c_50,plain,(
    ! [A_32] : k1_setfam_1(k1_tarski(A_32)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_42,plain,(
    ! [A_25,B_26] : k2_xboole_0(k1_tarski(A_25),k1_tarski(B_26)) = k2_tarski(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_579,plain,(
    ! [A_99,B_100] :
      ( k3_xboole_0(k1_setfam_1(A_99),k1_setfam_1(B_100)) = k1_setfam_1(k2_xboole_0(A_99,B_100))
      | k1_xboole_0 = B_100
      | k1_xboole_0 = A_99 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_629,plain,(
    ! [A_32,B_100] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_32),B_100)) = k3_xboole_0(A_32,k1_setfam_1(B_100))
      | k1_xboole_0 = B_100
      | k1_tarski(A_32) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_579])).

tff(c_5936,plain,(
    ! [A_266,B_267] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_266),B_267)) = k3_xboole_0(A_266,k1_setfam_1(B_267))
      | k1_xboole_0 = B_267 ) ),
    inference(negUnitSimplification,[status(thm)],[c_157,c_629])).

tff(c_5959,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,k1_setfam_1(k1_tarski(B_26))) = k1_setfam_1(k2_tarski(A_25,B_26))
      | k1_tarski(B_26) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_5936])).

tff(c_5966,plain,(
    ! [A_25,B_26] :
      ( k1_setfam_1(k2_tarski(A_25,B_26)) = k3_xboole_0(A_25,B_26)
      | k1_tarski(B_26) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_5959])).

tff(c_5967,plain,(
    ! [A_25,B_26] : k1_setfam_1(k2_tarski(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(negUnitSimplification,[status(thm)],[c_157,c_5966])).

tff(c_52,plain,(
    k1_setfam_1(k2_tarski('#skF_4','#skF_5')) != k3_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_5970,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5967,c_52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:41:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.08/2.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.08/2.72  
% 6.08/2.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.08/2.72  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 6.08/2.72  
% 6.08/2.72  %Foreground sorts:
% 6.08/2.72  
% 6.08/2.72  
% 6.08/2.72  %Background operators:
% 6.08/2.72  
% 6.08/2.72  
% 6.08/2.72  %Foreground operators:
% 6.08/2.72  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.08/2.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.08/2.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.08/2.72  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.08/2.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.08/2.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.08/2.72  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.08/2.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.08/2.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.08/2.72  tff('#skF_5', type, '#skF_5': $i).
% 6.08/2.72  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.08/2.72  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.08/2.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.08/2.72  tff('#skF_4', type, '#skF_4': $i).
% 6.08/2.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.08/2.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.08/2.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.08/2.72  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.08/2.72  
% 6.08/2.73  tff(f_40, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 6.08/2.73  tff(f_74, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 6.08/2.73  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 6.08/2.73  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.08/2.73  tff(f_86, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 6.08/2.73  tff(f_68, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 6.08/2.73  tff(f_84, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_setfam_1)).
% 6.08/2.73  tff(f_89, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 6.08/2.73  tff(c_24, plain, (![A_9]: (k3_xboole_0(A_9, A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.08/2.73  tff(c_145, plain, (![B_60, A_61]: (r2_hidden(B_60, A_61) | k3_xboole_0(A_61, k1_tarski(B_60))!=k1_tarski(B_60))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.08/2.73  tff(c_150, plain, (![B_60]: (r2_hidden(B_60, k1_tarski(B_60)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_145])).
% 6.08/2.73  tff(c_22, plain, (![A_7, B_8]: (r1_xboole_0(A_7, B_8) | k3_xboole_0(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.08/2.73  tff(c_135, plain, (![A_55, B_56, C_57]: (~r1_xboole_0(A_55, B_56) | ~r2_hidden(C_57, k3_xboole_0(A_55, B_56)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.08/2.73  tff(c_139, plain, (![A_58, C_59]: (~r1_xboole_0(A_58, A_58) | ~r2_hidden(C_59, A_58))), inference(superposition, [status(thm), theory('equality')], [c_24, c_135])).
% 6.08/2.73  tff(c_142, plain, (![C_59, B_8]: (~r2_hidden(C_59, B_8) | k3_xboole_0(B_8, B_8)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_139])).
% 6.08/2.73  tff(c_153, plain, (![C_63, B_64]: (~r2_hidden(C_63, B_64) | k1_xboole_0!=B_64)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_142])).
% 6.08/2.73  tff(c_157, plain, (![B_60]: (k1_tarski(B_60)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_150, c_153])).
% 6.08/2.73  tff(c_50, plain, (![A_32]: (k1_setfam_1(k1_tarski(A_32))=A_32)), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.08/2.73  tff(c_42, plain, (![A_25, B_26]: (k2_xboole_0(k1_tarski(A_25), k1_tarski(B_26))=k2_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.08/2.73  tff(c_579, plain, (![A_99, B_100]: (k3_xboole_0(k1_setfam_1(A_99), k1_setfam_1(B_100))=k1_setfam_1(k2_xboole_0(A_99, B_100)) | k1_xboole_0=B_100 | k1_xboole_0=A_99)), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.08/2.73  tff(c_629, plain, (![A_32, B_100]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_32), B_100))=k3_xboole_0(A_32, k1_setfam_1(B_100)) | k1_xboole_0=B_100 | k1_tarski(A_32)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_50, c_579])).
% 6.08/2.73  tff(c_5936, plain, (![A_266, B_267]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_266), B_267))=k3_xboole_0(A_266, k1_setfam_1(B_267)) | k1_xboole_0=B_267)), inference(negUnitSimplification, [status(thm)], [c_157, c_629])).
% 6.08/2.73  tff(c_5959, plain, (![A_25, B_26]: (k3_xboole_0(A_25, k1_setfam_1(k1_tarski(B_26)))=k1_setfam_1(k2_tarski(A_25, B_26)) | k1_tarski(B_26)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_42, c_5936])).
% 6.08/2.73  tff(c_5966, plain, (![A_25, B_26]: (k1_setfam_1(k2_tarski(A_25, B_26))=k3_xboole_0(A_25, B_26) | k1_tarski(B_26)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_5959])).
% 6.08/2.73  tff(c_5967, plain, (![A_25, B_26]: (k1_setfam_1(k2_tarski(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(negUnitSimplification, [status(thm)], [c_157, c_5966])).
% 6.08/2.73  tff(c_52, plain, (k1_setfam_1(k2_tarski('#skF_4', '#skF_5'))!=k3_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.08/2.73  tff(c_5970, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5967, c_52])).
% 6.08/2.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.08/2.73  
% 6.08/2.73  Inference rules
% 6.08/2.73  ----------------------
% 6.08/2.73  #Ref     : 7
% 6.08/2.73  #Sup     : 1526
% 6.08/2.73  #Fact    : 0
% 6.08/2.73  #Define  : 0
% 6.08/2.73  #Split   : 3
% 6.08/2.73  #Chain   : 0
% 6.08/2.73  #Close   : 0
% 6.08/2.73  
% 6.08/2.73  Ordering : KBO
% 6.08/2.73  
% 6.08/2.73  Simplification rules
% 6.08/2.73  ----------------------
% 6.08/2.73  #Subsume      : 635
% 6.08/2.73  #Demod        : 476
% 6.08/2.73  #Tautology    : 445
% 6.08/2.73  #SimpNegUnit  : 42
% 6.08/2.73  #BackRed      : 12
% 6.08/2.73  
% 6.08/2.73  #Partial instantiations: 0
% 6.08/2.73  #Strategies tried      : 1
% 6.08/2.73  
% 6.08/2.73  Timing (in seconds)
% 6.08/2.73  ----------------------
% 6.08/2.73  Preprocessing        : 0.51
% 6.08/2.73  Parsing              : 0.26
% 6.08/2.73  CNF conversion       : 0.04
% 6.08/2.73  Main loop            : 1.32
% 6.08/2.73  Inferencing          : 0.45
% 6.08/2.73  Reduction            : 0.46
% 6.08/2.73  Demodulation         : 0.34
% 6.08/2.73  BG Simplification    : 0.06
% 6.08/2.73  Subsumption          : 0.27
% 6.08/2.73  Abstraction          : 0.07
% 6.08/2.73  MUC search           : 0.00
% 6.08/2.73  Cooper               : 0.00
% 6.08/2.73  Total                : 1.87
% 6.08/2.73  Index Insertion      : 0.00
% 6.08/2.73  Index Deletion       : 0.00
% 6.08/2.73  Index Matching       : 0.00
% 6.08/2.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
