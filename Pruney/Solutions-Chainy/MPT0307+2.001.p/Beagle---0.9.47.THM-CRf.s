%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:52 EST 2020

% Result     : Theorem 5.26s
% Output     : CNFRefutation 5.26s
% Verified   : 
% Statistics : Number of formulae       :   29 (  32 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  45 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_14,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8,plain,(
    ! [C_10,A_8,B_9] :
      ( r1_tarski(k2_zfmisc_1(C_10,A_8),k2_zfmisc_1(C_10,B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_132,plain,(
    ! [A_23,C_24,B_25] :
      ( r1_tarski(k2_zfmisc_1(A_23,C_24),k2_zfmisc_1(B_25,C_24))
      | ~ r1_tarski(A_23,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_556,plain,(
    ! [A_54,C_55,B_56] :
      ( k2_xboole_0(k2_zfmisc_1(A_54,C_55),k2_zfmisc_1(B_56,C_55)) = k2_zfmisc_1(B_56,C_55)
      | ~ r1_tarski(A_54,B_56) ) ),
    inference(resolution,[status(thm)],[c_132,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_86,plain,(
    ! [A_15,C_16,B_17] :
      ( r1_tarski(A_15,k2_xboole_0(C_16,B_17))
      | ~ r1_tarski(A_15,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_101,plain,(
    ! [A_15,B_2,A_1] :
      ( r1_tarski(A_15,k2_xboole_0(B_2,A_1))
      | ~ r1_tarski(A_15,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_86])).

tff(c_2914,plain,(
    ! [A_124,B_125,C_126,A_127] :
      ( r1_tarski(A_124,k2_zfmisc_1(B_125,C_126))
      | ~ r1_tarski(A_124,k2_zfmisc_1(A_127,C_126))
      | ~ r1_tarski(A_127,B_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_556,c_101])).

tff(c_4370,plain,(
    ! [C_197,A_198,B_199,B_200] :
      ( r1_tarski(k2_zfmisc_1(C_197,A_198),k2_zfmisc_1(B_199,B_200))
      | ~ r1_tarski(C_197,B_199)
      | ~ r1_tarski(A_198,B_200) ) ),
    inference(resolution,[status(thm)],[c_8,c_2914])).

tff(c_12,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_3'),k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4387,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_4370,c_12])).

tff(c_4401,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16,c_4387])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:12:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.26/2.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.26/2.05  
% 5.26/2.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.26/2.06  %$ r1_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.26/2.06  
% 5.26/2.06  %Foreground sorts:
% 5.26/2.06  
% 5.26/2.06  
% 5.26/2.06  %Background operators:
% 5.26/2.06  
% 5.26/2.06  
% 5.26/2.06  %Foreground operators:
% 5.26/2.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.26/2.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.26/2.06  tff('#skF_2', type, '#skF_2': $i).
% 5.26/2.06  tff('#skF_3', type, '#skF_3': $i).
% 5.26/2.06  tff('#skF_1', type, '#skF_1': $i).
% 5.26/2.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.26/2.06  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.26/2.06  tff('#skF_4', type, '#skF_4': $i).
% 5.26/2.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.26/2.06  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.26/2.06  
% 5.26/2.06  tff(f_48, negated_conjecture, ~(![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_zfmisc_1)).
% 5.26/2.06  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 5.26/2.06  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.26/2.06  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.26/2.06  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 5.26/2.06  tff(c_14, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.26/2.06  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.26/2.06  tff(c_8, plain, (![C_10, A_8, B_9]: (r1_tarski(k2_zfmisc_1(C_10, A_8), k2_zfmisc_1(C_10, B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.26/2.06  tff(c_132, plain, (![A_23, C_24, B_25]: (r1_tarski(k2_zfmisc_1(A_23, C_24), k2_zfmisc_1(B_25, C_24)) | ~r1_tarski(A_23, B_25))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.26/2.06  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.26/2.06  tff(c_556, plain, (![A_54, C_55, B_56]: (k2_xboole_0(k2_zfmisc_1(A_54, C_55), k2_zfmisc_1(B_56, C_55))=k2_zfmisc_1(B_56, C_55) | ~r1_tarski(A_54, B_56))), inference(resolution, [status(thm)], [c_132, c_6])).
% 5.26/2.06  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.26/2.06  tff(c_86, plain, (![A_15, C_16, B_17]: (r1_tarski(A_15, k2_xboole_0(C_16, B_17)) | ~r1_tarski(A_15, B_17))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.26/2.06  tff(c_101, plain, (![A_15, B_2, A_1]: (r1_tarski(A_15, k2_xboole_0(B_2, A_1)) | ~r1_tarski(A_15, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_86])).
% 5.26/2.06  tff(c_2914, plain, (![A_124, B_125, C_126, A_127]: (r1_tarski(A_124, k2_zfmisc_1(B_125, C_126)) | ~r1_tarski(A_124, k2_zfmisc_1(A_127, C_126)) | ~r1_tarski(A_127, B_125))), inference(superposition, [status(thm), theory('equality')], [c_556, c_101])).
% 5.26/2.06  tff(c_4370, plain, (![C_197, A_198, B_199, B_200]: (r1_tarski(k2_zfmisc_1(C_197, A_198), k2_zfmisc_1(B_199, B_200)) | ~r1_tarski(C_197, B_199) | ~r1_tarski(A_198, B_200))), inference(resolution, [status(thm)], [c_8, c_2914])).
% 5.26/2.06  tff(c_12, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_3'), k2_zfmisc_1('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.26/2.06  tff(c_4387, plain, (~r1_tarski('#skF_1', '#skF_2') | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_4370, c_12])).
% 5.26/2.06  tff(c_4401, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_16, c_4387])).
% 5.26/2.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.26/2.06  
% 5.26/2.06  Inference rules
% 5.26/2.06  ----------------------
% 5.26/2.06  #Ref     : 0
% 5.26/2.06  #Sup     : 1334
% 5.26/2.06  #Fact    : 0
% 5.26/2.06  #Define  : 0
% 5.26/2.06  #Split   : 5
% 5.26/2.06  #Chain   : 0
% 5.26/2.06  #Close   : 0
% 5.26/2.06  
% 5.26/2.06  Ordering : KBO
% 5.26/2.06  
% 5.26/2.06  Simplification rules
% 5.26/2.06  ----------------------
% 5.26/2.06  #Subsume      : 416
% 5.26/2.06  #Demod        : 230
% 5.26/2.06  #Tautology    : 188
% 5.26/2.06  #SimpNegUnit  : 0
% 5.26/2.06  #BackRed      : 0
% 5.26/2.06  
% 5.26/2.06  #Partial instantiations: 0
% 5.26/2.06  #Strategies tried      : 1
% 5.26/2.06  
% 5.26/2.06  Timing (in seconds)
% 5.26/2.06  ----------------------
% 5.26/2.07  Preprocessing        : 0.25
% 5.26/2.07  Parsing              : 0.14
% 5.26/2.07  CNF conversion       : 0.02
% 5.26/2.07  Main loop            : 1.06
% 5.26/2.07  Inferencing          : 0.33
% 5.26/2.07  Reduction            : 0.35
% 5.26/2.07  Demodulation         : 0.27
% 5.26/2.07  BG Simplification    : 0.05
% 5.26/2.07  Subsumption          : 0.28
% 5.66/2.07  Abstraction          : 0.05
% 5.66/2.07  MUC search           : 0.00
% 5.66/2.07  Cooper               : 0.00
% 5.66/2.07  Total                : 1.33
% 5.66/2.07  Index Insertion      : 0.00
% 5.66/2.07  Index Deletion       : 0.00
% 5.66/2.07  Index Matching       : 0.00
% 5.66/2.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
