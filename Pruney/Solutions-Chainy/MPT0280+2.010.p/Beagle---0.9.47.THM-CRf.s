%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:25 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   41 (  54 expanded)
%              Number of leaves         :   23 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   43 (  69 expanded)
%              Number of equality atoms :    3 (   5 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k2_xboole_0(k1_zfmisc_1(A),k1_zfmisc_1(B)),k1_zfmisc_1(k2_xboole_0(A,B))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_zfmisc_1)).

tff(c_14,plain,(
    ! [A_12,B_13] : r1_tarski(A_12,k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(k1_zfmisc_1(A_27),k1_zfmisc_1(B_28))
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,k2_xboole_0(C_8,B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(k4_xboole_0(A_3,C_5),B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_96,plain,(
    ! [A_53,C_54,B_55] :
      ( r1_tarski(k5_xboole_0(A_53,C_54),B_55)
      | ~ r1_tarski(C_54,B_55)
      | ~ r1_tarski(A_53,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_187,plain,(
    ! [A_72,B_73,B_74] :
      ( r1_tarski(k2_xboole_0(A_72,B_73),B_74)
      | ~ r1_tarski(k4_xboole_0(B_73,A_72),B_74)
      | ~ r1_tarski(A_72,B_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_96])).

tff(c_207,plain,(
    ! [C_75,A_76,B_77] :
      ( r1_tarski(k2_xboole_0(C_75,A_76),B_77)
      | ~ r1_tarski(C_75,B_77)
      | ~ r1_tarski(A_76,B_77) ) ),
    inference(resolution,[status(thm)],[c_8,c_187])).

tff(c_28,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1('#skF_1'),k1_zfmisc_1('#skF_2')),k1_zfmisc_1(k2_xboole_0('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_239,plain,
    ( ~ r1_tarski(k1_zfmisc_1('#skF_1'),k1_zfmisc_1(k2_xboole_0('#skF_1','#skF_2')))
    | ~ r1_tarski(k1_zfmisc_1('#skF_2'),k1_zfmisc_1(k2_xboole_0('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_207,c_28])).

tff(c_948,plain,(
    ~ r1_tarski(k1_zfmisc_1('#skF_2'),k1_zfmisc_1(k2_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_239])).

tff(c_955,plain,(
    ~ r1_tarski('#skF_2',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_948])).

tff(c_961,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_955])).

tff(c_966,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_961])).

tff(c_967,plain,(
    ~ r1_tarski(k1_zfmisc_1('#skF_1'),k1_zfmisc_1(k2_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_239])).

tff(c_974,plain,(
    ~ r1_tarski('#skF_1',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_967])).

tff(c_980,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_974])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:39:47 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.35  
% 2.59/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.36  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.59/1.36  
% 2.59/1.36  %Foreground sorts:
% 2.59/1.36  
% 2.59/1.36  
% 2.59/1.36  %Background operators:
% 2.59/1.36  
% 2.59/1.36  
% 2.59/1.36  %Foreground operators:
% 2.59/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.59/1.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.59/1.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.59/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.59/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.59/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.59/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.59/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.59/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.59/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.59/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.36  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.59/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.59/1.36  
% 2.86/1.37  tff(f_47, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.86/1.37  tff(f_61, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 2.86/1.37  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.86/1.37  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.86/1.37  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 2.86/1.37  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.86/1.37  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_xboole_1)).
% 2.86/1.37  tff(f_64, negated_conjecture, ~(![A, B]: r1_tarski(k2_xboole_0(k1_zfmisc_1(A), k1_zfmisc_1(B)), k1_zfmisc_1(k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_zfmisc_1)).
% 2.86/1.37  tff(c_14, plain, (![A_12, B_13]: (r1_tarski(A_12, k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.86/1.37  tff(c_26, plain, (![A_27, B_28]: (r1_tarski(k1_zfmisc_1(A_27), k1_zfmisc_1(B_28)) | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.86/1.37  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.86/1.37  tff(c_10, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, k2_xboole_0(C_8, B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.86/1.37  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(k4_xboole_0(A_3, C_5), B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.86/1.37  tff(c_16, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.86/1.37  tff(c_96, plain, (![A_53, C_54, B_55]: (r1_tarski(k5_xboole_0(A_53, C_54), B_55) | ~r1_tarski(C_54, B_55) | ~r1_tarski(A_53, B_55))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.86/1.37  tff(c_187, plain, (![A_72, B_73, B_74]: (r1_tarski(k2_xboole_0(A_72, B_73), B_74) | ~r1_tarski(k4_xboole_0(B_73, A_72), B_74) | ~r1_tarski(A_72, B_74))), inference(superposition, [status(thm), theory('equality')], [c_16, c_96])).
% 2.86/1.37  tff(c_207, plain, (![C_75, A_76, B_77]: (r1_tarski(k2_xboole_0(C_75, A_76), B_77) | ~r1_tarski(C_75, B_77) | ~r1_tarski(A_76, B_77))), inference(resolution, [status(thm)], [c_8, c_187])).
% 2.86/1.37  tff(c_28, plain, (~r1_tarski(k2_xboole_0(k1_zfmisc_1('#skF_1'), k1_zfmisc_1('#skF_2')), k1_zfmisc_1(k2_xboole_0('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.86/1.37  tff(c_239, plain, (~r1_tarski(k1_zfmisc_1('#skF_1'), k1_zfmisc_1(k2_xboole_0('#skF_1', '#skF_2'))) | ~r1_tarski(k1_zfmisc_1('#skF_2'), k1_zfmisc_1(k2_xboole_0('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_207, c_28])).
% 2.86/1.37  tff(c_948, plain, (~r1_tarski(k1_zfmisc_1('#skF_2'), k1_zfmisc_1(k2_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_239])).
% 2.86/1.37  tff(c_955, plain, (~r1_tarski('#skF_2', k2_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_948])).
% 2.86/1.37  tff(c_961, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_10, c_955])).
% 2.86/1.37  tff(c_966, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_961])).
% 2.86/1.37  tff(c_967, plain, (~r1_tarski(k1_zfmisc_1('#skF_1'), k1_zfmisc_1(k2_xboole_0('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_239])).
% 2.86/1.37  tff(c_974, plain, (~r1_tarski('#skF_1', k2_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_967])).
% 2.86/1.37  tff(c_980, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_974])).
% 2.86/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.37  
% 2.86/1.37  Inference rules
% 2.86/1.37  ----------------------
% 2.86/1.37  #Ref     : 0
% 2.86/1.37  #Sup     : 227
% 2.86/1.37  #Fact    : 0
% 2.86/1.37  #Define  : 0
% 2.86/1.37  #Split   : 2
% 2.86/1.37  #Chain   : 0
% 2.86/1.37  #Close   : 0
% 2.86/1.37  
% 2.86/1.37  Ordering : KBO
% 2.86/1.37  
% 2.86/1.37  Simplification rules
% 2.86/1.37  ----------------------
% 2.86/1.37  #Subsume      : 19
% 2.86/1.37  #Demod        : 54
% 2.86/1.37  #Tautology    : 98
% 2.86/1.37  #SimpNegUnit  : 0
% 2.86/1.37  #BackRed      : 0
% 2.86/1.37  
% 2.86/1.37  #Partial instantiations: 0
% 2.86/1.37  #Strategies tried      : 1
% 2.86/1.37  
% 2.86/1.37  Timing (in seconds)
% 2.86/1.37  ----------------------
% 2.86/1.37  Preprocessing        : 0.28
% 2.86/1.37  Parsing              : 0.15
% 2.86/1.37  CNF conversion       : 0.02
% 2.86/1.37  Main loop            : 0.34
% 2.86/1.37  Inferencing          : 0.13
% 2.86/1.37  Reduction            : 0.09
% 2.86/1.37  Demodulation         : 0.07
% 2.86/1.37  BG Simplification    : 0.02
% 2.86/1.37  Subsumption          : 0.08
% 2.86/1.37  Abstraction          : 0.02
% 2.86/1.37  MUC search           : 0.00
% 2.86/1.37  Cooper               : 0.00
% 2.86/1.37  Total                : 0.65
% 2.86/1.37  Index Insertion      : 0.00
% 2.86/1.37  Index Deletion       : 0.00
% 2.86/1.37  Index Matching       : 0.00
% 2.86/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
