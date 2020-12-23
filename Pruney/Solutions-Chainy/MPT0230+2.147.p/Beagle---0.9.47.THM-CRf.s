%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:14 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   36 (  58 expanded)
%              Number of leaves         :   16 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :   44 (  94 expanded)
%              Number of equality atoms :   25 (  55 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_55,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A != B
     => k4_xboole_0(k2_tarski(A,B),k1_tarski(B)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_16,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(k1_tarski(A_5),k1_tarski(B_6)) = k1_tarski(A_5)
      | B_6 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_54,plain,(
    ! [A_20,B_21] :
      ( k4_xboole_0(k2_tarski(A_20,B_21),k1_tarski(B_21)) = k1_tarski(A_20)
      | B_21 = A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(k4_xboole_0(A_1,C_3),k4_xboole_0(B_2,C_3))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_95,plain,(
    ! [A_31,B_32,A_33] :
      ( r1_tarski(k4_xboole_0(A_31,k1_tarski(B_32)),k1_tarski(A_33))
      | ~ r1_tarski(A_31,k2_tarski(A_33,B_32))
      | B_32 = A_33 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_2])).

tff(c_106,plain,(
    ! [A_37,A_38,B_39] :
      ( r1_tarski(k1_tarski(A_37),k1_tarski(A_38))
      | ~ r1_tarski(k1_tarski(A_37),k2_tarski(A_38,B_39))
      | B_39 = A_38
      | B_39 = A_37 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_95])).

tff(c_109,plain,
    ( r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_2'))
    | '#skF_2' = '#skF_3'
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_18,c_106])).

tff(c_115,plain,
    ( r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_2'))
    | '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_109])).

tff(c_116,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_117,plain,(
    r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_18])).

tff(c_119,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_117])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( B_10 = A_9
      | ~ r1_tarski(k1_tarski(A_9),k1_tarski(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_126,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_119,c_12])).

tff(c_130,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_126])).

tff(c_131,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_135,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_131,c_12])).

tff(c_139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_135])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:10:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.41  
% 2.04/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.41  %$ r1_tarski > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.04/1.41  
% 2.04/1.41  %Foreground sorts:
% 2.04/1.41  
% 2.04/1.41  
% 2.04/1.41  %Background operators:
% 2.04/1.41  
% 2.04/1.41  
% 2.04/1.41  %Foreground operators:
% 2.04/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.04/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.04/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.04/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.04/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.04/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.04/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.04/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.41  
% 2.04/1.42  tff(f_55, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 2.04/1.42  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.04/1.42  tff(f_36, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.04/1.42  tff(f_41, axiom, (![A, B]: (~(A = B) => (k4_xboole_0(k2_tarski(A, B), k1_tarski(B)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_zfmisc_1)).
% 2.04/1.42  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_xboole_1)).
% 2.04/1.42  tff(f_45, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.04/1.42  tff(c_16, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.04/1.42  tff(c_14, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.04/1.42  tff(c_4, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.04/1.42  tff(c_18, plain, (r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.04/1.42  tff(c_8, plain, (![A_5, B_6]: (k4_xboole_0(k1_tarski(A_5), k1_tarski(B_6))=k1_tarski(A_5) | B_6=A_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.04/1.42  tff(c_54, plain, (![A_20, B_21]: (k4_xboole_0(k2_tarski(A_20, B_21), k1_tarski(B_21))=k1_tarski(A_20) | B_21=A_20)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.04/1.42  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(k4_xboole_0(A_1, C_3), k4_xboole_0(B_2, C_3)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.04/1.42  tff(c_95, plain, (![A_31, B_32, A_33]: (r1_tarski(k4_xboole_0(A_31, k1_tarski(B_32)), k1_tarski(A_33)) | ~r1_tarski(A_31, k2_tarski(A_33, B_32)) | B_32=A_33)), inference(superposition, [status(thm), theory('equality')], [c_54, c_2])).
% 2.04/1.42  tff(c_106, plain, (![A_37, A_38, B_39]: (r1_tarski(k1_tarski(A_37), k1_tarski(A_38)) | ~r1_tarski(k1_tarski(A_37), k2_tarski(A_38, B_39)) | B_39=A_38 | B_39=A_37)), inference(superposition, [status(thm), theory('equality')], [c_8, c_95])).
% 2.04/1.42  tff(c_109, plain, (r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_2')) | '#skF_2'='#skF_3' | '#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_18, c_106])).
% 2.04/1.42  tff(c_115, plain, (r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_2')) | '#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_14, c_109])).
% 2.04/1.42  tff(c_116, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_115])).
% 2.04/1.42  tff(c_117, plain, (r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_18])).
% 2.04/1.42  tff(c_119, plain, (r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_117])).
% 2.04/1.42  tff(c_12, plain, (![B_10, A_9]: (B_10=A_9 | ~r1_tarski(k1_tarski(A_9), k1_tarski(B_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.04/1.42  tff(c_126, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_119, c_12])).
% 2.04/1.42  tff(c_130, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_126])).
% 2.04/1.42  tff(c_131, plain, (r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_115])).
% 2.04/1.42  tff(c_135, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_131, c_12])).
% 2.04/1.42  tff(c_139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_135])).
% 2.04/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.42  
% 2.04/1.42  Inference rules
% 2.04/1.42  ----------------------
% 2.04/1.42  #Ref     : 0
% 2.04/1.42  #Sup     : 27
% 2.04/1.42  #Fact    : 0
% 2.04/1.42  #Define  : 0
% 2.04/1.42  #Split   : 1
% 2.04/1.42  #Chain   : 0
% 2.04/1.42  #Close   : 0
% 2.04/1.42  
% 2.04/1.42  Ordering : KBO
% 2.04/1.42  
% 2.04/1.42  Simplification rules
% 2.04/1.42  ----------------------
% 2.04/1.42  #Subsume      : 4
% 2.04/1.42  #Demod        : 3
% 2.04/1.42  #Tautology    : 12
% 2.04/1.42  #SimpNegUnit  : 4
% 2.04/1.42  #BackRed      : 2
% 2.04/1.42  
% 2.04/1.42  #Partial instantiations: 0
% 2.04/1.42  #Strategies tried      : 1
% 2.04/1.42  
% 2.04/1.42  Timing (in seconds)
% 2.04/1.42  ----------------------
% 2.04/1.43  Preprocessing        : 0.37
% 2.04/1.43  Parsing              : 0.21
% 2.04/1.43  CNF conversion       : 0.02
% 2.04/1.43  Main loop            : 0.17
% 2.04/1.43  Inferencing          : 0.07
% 2.04/1.43  Reduction            : 0.04
% 2.04/1.43  Demodulation         : 0.03
% 2.04/1.43  BG Simplification    : 0.01
% 2.04/1.43  Subsumption          : 0.04
% 2.04/1.43  Abstraction          : 0.01
% 2.04/1.43  MUC search           : 0.00
% 2.04/1.43  Cooper               : 0.00
% 2.04/1.43  Total                : 0.57
% 2.04/1.43  Index Insertion      : 0.00
% 2.04/1.43  Index Deletion       : 0.00
% 2.04/1.43  Index Matching       : 0.00
% 2.04/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
