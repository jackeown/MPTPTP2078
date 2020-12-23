%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:33 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   43 (  59 expanded)
%              Number of leaves         :   19 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   38 (  59 expanded)
%              Number of equality atoms :   26 (  40 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(A,C) )
       => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_71,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k4_xboole_0(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_92,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k3_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_71])).

tff(c_96,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_92])).

tff(c_20,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_44,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = A_16
      | ~ r1_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_48,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_20,c_44])).

tff(c_89,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_71])).

tff(c_176,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_89])).

tff(c_10,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_122,plain,(
    ! [A_25,B_26,C_27] : k2_xboole_0(k4_xboole_0(A_25,B_26),k3_xboole_0(A_25,C_27)) = k4_xboole_0(A_25,k4_xboole_0(B_26,C_27)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_134,plain,(
    ! [A_4,C_27] : k4_xboole_0(A_4,k4_xboole_0(A_4,C_27)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(A_4,C_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_122])).

tff(c_152,plain,(
    ! [A_4,C_27] : k2_xboole_0(k1_xboole_0,k3_xboole_0(A_4,C_27)) = k3_xboole_0(A_4,C_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_134])).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_53,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,B_19) = k1_xboole_0
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_61,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_53])).

tff(c_140,plain,(
    ! [C_27] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_27)) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_1',C_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_122])).

tff(c_330,plain,(
    ! [C_27] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_27)) = k3_xboole_0('#skF_1',C_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_140])).

tff(c_39,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | k4_xboole_0(A_14,B_15) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ~ r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_43,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_39,c_18])).

tff(c_331,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_43])).

tff(c_334,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_331])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:15:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.28  
% 1.93/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.28  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.93/1.28  
% 1.93/1.28  %Foreground sorts:
% 1.93/1.28  
% 1.93/1.28  
% 1.93/1.28  %Background operators:
% 1.93/1.28  
% 1.93/1.28  
% 1.93/1.28  %Foreground operators:
% 1.93/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.93/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.93/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.93/1.28  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.28  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.28  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.93/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.93/1.28  
% 1.93/1.29  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.93/1.29  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.93/1.29  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.93/1.29  tff(f_48, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 1.93/1.29  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.93/1.29  tff(f_37, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 1.93/1.29  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.93/1.29  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.93/1.29  tff(c_8, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.93/1.29  tff(c_71, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k4_xboole_0(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.93/1.29  tff(c_92, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k3_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_71])).
% 1.93/1.29  tff(c_96, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_92])).
% 1.93/1.29  tff(c_20, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.93/1.29  tff(c_44, plain, (![A_16, B_17]: (k4_xboole_0(A_16, B_17)=A_16 | ~r1_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.93/1.29  tff(c_48, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_20, c_44])).
% 1.93/1.29  tff(c_89, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_48, c_71])).
% 1.93/1.29  tff(c_176, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_96, c_89])).
% 1.93/1.29  tff(c_10, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.93/1.29  tff(c_122, plain, (![A_25, B_26, C_27]: (k2_xboole_0(k4_xboole_0(A_25, B_26), k3_xboole_0(A_25, C_27))=k4_xboole_0(A_25, k4_xboole_0(B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.93/1.29  tff(c_134, plain, (![A_4, C_27]: (k4_xboole_0(A_4, k4_xboole_0(A_4, C_27))=k2_xboole_0(k1_xboole_0, k3_xboole_0(A_4, C_27)))), inference(superposition, [status(thm), theory('equality')], [c_96, c_122])).
% 1.93/1.29  tff(c_152, plain, (![A_4, C_27]: (k2_xboole_0(k1_xboole_0, k3_xboole_0(A_4, C_27))=k3_xboole_0(A_4, C_27))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_134])).
% 1.93/1.29  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.93/1.29  tff(c_53, plain, (![A_18, B_19]: (k4_xboole_0(A_18, B_19)=k1_xboole_0 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.93/1.29  tff(c_61, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_53])).
% 1.93/1.29  tff(c_140, plain, (![C_27]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_27))=k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_1', C_27)))), inference(superposition, [status(thm), theory('equality')], [c_61, c_122])).
% 1.93/1.29  tff(c_330, plain, (![C_27]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_27))=k3_xboole_0('#skF_1', C_27))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_140])).
% 1.93/1.29  tff(c_39, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | k4_xboole_0(A_14, B_15)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.93/1.29  tff(c_18, plain, (~r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.93/1.29  tff(c_43, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_39, c_18])).
% 1.93/1.29  tff(c_331, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_330, c_43])).
% 1.93/1.29  tff(c_334, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_176, c_331])).
% 1.93/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.29  
% 1.93/1.29  Inference rules
% 1.93/1.29  ----------------------
% 1.93/1.29  #Ref     : 0
% 1.93/1.29  #Sup     : 80
% 1.93/1.29  #Fact    : 0
% 1.93/1.29  #Define  : 0
% 1.93/1.29  #Split   : 0
% 1.93/1.29  #Chain   : 0
% 1.93/1.29  #Close   : 0
% 1.93/1.29  
% 1.93/1.29  Ordering : KBO
% 1.93/1.29  
% 1.93/1.29  Simplification rules
% 1.93/1.29  ----------------------
% 1.93/1.29  #Subsume      : 0
% 1.93/1.29  #Demod        : 44
% 1.93/1.29  #Tautology    : 53
% 1.93/1.29  #SimpNegUnit  : 0
% 1.93/1.29  #BackRed      : 1
% 1.93/1.29  
% 1.93/1.29  #Partial instantiations: 0
% 1.93/1.29  #Strategies tried      : 1
% 1.93/1.29  
% 1.93/1.29  Timing (in seconds)
% 1.93/1.29  ----------------------
% 1.93/1.29  Preprocessing        : 0.27
% 1.93/1.29  Parsing              : 0.16
% 1.93/1.29  CNF conversion       : 0.02
% 1.93/1.29  Main loop            : 0.20
% 1.93/1.29  Inferencing          : 0.08
% 1.93/1.29  Reduction            : 0.07
% 1.93/1.29  Demodulation         : 0.05
% 1.93/1.29  BG Simplification    : 0.01
% 1.93/1.29  Subsumption          : 0.03
% 1.93/1.29  Abstraction          : 0.01
% 1.93/1.29  MUC search           : 0.00
% 1.93/1.29  Cooper               : 0.00
% 1.93/1.29  Total                : 0.50
% 1.93/1.29  Index Insertion      : 0.00
% 1.93/1.29  Index Deletion       : 0.00
% 1.93/1.29  Index Matching       : 0.00
% 1.93/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
