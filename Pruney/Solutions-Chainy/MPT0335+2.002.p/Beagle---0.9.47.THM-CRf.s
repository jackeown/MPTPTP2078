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
% DateTime   : Thu Dec  3 09:54:53 EST 2020

% Result     : Theorem 4.41s
% Output     : CNFRefutation 4.57s
% Verified   : 
% Statistics : Number of formulae       :   43 (  59 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :   36 (  66 expanded)
%              Number of equality atoms :   26 (  45 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_zfmisc_1)).

tff(c_40,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_42,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_22,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k3_xboole_0(A_18,B_19)) = k4_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_46,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_242,plain,(
    ! [A_49,B_50] :
      ( k3_xboole_0(A_49,B_50) = A_49
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_246,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_46,c_242])).

tff(c_1256,plain,(
    ! [A_80,B_81,C_82] : k4_xboole_0(k3_xboole_0(A_80,B_81),k3_xboole_0(A_80,C_82)) = k3_xboole_0(A_80,k4_xboole_0(B_81,C_82)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1336,plain,(
    ! [C_82] : k4_xboole_0('#skF_1',k3_xboole_0('#skF_1',C_82)) = k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_82)) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_1256])).

tff(c_1378,plain,(
    ! [C_82] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_82)) = k4_xboole_0('#skF_1',C_82) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1336])).

tff(c_44,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_273,plain,(
    ! [A_55,B_56] : k4_xboole_0(A_55,k3_xboole_0(A_55,B_56)) = k4_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_294,plain,(
    k4_xboole_0('#skF_2',k1_tarski('#skF_4')) = k4_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_273])).

tff(c_2025,plain,(
    ! [C_95] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_95)) = k4_xboole_0('#skF_1',C_95) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1336])).

tff(c_2069,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_4')) = k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_2025])).

tff(c_2085,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_4')) = k4_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1378,c_2069])).

tff(c_2178,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_1','#skF_3')) = k3_xboole_0('#skF_1',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2085,c_22])).

tff(c_2184,plain,(
    k3_xboole_0('#skF_1',k1_tarski('#skF_4')) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2178])).

tff(c_38,plain,(
    ! [B_38,A_37] :
      ( k3_xboole_0(B_38,k1_tarski(A_37)) = k1_tarski(A_37)
      | ~ r2_hidden(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2427,plain,
    ( k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4')
    | ~ r2_hidden('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2184,c_38])).

tff(c_2443,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2427])).

tff(c_2445,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_2443])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:41:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.41/1.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.49/1.81  
% 4.49/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.49/1.81  %$ r2_hidden > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.49/1.81  
% 4.49/1.81  %Foreground sorts:
% 4.49/1.81  
% 4.49/1.81  
% 4.49/1.81  %Background operators:
% 4.49/1.81  
% 4.49/1.81  
% 4.49/1.81  %Foreground operators:
% 4.49/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.49/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.49/1.81  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.49/1.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.49/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.49/1.81  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.49/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.49/1.81  tff('#skF_2', type, '#skF_2': $i).
% 4.49/1.81  tff('#skF_3', type, '#skF_3': $i).
% 4.49/1.81  tff('#skF_1', type, '#skF_1': $i).
% 4.49/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.49/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.49/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.49/1.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.49/1.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.49/1.81  
% 4.57/1.83  tff(f_80, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 4.57/1.83  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.57/1.83  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.57/1.83  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.57/1.83  tff(f_53, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_xboole_1)).
% 4.57/1.83  tff(f_71, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_zfmisc_1)).
% 4.57/1.83  tff(c_40, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.57/1.83  tff(c_42, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.57/1.83  tff(c_22, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.57/1.83  tff(c_20, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k3_xboole_0(A_18, B_19))=k4_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.57/1.83  tff(c_46, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.57/1.83  tff(c_242, plain, (![A_49, B_50]: (k3_xboole_0(A_49, B_50)=A_49 | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.57/1.83  tff(c_246, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_46, c_242])).
% 4.57/1.83  tff(c_1256, plain, (![A_80, B_81, C_82]: (k4_xboole_0(k3_xboole_0(A_80, B_81), k3_xboole_0(A_80, C_82))=k3_xboole_0(A_80, k4_xboole_0(B_81, C_82)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.57/1.83  tff(c_1336, plain, (![C_82]: (k4_xboole_0('#skF_1', k3_xboole_0('#skF_1', C_82))=k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_82)))), inference(superposition, [status(thm), theory('equality')], [c_246, c_1256])).
% 4.57/1.83  tff(c_1378, plain, (![C_82]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_82))=k4_xboole_0('#skF_1', C_82))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1336])).
% 4.57/1.83  tff(c_44, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.57/1.83  tff(c_273, plain, (![A_55, B_56]: (k4_xboole_0(A_55, k3_xboole_0(A_55, B_56))=k4_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.57/1.83  tff(c_294, plain, (k4_xboole_0('#skF_2', k1_tarski('#skF_4'))=k4_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_44, c_273])).
% 4.57/1.83  tff(c_2025, plain, (![C_95]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_95))=k4_xboole_0('#skF_1', C_95))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1336])).
% 4.57/1.83  tff(c_2069, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_4'))=k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_294, c_2025])).
% 4.57/1.83  tff(c_2085, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_4'))=k4_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1378, c_2069])).
% 4.57/1.83  tff(c_2178, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_1', '#skF_3'))=k3_xboole_0('#skF_1', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2085, c_22])).
% 4.57/1.83  tff(c_2184, plain, (k3_xboole_0('#skF_1', k1_tarski('#skF_4'))=k3_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2178])).
% 4.57/1.83  tff(c_38, plain, (![B_38, A_37]: (k3_xboole_0(B_38, k1_tarski(A_37))=k1_tarski(A_37) | ~r2_hidden(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.57/1.83  tff(c_2427, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4') | ~r2_hidden('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2184, c_38])).
% 4.57/1.83  tff(c_2443, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2427])).
% 4.57/1.83  tff(c_2445, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_2443])).
% 4.57/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.57/1.83  
% 4.57/1.83  Inference rules
% 4.57/1.83  ----------------------
% 4.57/1.83  #Ref     : 0
% 4.57/1.83  #Sup     : 654
% 4.57/1.83  #Fact    : 0
% 4.57/1.83  #Define  : 0
% 4.57/1.83  #Split   : 2
% 4.57/1.83  #Chain   : 0
% 4.57/1.83  #Close   : 0
% 4.57/1.83  
% 4.57/1.83  Ordering : KBO
% 4.57/1.83  
% 4.57/1.83  Simplification rules
% 4.57/1.83  ----------------------
% 4.57/1.83  #Subsume      : 15
% 4.57/1.83  #Demod        : 493
% 4.57/1.83  #Tautology    : 308
% 4.57/1.83  #SimpNegUnit  : 1
% 4.57/1.83  #BackRed      : 4
% 4.57/1.83  
% 4.57/1.83  #Partial instantiations: 0
% 4.57/1.83  #Strategies tried      : 1
% 4.57/1.83  
% 4.57/1.83  Timing (in seconds)
% 4.57/1.83  ----------------------
% 4.57/1.83  Preprocessing        : 0.33
% 4.57/1.83  Parsing              : 0.18
% 4.57/1.83  CNF conversion       : 0.02
% 4.57/1.83  Main loop            : 0.74
% 4.57/1.83  Inferencing          : 0.22
% 4.57/1.83  Reduction            : 0.34
% 4.57/1.84  Demodulation         : 0.28
% 4.57/1.84  BG Simplification    : 0.03
% 4.57/1.84  Subsumption          : 0.11
% 4.57/1.84  Abstraction          : 0.04
% 4.57/1.84  MUC search           : 0.00
% 4.57/1.84  Cooper               : 0.00
% 4.57/1.84  Total                : 1.10
% 4.57/1.84  Index Insertion      : 0.00
% 4.57/1.84  Index Deletion       : 0.00
% 4.57/1.84  Index Matching       : 0.00
% 4.57/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
