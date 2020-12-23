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
% DateTime   : Thu Dec  3 09:43:55 EST 2020

% Result     : Theorem 4.63s
% Output     : CNFRefutation 4.97s
% Verified   : 
% Statistics : Number of formulae       :   40 (  45 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   46 (  58 expanded)
%              Number of equality atoms :   16 (  19 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(f_66,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_101,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_241,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(A_58,B_59)
      | k4_xboole_0(A_58,B_59) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_40,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_257,plain,(
    k4_xboole_0('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_241,c_40])).

tff(c_22,plain,(
    ! [A_17,B_18] : r1_tarski(k4_xboole_0(A_17,B_18),A_17) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_42,plain,(
    r1_xboole_0('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_471,plain,(
    ! [A_74,C_75,B_76] :
      ( r1_xboole_0(A_74,C_75)
      | ~ r1_xboole_0(B_76,C_75)
      | ~ r1_tarski(A_74,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_506,plain,(
    ! [A_78] :
      ( r1_xboole_0(A_78,'#skF_4')
      | ~ r1_tarski(A_78,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_471])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_911,plain,(
    ! [A_92] :
      ( k3_xboole_0(A_92,'#skF_4') = k1_xboole_0
      | ~ r1_tarski(A_92,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_506,c_2])).

tff(c_941,plain,(
    ! [B_18] : k3_xboole_0(k4_xboole_0('#skF_2',B_18),'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_911])).

tff(c_44,plain,(
    r1_tarski('#skF_2',k2_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_805,plain,(
    ! [A_88,B_89,C_90] :
      ( r1_tarski(k4_xboole_0(A_88,B_89),C_90)
      | ~ r1_tarski(A_88,k2_xboole_0(B_89,C_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_26,plain,(
    ! [A_19,B_20] :
      ( k4_xboole_0(A_19,B_20) = k1_xboole_0
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4597,plain,(
    ! [A_184,B_185,C_186] :
      ( k4_xboole_0(k4_xboole_0(A_184,B_185),C_186) = k1_xboole_0
      | ~ r1_tarski(A_184,k2_xboole_0(B_185,C_186)) ) ),
    inference(resolution,[status(thm)],[c_805,c_26])).

tff(c_4684,plain,(
    k4_xboole_0(k4_xboole_0('#skF_2','#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_4597])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_256,plain,(
    ! [A_58,B_59] :
      ( k3_xboole_0(A_58,B_59) = A_58
      | k4_xboole_0(A_58,B_59) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_241,c_18])).

tff(c_4697,plain,(
    k3_xboole_0(k4_xboole_0('#skF_2','#skF_3'),'#skF_4') = k4_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4684,c_256])).

tff(c_4733,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_941,c_4697])).

tff(c_4735,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_257,c_4733])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:35:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.63/2.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.63/2.06  
% 4.63/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.63/2.06  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 4.63/2.06  
% 4.63/2.06  %Foreground sorts:
% 4.63/2.06  
% 4.63/2.06  
% 4.63/2.06  %Background operators:
% 4.63/2.06  
% 4.63/2.06  
% 4.63/2.06  %Foreground operators:
% 4.63/2.06  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.63/2.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.63/2.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.63/2.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.63/2.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.63/2.06  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.63/2.06  tff('#skF_2', type, '#skF_2': $i).
% 4.63/2.06  tff('#skF_3', type, '#skF_3': $i).
% 4.63/2.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.63/2.06  tff('#skF_4', type, '#skF_4': $i).
% 4.63/2.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.63/2.06  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.63/2.06  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.63/2.06  
% 4.97/2.07  tff(f_66, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 4.97/2.07  tff(f_101, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 4.97/2.07  tff(f_62, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.97/2.07  tff(f_80, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 4.97/2.07  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.97/2.07  tff(f_70, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 4.97/2.07  tff(f_58, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.97/2.07  tff(c_241, plain, (![A_58, B_59]: (r1_tarski(A_58, B_59) | k4_xboole_0(A_58, B_59)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.97/2.07  tff(c_40, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.97/2.07  tff(c_257, plain, (k4_xboole_0('#skF_2', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_241, c_40])).
% 4.97/2.07  tff(c_22, plain, (![A_17, B_18]: (r1_tarski(k4_xboole_0(A_17, B_18), A_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.97/2.07  tff(c_42, plain, (r1_xboole_0('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.97/2.07  tff(c_471, plain, (![A_74, C_75, B_76]: (r1_xboole_0(A_74, C_75) | ~r1_xboole_0(B_76, C_75) | ~r1_tarski(A_74, B_76))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.97/2.07  tff(c_506, plain, (![A_78]: (r1_xboole_0(A_78, '#skF_4') | ~r1_tarski(A_78, '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_471])).
% 4.97/2.07  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.97/2.07  tff(c_911, plain, (![A_92]: (k3_xboole_0(A_92, '#skF_4')=k1_xboole_0 | ~r1_tarski(A_92, '#skF_2'))), inference(resolution, [status(thm)], [c_506, c_2])).
% 4.97/2.07  tff(c_941, plain, (![B_18]: (k3_xboole_0(k4_xboole_0('#skF_2', B_18), '#skF_4')=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_911])).
% 4.97/2.07  tff(c_44, plain, (r1_tarski('#skF_2', k2_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.97/2.07  tff(c_805, plain, (![A_88, B_89, C_90]: (r1_tarski(k4_xboole_0(A_88, B_89), C_90) | ~r1_tarski(A_88, k2_xboole_0(B_89, C_90)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.97/2.07  tff(c_26, plain, (![A_19, B_20]: (k4_xboole_0(A_19, B_20)=k1_xboole_0 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.97/2.07  tff(c_4597, plain, (![A_184, B_185, C_186]: (k4_xboole_0(k4_xboole_0(A_184, B_185), C_186)=k1_xboole_0 | ~r1_tarski(A_184, k2_xboole_0(B_185, C_186)))), inference(resolution, [status(thm)], [c_805, c_26])).
% 4.97/2.07  tff(c_4684, plain, (k4_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_4597])).
% 4.97/2.07  tff(c_18, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.97/2.07  tff(c_256, plain, (![A_58, B_59]: (k3_xboole_0(A_58, B_59)=A_58 | k4_xboole_0(A_58, B_59)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_241, c_18])).
% 4.97/2.07  tff(c_4697, plain, (k3_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), '#skF_4')=k4_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4684, c_256])).
% 4.97/2.07  tff(c_4733, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_941, c_4697])).
% 4.97/2.07  tff(c_4735, plain, $false, inference(negUnitSimplification, [status(thm)], [c_257, c_4733])).
% 4.97/2.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.97/2.07  
% 4.97/2.07  Inference rules
% 4.97/2.07  ----------------------
% 4.97/2.07  #Ref     : 1
% 4.97/2.07  #Sup     : 1119
% 4.97/2.07  #Fact    : 0
% 4.97/2.07  #Define  : 0
% 4.97/2.07  #Split   : 5
% 4.97/2.07  #Chain   : 0
% 4.97/2.07  #Close   : 0
% 4.97/2.07  
% 4.97/2.07  Ordering : KBO
% 4.97/2.07  
% 4.97/2.07  Simplification rules
% 4.97/2.07  ----------------------
% 4.97/2.07  #Subsume      : 273
% 4.97/2.07  #Demod        : 439
% 4.97/2.07  #Tautology    : 581
% 4.97/2.07  #SimpNegUnit  : 64
% 4.97/2.07  #BackRed      : 1
% 4.97/2.07  
% 4.97/2.07  #Partial instantiations: 0
% 4.97/2.07  #Strategies tried      : 1
% 4.97/2.07  
% 4.97/2.07  Timing (in seconds)
% 4.97/2.07  ----------------------
% 4.97/2.07  Preprocessing        : 0.38
% 4.97/2.07  Parsing              : 0.21
% 4.97/2.07  CNF conversion       : 0.03
% 4.97/2.07  Main loop            : 0.85
% 4.97/2.07  Inferencing          : 0.29
% 4.97/2.07  Reduction            : 0.30
% 4.97/2.07  Demodulation         : 0.21
% 4.97/2.07  BG Simplification    : 0.03
% 4.97/2.07  Subsumption          : 0.17
% 4.97/2.07  Abstraction          : 0.04
% 4.97/2.07  MUC search           : 0.00
% 4.97/2.07  Cooper               : 0.00
% 4.97/2.07  Total                : 1.25
% 4.97/2.07  Index Insertion      : 0.00
% 4.97/2.07  Index Deletion       : 0.00
% 4.97/2.08  Index Matching       : 0.00
% 4.97/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
