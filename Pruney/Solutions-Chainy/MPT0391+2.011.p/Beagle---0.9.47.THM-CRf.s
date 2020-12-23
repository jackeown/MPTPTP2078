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
% DateTime   : Thu Dec  3 09:57:16 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   39 (  43 expanded)
%              Number of leaves         :   21 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   35 (  43 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r1_xboole_0(A,C) )
       => r1_xboole_0(k1_setfam_1(B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_setfam_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(c_22,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k1_setfam_1(B_11),A_10)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_80,plain,(
    ! [A_27,B_28] : k5_xboole_0(A_27,k3_xboole_0(A_27,B_28)) = k4_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_92,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = k4_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_80])).

tff(c_95,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_92])).

tff(c_20,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_45,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = k1_xboole_0
      | ~ r1_xboole_0(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_53,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_45])).

tff(c_89,plain,(
    k5_xboole_0('#skF_1',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_80])).

tff(c_114,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_89])).

tff(c_8,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_xboole_0(A_5,C_7)
      | ~ r1_tarski(A_5,k4_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_125,plain,(
    ! [A_33] :
      ( r1_xboole_0(A_33,'#skF_3')
      | ~ r1_tarski(A_33,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_8])).

tff(c_18,plain,(
    ~ r1_xboole_0(k1_setfam_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_133,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_125,c_18])).

tff(c_136,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_133])).

tff(c_140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_136])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:04:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.21  
% 1.88/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.21  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.88/1.21  
% 1.88/1.21  %Foreground sorts:
% 1.88/1.21  
% 1.88/1.21  
% 1.88/1.21  %Background operators:
% 1.88/1.21  
% 1.88/1.21  
% 1.88/1.21  %Foreground operators:
% 1.88/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.88/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.88/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.88/1.21  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.88/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.88/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.88/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.88/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.88/1.21  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.88/1.21  
% 1.88/1.22  tff(f_52, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r1_xboole_0(A, C)) => r1_xboole_0(k1_setfam_1(B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_setfam_1)).
% 1.88/1.22  tff(f_45, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 1.88/1.22  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.88/1.22  tff(f_39, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.88/1.22  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.88/1.22  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.88/1.22  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 1.88/1.22  tff(c_22, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.88/1.22  tff(c_16, plain, (![B_11, A_10]: (r1_tarski(k1_setfam_1(B_11), A_10) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.88/1.22  tff(c_14, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.88/1.22  tff(c_12, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.88/1.22  tff(c_80, plain, (![A_27, B_28]: (k5_xboole_0(A_27, k3_xboole_0(A_27, B_28))=k4_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.88/1.22  tff(c_92, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=k4_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_80])).
% 1.88/1.22  tff(c_95, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_92])).
% 1.88/1.22  tff(c_20, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.88/1.22  tff(c_45, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=k1_xboole_0 | ~r1_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.88/1.22  tff(c_53, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_45])).
% 1.88/1.22  tff(c_89, plain, (k5_xboole_0('#skF_1', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_53, c_80])).
% 1.88/1.22  tff(c_114, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_95, c_89])).
% 1.88/1.22  tff(c_8, plain, (![A_5, C_7, B_6]: (r1_xboole_0(A_5, C_7) | ~r1_tarski(A_5, k4_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.88/1.22  tff(c_125, plain, (![A_33]: (r1_xboole_0(A_33, '#skF_3') | ~r1_tarski(A_33, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_114, c_8])).
% 1.88/1.22  tff(c_18, plain, (~r1_xboole_0(k1_setfam_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.88/1.22  tff(c_133, plain, (~r1_tarski(k1_setfam_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_125, c_18])).
% 1.88/1.22  tff(c_136, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_16, c_133])).
% 1.88/1.22  tff(c_140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_136])).
% 1.88/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.22  
% 1.88/1.22  Inference rules
% 1.88/1.22  ----------------------
% 1.88/1.22  #Ref     : 0
% 1.88/1.22  #Sup     : 29
% 1.88/1.22  #Fact    : 0
% 1.88/1.22  #Define  : 0
% 1.88/1.22  #Split   : 0
% 1.88/1.22  #Chain   : 0
% 1.88/1.22  #Close   : 0
% 1.88/1.22  
% 1.88/1.22  Ordering : KBO
% 1.88/1.22  
% 1.88/1.22  Simplification rules
% 1.88/1.22  ----------------------
% 1.88/1.22  #Subsume      : 0
% 1.88/1.22  #Demod        : 4
% 1.88/1.22  #Tautology    : 16
% 1.88/1.22  #SimpNegUnit  : 0
% 1.88/1.22  #BackRed      : 0
% 1.88/1.22  
% 1.88/1.22  #Partial instantiations: 0
% 1.88/1.22  #Strategies tried      : 1
% 1.88/1.22  
% 1.88/1.22  Timing (in seconds)
% 1.88/1.22  ----------------------
% 1.88/1.22  Preprocessing        : 0.28
% 1.88/1.22  Parsing              : 0.16
% 1.88/1.22  CNF conversion       : 0.02
% 1.88/1.22  Main loop            : 0.13
% 1.88/1.22  Inferencing          : 0.06
% 1.88/1.22  Reduction            : 0.04
% 1.88/1.22  Demodulation         : 0.03
% 1.88/1.22  BG Simplification    : 0.01
% 1.88/1.22  Subsumption          : 0.02
% 1.88/1.22  Abstraction          : 0.01
% 1.88/1.22  MUC search           : 0.00
% 1.88/1.23  Cooper               : 0.00
% 1.88/1.23  Total                : 0.44
% 1.88/1.23  Index Insertion      : 0.00
% 1.88/1.23  Index Deletion       : 0.00
% 1.88/1.23  Index Matching       : 0.00
% 1.88/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
