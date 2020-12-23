%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:42 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :   49 (  53 expanded)
%              Number of leaves         :   31 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   44 (  53 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_6 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_53,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_75,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_68,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_34,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_112,plain,(
    ! [A_78,B_79] : k1_enumset1(A_78,A_78,B_79) = k2_tarski(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10,plain,(
    ! [E_12,A_6,B_7] : r2_hidden(E_12,k1_enumset1(A_6,B_7,E_12)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_131,plain,(
    ! [B_82,A_83] : r2_hidden(B_82,k2_tarski(A_83,B_82)) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_10])).

tff(c_134,plain,(
    ! [A_16] : r2_hidden(A_16,k1_tarski(A_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_131])).

tff(c_70,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_8'),'#skF_9'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_66,plain,(
    ! [A_63,B_64] : k3_tarski(k2_tarski(A_63,B_64)) = k2_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_14,plain,(
    ! [E_12,B_7,C_8] : r2_hidden(E_12,k1_enumset1(E_12,B_7,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_124,plain,(
    ! [A_78,B_79] : r2_hidden(A_78,k2_tarski(A_78,B_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_14])).

tff(c_406,plain,(
    ! [C_115,A_116,D_117] :
      ( r2_hidden(C_115,k3_tarski(A_116))
      | ~ r2_hidden(D_117,A_116)
      | ~ r2_hidden(C_115,D_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_408,plain,(
    ! [C_115,A_78,B_79] :
      ( r2_hidden(C_115,k3_tarski(k2_tarski(A_78,B_79)))
      | ~ r2_hidden(C_115,A_78) ) ),
    inference(resolution,[status(thm)],[c_124,c_406])).

tff(c_430,plain,(
    ! [C_118,A_119,B_120] :
      ( r2_hidden(C_118,k2_xboole_0(A_119,B_120))
      | ~ r2_hidden(C_118,A_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_408])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_818,plain,(
    ! [C_178,B_179,A_180,B_181] :
      ( r2_hidden(C_178,B_179)
      | ~ r1_tarski(k2_xboole_0(A_180,B_181),B_179)
      | ~ r2_hidden(C_178,A_180) ) ),
    inference(resolution,[status(thm)],[c_430,c_2])).

tff(c_828,plain,(
    ! [C_182] :
      ( r2_hidden(C_182,'#skF_9')
      | ~ r2_hidden(C_182,k1_tarski('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_70,c_818])).

tff(c_840,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_134,c_828])).

tff(c_851,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_840])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:46:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.85/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.47  
% 2.85/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.47  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_6 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 2.85/1.47  
% 2.85/1.47  %Foreground sorts:
% 2.85/1.47  
% 2.85/1.47  
% 2.85/1.47  %Background operators:
% 2.85/1.47  
% 2.85/1.47  
% 2.85/1.47  %Foreground operators:
% 2.85/1.47  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.85/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.85/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.85/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.85/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.85/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.85/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.85/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.85/1.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.85/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.85/1.47  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.85/1.47  tff('#skF_9', type, '#skF_9': $i).
% 2.85/1.47  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 2.85/1.47  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.85/1.47  tff('#skF_8', type, '#skF_8': $i).
% 2.85/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.85/1.47  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.85/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.85/1.47  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.85/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.85/1.47  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.85/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.85/1.47  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.85/1.47  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.85/1.47  
% 2.96/1.48  tff(f_80, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 2.96/1.48  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.96/1.48  tff(f_53, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.96/1.48  tff(f_47, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.96/1.48  tff(f_75, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.96/1.48  tff(f_73, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 2.96/1.48  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.96/1.48  tff(c_68, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.96/1.48  tff(c_34, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.96/1.48  tff(c_112, plain, (![A_78, B_79]: (k1_enumset1(A_78, A_78, B_79)=k2_tarski(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.96/1.48  tff(c_10, plain, (![E_12, A_6, B_7]: (r2_hidden(E_12, k1_enumset1(A_6, B_7, E_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.96/1.48  tff(c_131, plain, (![B_82, A_83]: (r2_hidden(B_82, k2_tarski(A_83, B_82)))), inference(superposition, [status(thm), theory('equality')], [c_112, c_10])).
% 2.96/1.48  tff(c_134, plain, (![A_16]: (r2_hidden(A_16, k1_tarski(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_131])).
% 2.96/1.48  tff(c_70, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_8'), '#skF_9'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.96/1.48  tff(c_66, plain, (![A_63, B_64]: (k3_tarski(k2_tarski(A_63, B_64))=k2_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.96/1.48  tff(c_14, plain, (![E_12, B_7, C_8]: (r2_hidden(E_12, k1_enumset1(E_12, B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.96/1.48  tff(c_124, plain, (![A_78, B_79]: (r2_hidden(A_78, k2_tarski(A_78, B_79)))), inference(superposition, [status(thm), theory('equality')], [c_112, c_14])).
% 2.96/1.48  tff(c_406, plain, (![C_115, A_116, D_117]: (r2_hidden(C_115, k3_tarski(A_116)) | ~r2_hidden(D_117, A_116) | ~r2_hidden(C_115, D_117))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.96/1.48  tff(c_408, plain, (![C_115, A_78, B_79]: (r2_hidden(C_115, k3_tarski(k2_tarski(A_78, B_79))) | ~r2_hidden(C_115, A_78))), inference(resolution, [status(thm)], [c_124, c_406])).
% 2.96/1.48  tff(c_430, plain, (![C_118, A_119, B_120]: (r2_hidden(C_118, k2_xboole_0(A_119, B_120)) | ~r2_hidden(C_118, A_119))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_408])).
% 2.96/1.48  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.96/1.48  tff(c_818, plain, (![C_178, B_179, A_180, B_181]: (r2_hidden(C_178, B_179) | ~r1_tarski(k2_xboole_0(A_180, B_181), B_179) | ~r2_hidden(C_178, A_180))), inference(resolution, [status(thm)], [c_430, c_2])).
% 2.96/1.48  tff(c_828, plain, (![C_182]: (r2_hidden(C_182, '#skF_9') | ~r2_hidden(C_182, k1_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_70, c_818])).
% 2.96/1.48  tff(c_840, plain, (r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_134, c_828])).
% 2.96/1.48  tff(c_851, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_840])).
% 2.96/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.48  
% 2.96/1.48  Inference rules
% 2.96/1.48  ----------------------
% 2.96/1.48  #Ref     : 0
% 2.96/1.48  #Sup     : 189
% 2.96/1.48  #Fact    : 0
% 2.96/1.48  #Define  : 0
% 2.96/1.48  #Split   : 0
% 2.96/1.48  #Chain   : 0
% 2.96/1.48  #Close   : 0
% 2.96/1.48  
% 2.96/1.48  Ordering : KBO
% 2.96/1.48  
% 2.96/1.48  Simplification rules
% 2.96/1.48  ----------------------
% 2.96/1.48  #Subsume      : 43
% 2.96/1.48  #Demod        : 64
% 2.96/1.48  #Tautology    : 73
% 2.96/1.48  #SimpNegUnit  : 1
% 2.96/1.48  #BackRed      : 0
% 2.96/1.48  
% 2.96/1.48  #Partial instantiations: 0
% 2.96/1.48  #Strategies tried      : 1
% 2.96/1.48  
% 2.96/1.48  Timing (in seconds)
% 2.96/1.48  ----------------------
% 2.96/1.48  Preprocessing        : 0.34
% 2.96/1.48  Parsing              : 0.18
% 2.96/1.48  CNF conversion       : 0.03
% 2.96/1.48  Main loop            : 0.31
% 2.96/1.49  Inferencing          : 0.11
% 2.96/1.49  Reduction            : 0.11
% 2.96/1.49  Demodulation         : 0.08
% 2.96/1.49  BG Simplification    : 0.02
% 2.96/1.49  Subsumption          : 0.05
% 2.96/1.49  Abstraction          : 0.02
% 2.96/1.49  MUC search           : 0.00
% 2.96/1.49  Cooper               : 0.00
% 2.96/1.49  Total                : 0.68
% 2.96/1.49  Index Insertion      : 0.00
% 2.96/1.49  Index Deletion       : 0.00
% 2.96/1.49  Index Matching       : 0.00
% 2.96/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
