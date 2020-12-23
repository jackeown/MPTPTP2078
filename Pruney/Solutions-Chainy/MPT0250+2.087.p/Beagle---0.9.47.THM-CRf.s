%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:43 EST 2020

% Result     : Theorem 5.97s
% Output     : CNFRefutation 6.27s
% Verified   : 
% Statistics : Number of formulae       :   47 (  53 expanded)
%              Number of leaves         :   28 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :   42 (  55 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_67,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_64,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_66,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_4'),'#skF_5'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_62,plain,(
    ! [A_66,B_67] : k3_tarski(k2_tarski(A_66,B_67)) = k2_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_82,plain,(
    ! [A_83,B_84] : k1_enumset1(A_83,A_83,B_84) = k2_tarski(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_20,plain,(
    ! [E_16,A_10,C_12] : r2_hidden(E_16,k1_enumset1(A_10,E_16,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_88,plain,(
    ! [A_83,B_84] : r2_hidden(A_83,k2_tarski(A_83,B_84)) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_20])).

tff(c_60,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(A_64,k3_tarski(B_65))
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_46,plain,(
    ! [A_36] : k2_tarski(A_36,A_36) = k1_tarski(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_100,plain,(
    ! [A_85,B_86] : r2_hidden(A_85,k2_tarski(A_85,B_86)) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_20])).

tff(c_103,plain,(
    ! [A_36] : r2_hidden(A_36,k1_tarski(A_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_100])).

tff(c_192,plain,(
    ! [C_107,B_108,A_109] :
      ( r2_hidden(C_107,B_108)
      | ~ r2_hidden(C_107,A_109)
      | ~ r1_tarski(A_109,B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_214,plain,(
    ! [A_110,B_111] :
      ( r2_hidden(A_110,B_111)
      | ~ r1_tarski(k1_tarski(A_110),B_111) ) ),
    inference(resolution,[status(thm)],[c_103,c_192])).

tff(c_303,plain,(
    ! [A_122,B_123] :
      ( r2_hidden(A_122,k3_tarski(B_123))
      | ~ r2_hidden(k1_tarski(A_122),B_123) ) ),
    inference(resolution,[status(thm)],[c_60,c_214])).

tff(c_315,plain,(
    ! [A_122,B_84] : r2_hidden(A_122,k3_tarski(k2_tarski(k1_tarski(A_122),B_84))) ),
    inference(resolution,[status(thm)],[c_88,c_303])).

tff(c_360,plain,(
    ! [A_127,B_128] : r2_hidden(A_127,k2_xboole_0(k1_tarski(A_127),B_128)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_315])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5850,plain,(
    ! [A_14207,B_14208,B_14209] :
      ( r2_hidden(A_14207,B_14208)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(A_14207),B_14209),B_14208) ) ),
    inference(resolution,[status(thm)],[c_360,c_2])).

tff(c_5879,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_5850])).

tff(c_5889,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_5879])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:16:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.97/2.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.97/2.22  
% 5.97/2.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.97/2.22  %$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 5.97/2.22  
% 5.97/2.22  %Foreground sorts:
% 5.97/2.22  
% 5.97/2.22  
% 5.97/2.22  %Background operators:
% 5.97/2.22  
% 5.97/2.22  
% 5.97/2.22  %Foreground operators:
% 5.97/2.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.97/2.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.97/2.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.97/2.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.97/2.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.97/2.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.97/2.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.97/2.22  tff('#skF_5', type, '#skF_5': $i).
% 5.97/2.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 5.97/2.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.97/2.22  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.97/2.22  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 5.97/2.22  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.97/2.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.97/2.22  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.97/2.22  tff('#skF_4', type, '#skF_4': $i).
% 5.97/2.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.97/2.22  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.97/2.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.97/2.22  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.97/2.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.97/2.22  
% 6.27/2.24  tff(f_90, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 6.27/2.24  tff(f_85, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.27/2.24  tff(f_69, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 6.27/2.24  tff(f_59, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 6.27/2.24  tff(f_83, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 6.27/2.24  tff(f_67, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.27/2.24  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.27/2.24  tff(c_64, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.27/2.24  tff(c_66, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_4'), '#skF_5'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.27/2.24  tff(c_62, plain, (![A_66, B_67]: (k3_tarski(k2_tarski(A_66, B_67))=k2_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.27/2.24  tff(c_82, plain, (![A_83, B_84]: (k1_enumset1(A_83, A_83, B_84)=k2_tarski(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.27/2.24  tff(c_20, plain, (![E_16, A_10, C_12]: (r2_hidden(E_16, k1_enumset1(A_10, E_16, C_12)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.27/2.24  tff(c_88, plain, (![A_83, B_84]: (r2_hidden(A_83, k2_tarski(A_83, B_84)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_20])).
% 6.27/2.24  tff(c_60, plain, (![A_64, B_65]: (r1_tarski(A_64, k3_tarski(B_65)) | ~r2_hidden(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.27/2.24  tff(c_46, plain, (![A_36]: (k2_tarski(A_36, A_36)=k1_tarski(A_36))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.27/2.24  tff(c_100, plain, (![A_85, B_86]: (r2_hidden(A_85, k2_tarski(A_85, B_86)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_20])).
% 6.27/2.24  tff(c_103, plain, (![A_36]: (r2_hidden(A_36, k1_tarski(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_100])).
% 6.27/2.24  tff(c_192, plain, (![C_107, B_108, A_109]: (r2_hidden(C_107, B_108) | ~r2_hidden(C_107, A_109) | ~r1_tarski(A_109, B_108))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.27/2.24  tff(c_214, plain, (![A_110, B_111]: (r2_hidden(A_110, B_111) | ~r1_tarski(k1_tarski(A_110), B_111))), inference(resolution, [status(thm)], [c_103, c_192])).
% 6.27/2.24  tff(c_303, plain, (![A_122, B_123]: (r2_hidden(A_122, k3_tarski(B_123)) | ~r2_hidden(k1_tarski(A_122), B_123))), inference(resolution, [status(thm)], [c_60, c_214])).
% 6.27/2.24  tff(c_315, plain, (![A_122, B_84]: (r2_hidden(A_122, k3_tarski(k2_tarski(k1_tarski(A_122), B_84))))), inference(resolution, [status(thm)], [c_88, c_303])).
% 6.27/2.24  tff(c_360, plain, (![A_127, B_128]: (r2_hidden(A_127, k2_xboole_0(k1_tarski(A_127), B_128)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_315])).
% 6.27/2.24  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.27/2.24  tff(c_5850, plain, (![A_14207, B_14208, B_14209]: (r2_hidden(A_14207, B_14208) | ~r1_tarski(k2_xboole_0(k1_tarski(A_14207), B_14209), B_14208))), inference(resolution, [status(thm)], [c_360, c_2])).
% 6.27/2.24  tff(c_5879, plain, (r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_66, c_5850])).
% 6.27/2.24  tff(c_5889, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_5879])).
% 6.27/2.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.27/2.24  
% 6.27/2.24  Inference rules
% 6.27/2.24  ----------------------
% 6.27/2.24  #Ref     : 0
% 6.27/2.24  #Sup     : 628
% 6.27/2.24  #Fact    : 18
% 6.27/2.24  #Define  : 0
% 6.27/2.24  #Split   : 1
% 6.27/2.24  #Chain   : 0
% 6.27/2.24  #Close   : 0
% 6.27/2.24  
% 6.27/2.24  Ordering : KBO
% 6.27/2.24  
% 6.27/2.24  Simplification rules
% 6.27/2.24  ----------------------
% 6.27/2.24  #Subsume      : 81
% 6.27/2.24  #Demod        : 127
% 6.27/2.24  #Tautology    : 150
% 6.27/2.24  #SimpNegUnit  : 1
% 6.27/2.24  #BackRed      : 0
% 6.27/2.24  
% 6.27/2.24  #Partial instantiations: 4275
% 6.27/2.24  #Strategies tried      : 1
% 6.27/2.24  
% 6.27/2.24  Timing (in seconds)
% 6.27/2.24  ----------------------
% 6.27/2.24  Preprocessing        : 0.35
% 6.27/2.24  Parsing              : 0.18
% 6.27/2.24  CNF conversion       : 0.03
% 6.27/2.24  Main loop            : 1.12
% 6.27/2.24  Inferencing          : 0.62
% 6.27/2.24  Reduction            : 0.27
% 6.27/2.24  Demodulation         : 0.21
% 6.27/2.24  BG Simplification    : 0.05
% 6.27/2.24  Subsumption          : 0.14
% 6.27/2.24  Abstraction          : 0.05
% 6.27/2.24  MUC search           : 0.00
% 6.27/2.24  Cooper               : 0.00
% 6.27/2.24  Total                : 1.51
% 6.27/2.24  Index Insertion      : 0.00
% 6.27/2.24  Index Deletion       : 0.00
% 6.27/2.24  Index Matching       : 0.00
% 6.27/2.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
