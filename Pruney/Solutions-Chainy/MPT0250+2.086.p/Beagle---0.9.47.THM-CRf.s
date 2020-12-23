%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:43 EST 2020

% Result     : Theorem 5.82s
% Output     : CNFRefutation 5.82s
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

tff(c_299,plain,(
    ! [A_122,B_123] :
      ( r2_hidden(A_122,k3_tarski(B_123))
      | ~ r2_hidden(k1_tarski(A_122),B_123) ) ),
    inference(resolution,[status(thm)],[c_60,c_214])).

tff(c_311,plain,(
    ! [A_122,B_84] : r2_hidden(A_122,k3_tarski(k2_tarski(k1_tarski(A_122),B_84))) ),
    inference(resolution,[status(thm)],[c_88,c_299])).

tff(c_356,plain,(
    ! [A_127,B_128] : r2_hidden(A_127,k2_xboole_0(k1_tarski(A_127),B_128)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_311])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6163,plain,(
    ! [A_14355,B_14356,B_14357] :
      ( r2_hidden(A_14355,B_14356)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(A_14355),B_14357),B_14356) ) ),
    inference(resolution,[status(thm)],[c_356,c_2])).

tff(c_6192,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_6163])).

tff(c_6202,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_6192])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:33:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.82/2.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.82/2.16  
% 5.82/2.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.82/2.16  %$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 5.82/2.16  
% 5.82/2.16  %Foreground sorts:
% 5.82/2.16  
% 5.82/2.16  
% 5.82/2.16  %Background operators:
% 5.82/2.16  
% 5.82/2.16  
% 5.82/2.16  %Foreground operators:
% 5.82/2.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.82/2.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.82/2.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.82/2.16  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.82/2.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.82/2.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.82/2.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.82/2.16  tff('#skF_5', type, '#skF_5': $i).
% 5.82/2.16  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 5.82/2.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.82/2.16  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.82/2.16  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 5.82/2.16  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.82/2.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.82/2.16  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.82/2.16  tff('#skF_4', type, '#skF_4': $i).
% 5.82/2.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.82/2.16  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.82/2.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.82/2.16  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.82/2.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.82/2.16  
% 5.82/2.17  tff(f_90, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 5.82/2.17  tff(f_85, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.82/2.17  tff(f_69, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 5.82/2.17  tff(f_59, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 5.82/2.17  tff(f_83, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 5.82/2.17  tff(f_67, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 5.82/2.17  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.82/2.17  tff(c_64, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.82/2.17  tff(c_66, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_4'), '#skF_5'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.82/2.17  tff(c_62, plain, (![A_66, B_67]: (k3_tarski(k2_tarski(A_66, B_67))=k2_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.82/2.17  tff(c_82, plain, (![A_83, B_84]: (k1_enumset1(A_83, A_83, B_84)=k2_tarski(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.82/2.17  tff(c_20, plain, (![E_16, A_10, C_12]: (r2_hidden(E_16, k1_enumset1(A_10, E_16, C_12)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.82/2.17  tff(c_88, plain, (![A_83, B_84]: (r2_hidden(A_83, k2_tarski(A_83, B_84)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_20])).
% 5.82/2.17  tff(c_60, plain, (![A_64, B_65]: (r1_tarski(A_64, k3_tarski(B_65)) | ~r2_hidden(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.82/2.17  tff(c_46, plain, (![A_36]: (k2_tarski(A_36, A_36)=k1_tarski(A_36))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.82/2.17  tff(c_100, plain, (![A_85, B_86]: (r2_hidden(A_85, k2_tarski(A_85, B_86)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_20])).
% 5.82/2.17  tff(c_103, plain, (![A_36]: (r2_hidden(A_36, k1_tarski(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_100])).
% 5.82/2.17  tff(c_192, plain, (![C_107, B_108, A_109]: (r2_hidden(C_107, B_108) | ~r2_hidden(C_107, A_109) | ~r1_tarski(A_109, B_108))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.82/2.17  tff(c_214, plain, (![A_110, B_111]: (r2_hidden(A_110, B_111) | ~r1_tarski(k1_tarski(A_110), B_111))), inference(resolution, [status(thm)], [c_103, c_192])).
% 5.82/2.17  tff(c_299, plain, (![A_122, B_123]: (r2_hidden(A_122, k3_tarski(B_123)) | ~r2_hidden(k1_tarski(A_122), B_123))), inference(resolution, [status(thm)], [c_60, c_214])).
% 5.82/2.17  tff(c_311, plain, (![A_122, B_84]: (r2_hidden(A_122, k3_tarski(k2_tarski(k1_tarski(A_122), B_84))))), inference(resolution, [status(thm)], [c_88, c_299])).
% 5.82/2.17  tff(c_356, plain, (![A_127, B_128]: (r2_hidden(A_127, k2_xboole_0(k1_tarski(A_127), B_128)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_311])).
% 5.82/2.17  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.82/2.17  tff(c_6163, plain, (![A_14355, B_14356, B_14357]: (r2_hidden(A_14355, B_14356) | ~r1_tarski(k2_xboole_0(k1_tarski(A_14355), B_14357), B_14356))), inference(resolution, [status(thm)], [c_356, c_2])).
% 5.82/2.17  tff(c_6192, plain, (r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_66, c_6163])).
% 5.82/2.17  tff(c_6202, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_6192])).
% 5.82/2.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.82/2.17  
% 5.82/2.17  Inference rules
% 5.82/2.17  ----------------------
% 5.82/2.17  #Ref     : 0
% 5.82/2.17  #Sup     : 661
% 5.82/2.17  #Fact    : 18
% 5.82/2.17  #Define  : 0
% 5.82/2.17  #Split   : 1
% 5.82/2.17  #Chain   : 0
% 5.82/2.17  #Close   : 0
% 5.82/2.17  
% 5.82/2.17  Ordering : KBO
% 5.82/2.17  
% 5.82/2.17  Simplification rules
% 5.82/2.17  ----------------------
% 5.82/2.17  #Subsume      : 90
% 5.82/2.17  #Demod        : 176
% 5.82/2.17  #Tautology    : 173
% 5.82/2.17  #SimpNegUnit  : 1
% 5.82/2.17  #BackRed      : 0
% 5.82/2.17  
% 5.82/2.17  #Partial instantiations: 4320
% 5.82/2.17  #Strategies tried      : 1
% 5.82/2.17  
% 5.82/2.17  Timing (in seconds)
% 5.82/2.17  ----------------------
% 5.82/2.18  Preprocessing        : 0.34
% 5.82/2.18  Parsing              : 0.17
% 5.82/2.18  CNF conversion       : 0.03
% 5.82/2.18  Main loop            : 1.07
% 5.82/2.18  Inferencing          : 0.59
% 5.82/2.18  Reduction            : 0.27
% 5.82/2.18  Demodulation         : 0.21
% 5.82/2.18  BG Simplification    : 0.04
% 5.82/2.18  Subsumption          : 0.13
% 5.82/2.18  Abstraction          : 0.05
% 5.82/2.18  MUC search           : 0.00
% 5.82/2.18  Cooper               : 0.00
% 5.82/2.18  Total                : 1.43
% 5.82/2.18  Index Insertion      : 0.00
% 5.82/2.18  Index Deletion       : 0.00
% 5.82/2.18  Index Matching       : 0.00
% 5.82/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
