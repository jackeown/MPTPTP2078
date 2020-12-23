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
% DateTime   : Thu Dec  3 09:50:43 EST 2020

% Result     : Theorem 5.35s
% Output     : CNFRefutation 5.35s
% Verified   : 
% Statistics : Number of formulae       :   47 (  52 expanded)
%              Number of leaves         :   27 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :   43 (  55 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_54,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_56,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_4'),'#skF_5'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_52,plain,(
    ! [A_49,B_50] : k3_tarski(k2_tarski(A_49,B_50)) = k2_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_98,plain,(
    ! [A_64,B_65] : k1_enumset1(A_64,A_64,B_65) = k2_tarski(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_14,plain,(
    ! [E_15,A_9,C_11] : r2_hidden(E_15,k1_enumset1(A_9,E_15,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_107,plain,(
    ! [A_64,B_65] : r2_hidden(A_64,k2_tarski(A_64,B_65)) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_14])).

tff(c_50,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,k3_tarski(B_48))
      | ~ r2_hidden(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_36,plain,(
    ! [A_19] : k2_tarski(A_19,A_19) = k1_tarski(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    ! [E_15,A_9,B_10] : r2_hidden(E_15,k1_enumset1(A_9,B_10,E_15)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_123,plain,(
    ! [B_68,A_69] : r2_hidden(B_68,k2_tarski(A_69,B_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_12])).

tff(c_126,plain,(
    ! [A_19] : r2_hidden(A_19,k1_tarski(A_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_123])).

tff(c_275,plain,(
    ! [C_86,B_87,A_88] :
      ( r2_hidden(C_86,B_87)
      | ~ r2_hidden(C_86,A_88)
      | ~ r1_tarski(A_88,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_297,plain,(
    ! [A_89,B_90] :
      ( r2_hidden(A_89,B_90)
      | ~ r1_tarski(k1_tarski(A_89),B_90) ) ),
    inference(resolution,[status(thm)],[c_126,c_275])).

tff(c_348,plain,(
    ! [A_100,B_101] :
      ( r2_hidden(A_100,k3_tarski(B_101))
      | ~ r2_hidden(k1_tarski(A_100),B_101) ) ),
    inference(resolution,[status(thm)],[c_50,c_297])).

tff(c_352,plain,(
    ! [A_100,B_65] : r2_hidden(A_100,k3_tarski(k2_tarski(k1_tarski(A_100),B_65))) ),
    inference(resolution,[status(thm)],[c_107,c_348])).

tff(c_411,plain,(
    ! [A_106,B_107] : r2_hidden(A_106,k2_xboole_0(k1_tarski(A_106),B_107)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_352])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6161,plain,(
    ! [A_12092,B_12093,B_12094] :
      ( r2_hidden(A_12092,B_12093)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(A_12092),B_12094),B_12093) ) ),
    inference(resolution,[status(thm)],[c_411,c_2])).

tff(c_6198,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_6161])).

tff(c_6210,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_6198])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:05:47 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.35/2.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.35/2.06  
% 5.35/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.35/2.07  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 5.35/2.07  
% 5.35/2.07  %Foreground sorts:
% 5.35/2.07  
% 5.35/2.07  
% 5.35/2.07  %Background operators:
% 5.35/2.07  
% 5.35/2.07  
% 5.35/2.07  %Foreground operators:
% 5.35/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.35/2.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.35/2.07  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.35/2.07  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.35/2.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.35/2.07  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.35/2.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.35/2.07  tff('#skF_5', type, '#skF_5': $i).
% 5.35/2.07  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 5.35/2.07  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.35/2.07  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.35/2.07  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.35/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.35/2.07  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.35/2.07  tff('#skF_4', type, '#skF_4': $i).
% 5.35/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.35/2.07  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.35/2.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.35/2.07  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.35/2.07  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.35/2.07  
% 5.35/2.08  tff(f_80, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 5.35/2.08  tff(f_75, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.35/2.08  tff(f_59, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 5.35/2.08  tff(f_53, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 5.35/2.08  tff(f_73, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 5.35/2.08  tff(f_57, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 5.35/2.08  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.35/2.08  tff(c_54, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.35/2.08  tff(c_56, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_4'), '#skF_5'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.35/2.08  tff(c_52, plain, (![A_49, B_50]: (k3_tarski(k2_tarski(A_49, B_50))=k2_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.35/2.08  tff(c_98, plain, (![A_64, B_65]: (k1_enumset1(A_64, A_64, B_65)=k2_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.35/2.08  tff(c_14, plain, (![E_15, A_9, C_11]: (r2_hidden(E_15, k1_enumset1(A_9, E_15, C_11)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.35/2.08  tff(c_107, plain, (![A_64, B_65]: (r2_hidden(A_64, k2_tarski(A_64, B_65)))), inference(superposition, [status(thm), theory('equality')], [c_98, c_14])).
% 5.35/2.08  tff(c_50, plain, (![A_47, B_48]: (r1_tarski(A_47, k3_tarski(B_48)) | ~r2_hidden(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.35/2.08  tff(c_36, plain, (![A_19]: (k2_tarski(A_19, A_19)=k1_tarski(A_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.35/2.08  tff(c_12, plain, (![E_15, A_9, B_10]: (r2_hidden(E_15, k1_enumset1(A_9, B_10, E_15)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.35/2.08  tff(c_123, plain, (![B_68, A_69]: (r2_hidden(B_68, k2_tarski(A_69, B_68)))), inference(superposition, [status(thm), theory('equality')], [c_98, c_12])).
% 5.35/2.08  tff(c_126, plain, (![A_19]: (r2_hidden(A_19, k1_tarski(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_123])).
% 5.35/2.08  tff(c_275, plain, (![C_86, B_87, A_88]: (r2_hidden(C_86, B_87) | ~r2_hidden(C_86, A_88) | ~r1_tarski(A_88, B_87))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.35/2.08  tff(c_297, plain, (![A_89, B_90]: (r2_hidden(A_89, B_90) | ~r1_tarski(k1_tarski(A_89), B_90))), inference(resolution, [status(thm)], [c_126, c_275])).
% 5.35/2.08  tff(c_348, plain, (![A_100, B_101]: (r2_hidden(A_100, k3_tarski(B_101)) | ~r2_hidden(k1_tarski(A_100), B_101))), inference(resolution, [status(thm)], [c_50, c_297])).
% 5.35/2.08  tff(c_352, plain, (![A_100, B_65]: (r2_hidden(A_100, k3_tarski(k2_tarski(k1_tarski(A_100), B_65))))), inference(resolution, [status(thm)], [c_107, c_348])).
% 5.35/2.08  tff(c_411, plain, (![A_106, B_107]: (r2_hidden(A_106, k2_xboole_0(k1_tarski(A_106), B_107)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_352])).
% 5.35/2.08  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.35/2.08  tff(c_6161, plain, (![A_12092, B_12093, B_12094]: (r2_hidden(A_12092, B_12093) | ~r1_tarski(k2_xboole_0(k1_tarski(A_12092), B_12094), B_12093))), inference(resolution, [status(thm)], [c_411, c_2])).
% 5.35/2.08  tff(c_6198, plain, (r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_56, c_6161])).
% 5.35/2.08  tff(c_6210, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_6198])).
% 5.35/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.35/2.08  
% 5.35/2.08  Inference rules
% 5.35/2.08  ----------------------
% 5.35/2.08  #Ref     : 0
% 5.35/2.08  #Sup     : 676
% 5.35/2.08  #Fact    : 18
% 5.35/2.08  #Define  : 0
% 5.35/2.08  #Split   : 0
% 5.35/2.08  #Chain   : 0
% 5.35/2.08  #Close   : 0
% 5.35/2.08  
% 5.35/2.08  Ordering : KBO
% 5.35/2.08  
% 5.35/2.08  Simplification rules
% 5.35/2.08  ----------------------
% 5.35/2.08  #Subsume      : 90
% 5.35/2.08  #Demod        : 176
% 5.35/2.08  #Tautology    : 183
% 5.35/2.08  #SimpNegUnit  : 1
% 5.35/2.08  #BackRed      : 0
% 5.35/2.08  
% 5.35/2.08  #Partial instantiations: 3645
% 5.35/2.08  #Strategies tried      : 1
% 5.35/2.08  
% 5.35/2.08  Timing (in seconds)
% 5.35/2.08  ----------------------
% 5.35/2.08  Preprocessing        : 0.31
% 5.35/2.08  Parsing              : 0.16
% 5.35/2.08  CNF conversion       : 0.02
% 5.35/2.08  Main loop            : 1.02
% 5.35/2.08  Inferencing          : 0.58
% 5.35/2.08  Reduction            : 0.25
% 5.35/2.08  Demodulation         : 0.20
% 5.35/2.08  BG Simplification    : 0.04
% 5.35/2.08  Subsumption          : 0.12
% 5.35/2.08  Abstraction          : 0.04
% 5.72/2.08  MUC search           : 0.00
% 5.72/2.08  Cooper               : 0.00
% 5.72/2.08  Total                : 1.36
% 5.72/2.08  Index Insertion      : 0.00
% 5.72/2.08  Index Deletion       : 0.00
% 5.72/2.08  Index Matching       : 0.00
% 5.72/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
