%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:43 EST 2020

% Result     : Theorem 5.76s
% Output     : CNFRefutation 5.93s
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_67,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_64,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_66,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_4'),'#skF_5'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_62,plain,(
    ! [A_65,B_66] : k3_tarski(k2_tarski(A_65,B_66)) = k2_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_82,plain,(
    ! [A_82,B_83] : k1_enumset1(A_82,A_82,B_83) = k2_tarski(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_20,plain,(
    ! [E_16,A_10,C_12] : r2_hidden(E_16,k1_enumset1(A_10,E_16,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_88,plain,(
    ! [A_82,B_83] : r2_hidden(A_82,k2_tarski(A_82,B_83)) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_20])).

tff(c_60,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(A_63,k3_tarski(B_64))
      | ~ r2_hidden(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_46,plain,(
    ! [A_35] : k2_tarski(A_35,A_35) = k1_tarski(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_100,plain,(
    ! [A_84,B_85] : r2_hidden(A_84,k2_tarski(A_84,B_85)) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_20])).

tff(c_103,plain,(
    ! [A_35] : r2_hidden(A_35,k1_tarski(A_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_100])).

tff(c_308,plain,(
    ! [C_108,B_109,A_110] :
      ( r2_hidden(C_108,B_109)
      | ~ r2_hidden(C_108,A_110)
      | ~ r1_tarski(A_110,B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_330,plain,(
    ! [A_111,B_112] :
      ( r2_hidden(A_111,B_112)
      | ~ r1_tarski(k1_tarski(A_111),B_112) ) ),
    inference(resolution,[status(thm)],[c_103,c_308])).

tff(c_373,plain,(
    ! [A_119,B_120] :
      ( r2_hidden(A_119,k3_tarski(B_120))
      | ~ r2_hidden(k1_tarski(A_119),B_120) ) ),
    inference(resolution,[status(thm)],[c_60,c_330])).

tff(c_385,plain,(
    ! [A_119,B_83] : r2_hidden(A_119,k3_tarski(k2_tarski(k1_tarski(A_119),B_83))) ),
    inference(resolution,[status(thm)],[c_88,c_373])).

tff(c_437,plain,(
    ! [A_127,B_128] : r2_hidden(A_127,k2_xboole_0(k1_tarski(A_127),B_128)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_385])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6146,plain,(
    ! [A_13008,B_13009,B_13010] :
      ( r2_hidden(A_13008,B_13009)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(A_13008),B_13010),B_13009) ) ),
    inference(resolution,[status(thm)],[c_437,c_2])).

tff(c_6175,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_6146])).

tff(c_6185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_6175])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:07:57 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.76/2.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.76/2.10  
% 5.76/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.76/2.10  %$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 5.76/2.10  
% 5.76/2.10  %Foreground sorts:
% 5.76/2.10  
% 5.76/2.10  
% 5.76/2.10  %Background operators:
% 5.76/2.10  
% 5.76/2.10  
% 5.76/2.10  %Foreground operators:
% 5.76/2.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.76/2.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.76/2.10  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.76/2.10  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.76/2.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.76/2.10  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.76/2.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.76/2.10  tff('#skF_5', type, '#skF_5': $i).
% 5.76/2.10  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 5.76/2.10  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.76/2.10  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.76/2.10  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 5.76/2.10  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.76/2.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.76/2.10  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.76/2.10  tff('#skF_4', type, '#skF_4': $i).
% 5.76/2.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.76/2.10  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.76/2.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.76/2.10  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.76/2.10  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.76/2.10  
% 5.93/2.12  tff(f_90, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 5.93/2.12  tff(f_85, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.93/2.12  tff(f_69, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 5.93/2.12  tff(f_59, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 5.93/2.12  tff(f_83, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 5.93/2.12  tff(f_67, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.93/2.12  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.93/2.12  tff(c_64, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.93/2.12  tff(c_66, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_4'), '#skF_5'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.93/2.12  tff(c_62, plain, (![A_65, B_66]: (k3_tarski(k2_tarski(A_65, B_66))=k2_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.93/2.12  tff(c_82, plain, (![A_82, B_83]: (k1_enumset1(A_82, A_82, B_83)=k2_tarski(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.93/2.12  tff(c_20, plain, (![E_16, A_10, C_12]: (r2_hidden(E_16, k1_enumset1(A_10, E_16, C_12)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.93/2.12  tff(c_88, plain, (![A_82, B_83]: (r2_hidden(A_82, k2_tarski(A_82, B_83)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_20])).
% 5.93/2.12  tff(c_60, plain, (![A_63, B_64]: (r1_tarski(A_63, k3_tarski(B_64)) | ~r2_hidden(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.93/2.12  tff(c_46, plain, (![A_35]: (k2_tarski(A_35, A_35)=k1_tarski(A_35))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.93/2.12  tff(c_100, plain, (![A_84, B_85]: (r2_hidden(A_84, k2_tarski(A_84, B_85)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_20])).
% 5.93/2.12  tff(c_103, plain, (![A_35]: (r2_hidden(A_35, k1_tarski(A_35)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_100])).
% 5.93/2.12  tff(c_308, plain, (![C_108, B_109, A_110]: (r2_hidden(C_108, B_109) | ~r2_hidden(C_108, A_110) | ~r1_tarski(A_110, B_109))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.93/2.12  tff(c_330, plain, (![A_111, B_112]: (r2_hidden(A_111, B_112) | ~r1_tarski(k1_tarski(A_111), B_112))), inference(resolution, [status(thm)], [c_103, c_308])).
% 5.93/2.12  tff(c_373, plain, (![A_119, B_120]: (r2_hidden(A_119, k3_tarski(B_120)) | ~r2_hidden(k1_tarski(A_119), B_120))), inference(resolution, [status(thm)], [c_60, c_330])).
% 5.93/2.12  tff(c_385, plain, (![A_119, B_83]: (r2_hidden(A_119, k3_tarski(k2_tarski(k1_tarski(A_119), B_83))))), inference(resolution, [status(thm)], [c_88, c_373])).
% 5.93/2.12  tff(c_437, plain, (![A_127, B_128]: (r2_hidden(A_127, k2_xboole_0(k1_tarski(A_127), B_128)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_385])).
% 5.93/2.12  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.93/2.12  tff(c_6146, plain, (![A_13008, B_13009, B_13010]: (r2_hidden(A_13008, B_13009) | ~r1_tarski(k2_xboole_0(k1_tarski(A_13008), B_13010), B_13009))), inference(resolution, [status(thm)], [c_437, c_2])).
% 5.93/2.12  tff(c_6175, plain, (r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_66, c_6146])).
% 5.93/2.12  tff(c_6185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_6175])).
% 5.93/2.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.93/2.12  
% 5.93/2.12  Inference rules
% 5.93/2.12  ----------------------
% 5.93/2.12  #Ref     : 0
% 5.93/2.12  #Sup     : 672
% 5.93/2.12  #Fact    : 18
% 5.93/2.12  #Define  : 0
% 5.93/2.12  #Split   : 1
% 5.93/2.12  #Chain   : 0
% 5.93/2.12  #Close   : 0
% 5.93/2.12  
% 5.93/2.12  Ordering : KBO
% 5.93/2.12  
% 5.93/2.12  Simplification rules
% 5.93/2.12  ----------------------
% 5.93/2.12  #Subsume      : 89
% 5.93/2.12  #Demod        : 183
% 5.93/2.12  #Tautology    : 188
% 5.93/2.12  #SimpNegUnit  : 1
% 5.93/2.12  #BackRed      : 0
% 5.93/2.12  
% 5.93/2.12  #Partial instantiations: 3915
% 5.93/2.12  #Strategies tried      : 1
% 5.93/2.12  
% 5.93/2.12  Timing (in seconds)
% 5.93/2.12  ----------------------
% 5.93/2.12  Preprocessing        : 0.32
% 5.93/2.12  Parsing              : 0.16
% 5.93/2.12  CNF conversion       : 0.03
% 5.93/2.12  Main loop            : 1.04
% 5.93/2.12  Inferencing          : 0.55
% 5.93/2.12  Reduction            : 0.27
% 5.93/2.12  Demodulation         : 0.22
% 5.93/2.12  BG Simplification    : 0.04
% 5.93/2.12  Subsumption          : 0.13
% 5.93/2.12  Abstraction          : 0.05
% 5.93/2.12  MUC search           : 0.00
% 5.93/2.12  Cooper               : 0.00
% 5.93/2.12  Total                : 1.39
% 5.93/2.12  Index Insertion      : 0.00
% 5.93/2.12  Index Deletion       : 0.00
% 5.93/2.12  Index Matching       : 0.00
% 5.93/2.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
