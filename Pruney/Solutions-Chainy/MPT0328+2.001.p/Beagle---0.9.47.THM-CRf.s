%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:38 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :   34 (  35 expanded)
%              Number of leaves         :   23 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   25 (  27 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ r2_hidden(A,B)
       => k4_xboole_0(k2_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t141_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(c_52,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_264,plain,(
    ! [A_65,B_66] :
      ( r1_xboole_0(k1_tarski(A_65),B_66)
      | r2_hidden(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( r1_xboole_0(B_9,A_8)
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_797,plain,(
    ! [B_103,A_104] :
      ( r1_xboole_0(B_103,k1_tarski(A_104))
      | r2_hidden(A_104,B_103) ) ),
    inference(resolution,[status(thm)],[c_264,c_10])).

tff(c_30,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,B_23) = A_22
      | ~ r1_xboole_0(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1117,plain,(
    ! [B_129,A_130] :
      ( k4_xboole_0(B_129,k1_tarski(A_130)) = B_129
      | r2_hidden(A_130,B_129) ) ),
    inference(resolution,[status(thm)],[c_797,c_30])).

tff(c_24,plain,(
    ! [A_18,B_19] : k4_xboole_0(k2_xboole_0(A_18,B_19),B_19) = k4_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_50,plain,(
    k4_xboole_0(k2_xboole_0('#skF_3',k1_tarski('#skF_2')),k1_tarski('#skF_2')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_53,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_2')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_50])).

tff(c_1159,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1117,c_53])).

tff(c_1193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1159])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:01:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.39  
% 2.89/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.39  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.89/1.39  
% 2.89/1.39  %Foreground sorts:
% 2.89/1.39  
% 2.89/1.39  
% 2.89/1.39  %Background operators:
% 2.89/1.39  
% 2.89/1.39  
% 2.89/1.39  %Foreground operators:
% 2.89/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.89/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.89/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.89/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.89/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.89/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.89/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.89/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.89/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.89/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.89/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.89/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.39  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.89/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.89/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.89/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.89/1.39  
% 2.89/1.40  tff(f_90, negated_conjecture, ~(![A, B]: (~r2_hidden(A, B) => (k4_xboole_0(k2_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t141_zfmisc_1)).
% 2.89/1.40  tff(f_77, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.89/1.40  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.89/1.40  tff(f_62, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.89/1.40  tff(f_54, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.89/1.40  tff(c_52, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.89/1.40  tff(c_264, plain, (![A_65, B_66]: (r1_xboole_0(k1_tarski(A_65), B_66) | r2_hidden(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.89/1.40  tff(c_10, plain, (![B_9, A_8]: (r1_xboole_0(B_9, A_8) | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.89/1.40  tff(c_797, plain, (![B_103, A_104]: (r1_xboole_0(B_103, k1_tarski(A_104)) | r2_hidden(A_104, B_103))), inference(resolution, [status(thm)], [c_264, c_10])).
% 2.89/1.40  tff(c_30, plain, (![A_22, B_23]: (k4_xboole_0(A_22, B_23)=A_22 | ~r1_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.89/1.40  tff(c_1117, plain, (![B_129, A_130]: (k4_xboole_0(B_129, k1_tarski(A_130))=B_129 | r2_hidden(A_130, B_129))), inference(resolution, [status(thm)], [c_797, c_30])).
% 2.89/1.40  tff(c_24, plain, (![A_18, B_19]: (k4_xboole_0(k2_xboole_0(A_18, B_19), B_19)=k4_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.89/1.40  tff(c_50, plain, (k4_xboole_0(k2_xboole_0('#skF_3', k1_tarski('#skF_2')), k1_tarski('#skF_2'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.89/1.40  tff(c_53, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_2'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_50])).
% 2.89/1.40  tff(c_1159, plain, (r2_hidden('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1117, c_53])).
% 2.89/1.40  tff(c_1193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_1159])).
% 2.89/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.40  
% 2.89/1.40  Inference rules
% 2.89/1.40  ----------------------
% 2.89/1.40  #Ref     : 0
% 2.89/1.40  #Sup     : 268
% 2.89/1.40  #Fact    : 0
% 2.89/1.40  #Define  : 0
% 2.89/1.40  #Split   : 0
% 2.89/1.40  #Chain   : 0
% 2.89/1.40  #Close   : 0
% 2.89/1.40  
% 2.89/1.40  Ordering : KBO
% 2.89/1.40  
% 2.89/1.40  Simplification rules
% 2.89/1.40  ----------------------
% 2.89/1.40  #Subsume      : 10
% 2.89/1.40  #Demod        : 121
% 2.89/1.40  #Tautology    : 179
% 2.89/1.40  #SimpNegUnit  : 2
% 2.89/1.40  #BackRed      : 1
% 2.89/1.40  
% 2.89/1.40  #Partial instantiations: 0
% 2.89/1.40  #Strategies tried      : 1
% 2.89/1.40  
% 2.89/1.40  Timing (in seconds)
% 2.89/1.40  ----------------------
% 2.89/1.40  Preprocessing        : 0.33
% 2.89/1.40  Parsing              : 0.18
% 2.89/1.40  CNF conversion       : 0.02
% 2.89/1.40  Main loop            : 0.33
% 2.89/1.40  Inferencing          : 0.12
% 2.89/1.40  Reduction            : 0.12
% 2.89/1.40  Demodulation         : 0.10
% 2.89/1.40  BG Simplification    : 0.02
% 2.89/1.40  Subsumption          : 0.05
% 2.89/1.40  Abstraction          : 0.02
% 2.89/1.40  MUC search           : 0.00
% 2.89/1.40  Cooper               : 0.00
% 2.89/1.40  Total                : 0.68
% 2.89/1.40  Index Insertion      : 0.00
% 2.89/1.40  Index Deletion       : 0.00
% 2.89/1.40  Index Matching       : 0.00
% 2.89/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
