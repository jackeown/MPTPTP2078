%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:39 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   28 (  29 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   25 (  27 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ r2_hidden(A,B)
       => k4_xboole_0(k2_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t141_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(c_18,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_39,plain,(
    ! [A_19,B_20] :
      ( r1_xboole_0(k1_tarski(A_19),B_20)
      | r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_55,plain,(
    ! [B_23,A_24] :
      ( r1_xboole_0(B_23,k1_tarski(A_24))
      | r2_hidden(A_24,B_23) ) ),
    inference(resolution,[status(thm)],[c_39,c_2])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = A_5
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_103,plain,(
    ! [B_31,A_32] :
      ( k4_xboole_0(B_31,k1_tarski(A_32)) = B_31
      | r2_hidden(A_32,B_31) ) ),
    inference(resolution,[status(thm)],[c_55,c_6])).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(k2_xboole_0(A_3,B_4),B_4) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    k4_xboole_0(k2_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_19,plain,(
    k4_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_16])).

tff(c_116,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_19])).

tff(c_128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_116])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:11:40 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.20  
% 1.71/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.20  %$ r2_hidden > r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.71/1.20  
% 1.71/1.20  %Foreground sorts:
% 1.71/1.20  
% 1.71/1.20  
% 1.71/1.20  %Background operators:
% 1.71/1.20  
% 1.71/1.20  
% 1.71/1.20  %Foreground operators:
% 1.71/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.71/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.71/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.71/1.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.71/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.71/1.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.71/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.71/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.71/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.71/1.20  
% 1.71/1.21  tff(f_50, negated_conjecture, ~(![A, B]: (~r2_hidden(A, B) => (k4_xboole_0(k2_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t141_zfmisc_1)).
% 1.71/1.21  tff(f_44, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 1.71/1.21  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.71/1.21  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.71/1.21  tff(f_31, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 1.71/1.21  tff(c_18, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.71/1.21  tff(c_39, plain, (![A_19, B_20]: (r1_xboole_0(k1_tarski(A_19), B_20) | r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.71/1.21  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.71/1.21  tff(c_55, plain, (![B_23, A_24]: (r1_xboole_0(B_23, k1_tarski(A_24)) | r2_hidden(A_24, B_23))), inference(resolution, [status(thm)], [c_39, c_2])).
% 1.71/1.21  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=A_5 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.71/1.21  tff(c_103, plain, (![B_31, A_32]: (k4_xboole_0(B_31, k1_tarski(A_32))=B_31 | r2_hidden(A_32, B_31))), inference(resolution, [status(thm)], [c_55, c_6])).
% 1.71/1.21  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(k2_xboole_0(A_3, B_4), B_4)=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.71/1.21  tff(c_16, plain, (k4_xboole_0(k2_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.71/1.21  tff(c_19, plain, (k4_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4, c_16])).
% 1.71/1.21  tff(c_116, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_103, c_19])).
% 1.71/1.21  tff(c_128, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_116])).
% 1.71/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.21  
% 1.71/1.21  Inference rules
% 1.71/1.21  ----------------------
% 1.71/1.21  #Ref     : 0
% 1.71/1.21  #Sup     : 26
% 1.71/1.21  #Fact    : 0
% 1.71/1.21  #Define  : 0
% 1.71/1.21  #Split   : 0
% 1.71/1.21  #Chain   : 0
% 1.71/1.21  #Close   : 0
% 1.71/1.21  
% 1.71/1.21  Ordering : KBO
% 1.71/1.21  
% 1.71/1.21  Simplification rules
% 1.71/1.21  ----------------------
% 1.71/1.21  #Subsume      : 2
% 1.71/1.21  #Demod        : 2
% 1.71/1.21  #Tautology    : 10
% 1.71/1.21  #SimpNegUnit  : 1
% 1.71/1.21  #BackRed      : 0
% 1.71/1.21  
% 1.71/1.21  #Partial instantiations: 0
% 1.71/1.21  #Strategies tried      : 1
% 1.71/1.21  
% 1.71/1.21  Timing (in seconds)
% 1.71/1.21  ----------------------
% 1.71/1.21  Preprocessing        : 0.29
% 1.71/1.21  Parsing              : 0.16
% 1.71/1.21  CNF conversion       : 0.02
% 1.71/1.21  Main loop            : 0.11
% 1.71/1.21  Inferencing          : 0.05
% 1.71/1.21  Reduction            : 0.03
% 1.71/1.21  Demodulation         : 0.02
% 1.71/1.21  BG Simplification    : 0.01
% 1.71/1.21  Subsumption          : 0.02
% 1.71/1.21  Abstraction          : 0.01
% 1.71/1.21  MUC search           : 0.00
% 1.71/1.21  Cooper               : 0.00
% 1.71/1.21  Total                : 0.43
% 1.71/1.21  Index Insertion      : 0.00
% 1.71/1.21  Index Deletion       : 0.00
% 1.71/1.21  Index Matching       : 0.00
% 1.71/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
